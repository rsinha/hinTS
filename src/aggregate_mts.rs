use std::ops::{AddAssign};
use std::time::{Instant};
use std::borrow::Borrow;

use ark_ec::{*};
use ark_ff::{*};
use ark_bls12_377::{*, constraints::*};
use ark_bw6_761::{*};
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_r1cs_std::pairing::PairingVar;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{*, rand::Rng};
use ark_relations::r1cs::*;
use ark_groth16::{Groth16, Proof};
use ark_snark::SNARK;

use ark_ed_on_bw6_761::{constraints::EdwardsVar, EdwardsProjective};

use ark_crypto_primitives::crh::{
    injective_map::{PedersenCRHCompressor, TECompressor},
    injective_map::constraints::{PedersenCRHCompressorGadget, TECompressorGadget,},
    pedersen, TwoToOneCRH, CRH,
    constraints::{CRHGadget, TwoToOneCRHGadget},
};

use ark_crypto_primitives::merkle_tree::{self, MerkleTree, Path};
use ark_crypto_primitives::merkle_tree::constraints::PathVar;

pub type ConstraintF = ark_bw6_761::Fr;
const NUM_UNIVERSES: usize = 4095;


#[test]
fn end_to_end_test() {
    end_to_end();
}


fn end_to_end() {
    const TOTAL_SIGNED_WEIGHT: u64 = 6;
    const NUM_SIGS: usize = 4;

    let circuit_defining_cs = AggregateMTS::<NUM_SIGS>::new();
    let mut rng = ark_std::test_rng();
    
    let now = Instant::now();
    let (pk, vk) = Groth16::<BW6_761>::
        circuit_specific_setup(circuit_defining_cs, &mut rng)
        .unwrap();
    let duration = now.elapsed();
    println!("setup time: {}.{}", duration.as_secs(), duration.as_millis());
    
    let mut vk_serialized = vec![];
    vk.serialize(&mut vk_serialized).unwrap();
    println!("vk size: {}", vk_serialized.len());

    let circuit_to_verify_against = AggregateMTS::<NUM_SIGS>::new();
    let public_input = [
        circuit_to_verify_against.merkle_root,
        ark_bw6_761::Fr::new(BigInteger384::try_from(TOTAL_SIGNED_WEIGHT as u64).unwrap()),
    ];
    
    let now = Instant::now();
    let proof = Groth16::prove(
        &pk, circuit_to_verify_against, &mut rng).unwrap();
    let duration = now.elapsed();
    println!("prover time: {}.{}", duration.as_secs(), duration.as_millis());

    let mut proof_serialized = vec![];
    proof.serialize(&mut proof_serialized).unwrap();
    println!("proof size: {}", proof_serialized.len());
    let parsed_proof = Proof::deserialize(
        &proof_serialized[..]).unwrap();
    
    
    let now = Instant::now();
    let valid_proof = Groth16::verify(
        &vk, &public_input, &parsed_proof).unwrap();
    let duration = now.elapsed();
    println!("verifier time: {}.{}", duration.as_secs(), duration.as_millis());

    assert!(valid_proof);
}


/// Information about the account, such as the balance and the associated public key.
#[derive(Hash, Eq, PartialEq, Copy, Clone)]
pub struct AggMTSUniverse {
    /// verification key part 1
    pub vk_0: ark_bls12_377::G1Projective,
    /// verification key part 2
    pub vk_1: ark_bls12_377::G2Projective,
    /// the weight associated with this universe
    pub weight: ark_bls12_377::Fq,
}

impl AggMTSUniverse {
    /// Convert the account information to bytes.
    pub fn to_bytes_le(&self) -> Vec<u8> {
        //ark_ff::to_bytes![self.vk_0, self.vk_1, self.weight.to_bytes_le()].unwrap()
        let vks = ark_ff::to_bytes![
            self.vk_0.into_affine(), 
            self.vk_1.into_affine(), 
            self.weight]
            .unwrap();
        [&vks[..]].concat()
    }
}

#[derive(Clone)]
pub struct AggMTSUniverseVar {
    /// verification key part 1
    pub vk_0: G1Var,
    /// verification key part 2
    pub vk_1: G2Var,
    //weight of universe (number of parties)
    pub weight: FqVar
}

impl AggMTSUniverseVar {
    /// Convert the account information to bytes.
    //#[tracing::instrument(target = "r1cs", skip(self))]
    pub fn to_bytes_le(&self) -> Vec<UInt8<ConstraintF>> {
        let vk_0: Vec<UInt8<ConstraintF>> = self.vk_0
            .to_bytes()
            .unwrap()
            .into_iter()
            .collect();
        let vk_1: Vec<UInt8<ConstraintF>> = self.vk_1
            .to_bytes()
            .unwrap()
            .into_iter()
            .collect();
        let w: Vec<UInt8<ConstraintF>> = self.weight
            .to_bytes()
            .unwrap()
            .into_iter()
            .collect();
        [&vk_0[..], &vk_1[..], &w[..]].concat()
    }
}

/// The parameters that are used in transaction creation and validation.
#[derive(Clone)]
pub struct AggMTSMerkleParameters {
    pub leaf_crh_params: <AggMTSTwoToOneHash as CRH>::Parameters,
    pub two_to_one_crh_params: <AggMTSTwoToOneHash as TwoToOneCRH>::Parameters,
}

impl AggMTSMerkleParameters {
    pub fn sample<R: Rng>(rng: &mut R) -> Self {
        let leaf_crh_params = 
            <AggMTSLeafHash as CRH>::setup(rng).unwrap();
        let two_to_one_crh_params = 
            <AggMTSTwoToOneHash as TwoToOneCRH>::setup(rng).unwrap();
        Self {
            leaf_crh_params,
            two_to_one_crh_params,
        }
    }
}

pub type AggMTSTwoToOneHash = PedersenCRHCompressor<EdwardsProjective, TECompressor, AggMTSTwoToOneWindow>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AggMTSTwoToOneWindow;

// `WINDOW_SIZE * NUM_WINDOWS` = 2 * 256 bits = enough for hashing two outputs.
impl pedersen::Window for AggMTSTwoToOneWindow {
    const WINDOW_SIZE: usize = 880;
    const NUM_WINDOWS: usize = 4;
}

pub type AggMTSLeafHash = PedersenCRHCompressor<EdwardsProjective, TECompressor, AggMTSLeafWindow>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AggMTSLeafWindow;

// `WINDOW_SIZE * NUM_WINDOWS` = 2 * 256 bits = enough for hashing two outputs.
impl pedersen::Window for AggMTSLeafWindow {
    const WINDOW_SIZE: usize = 880;
    const NUM_WINDOWS: usize = 4;
}

#[derive(Clone)]
pub struct AggMTSMerkleConfig;
impl merkle_tree::Config for AggMTSMerkleConfig {
    type LeafHash = AggMTSLeafHash;
    type TwoToOneHash = AggMTSTwoToOneHash;
}

/// A Merkle tree containing account information.
pub type UniMerkleTree = MerkleTree<AggMTSMerkleConfig>;
/// The root of the account Merkle tree.
pub type UniRoot = <AggMTSTwoToOneHash as TwoToOneCRH>::Output;
/// A membership proof for a given account.
pub type UniPath = Path<AggMTSMerkleConfig>;

#[derive(Clone)]
pub struct AggMTSState {
    /// A merkle tree mapping where the i-th leaf corresponds to the i-th account's
    /// information (= balance and public key).
    pub universe_merkle_tree: UniMerkleTree,
    pub num_universes: usize,
}

impl AggMTSState {
    /// Create an empty ledger that supports `num_accounts` accounts.
    pub fn new(num_universes: usize, parameters: &AggMTSMerkleParameters) -> Self {
        let height = ark_std::log2(num_universes) + 1;
        let universe_merkle_tree = MerkleTree::blank(
            &parameters.leaf_crh_params,
            &parameters.two_to_one_crh_params,
            height as usize,
        )
        .unwrap();
        Self {
            universe_merkle_tree: universe_merkle_tree,
            num_universes: 0
        }
    }

    /// Return the root of the account Merkle tree.
    pub fn root(&self) -> UniRoot {
        self.universe_merkle_tree.root()
    }

    /// Create a new account with public key `pub_key`. Returns a fresh account identifier
    /// if there is space for a new account, and returns `None` otherwise.
    /// The initial balance of the new account is 0.
    pub fn register_universe(&mut self, 
        vk_0: ark_bls12_377::G1Projective, 
        vk_1: ark_bls12_377::G2Projective,
        weight: ark_bls12_377::Fq) {
        // Construct account information for the new account.
        let uni_info = AggMTSUniverse { vk_0, vk_1, weight };
        // Insert information into the relevant accounts.
        self.universe_merkle_tree
            .update(self.num_universes, &uni_info.to_bytes_le())
            .expect("should exist");
        self.num_universes += 1;
    }

}



pub type AggMTSTwoToOneHashGadget = PedersenCRHCompressorGadget<
    EdwardsProjective,
    TECompressor,
    AggMTSTwoToOneWindow,
    EdwardsVar,
    TECompressorGadget,
>;

pub type AggMTSLeafHashGadget = PedersenCRHCompressorGadget<
    EdwardsProjective,
    TECompressor,
    AggMTSLeafWindow,
    EdwardsVar,
    TECompressorGadget,
>;

pub type AggMTSMerkleRootVar =
    <AggMTSTwoToOneHashGadget as TwoToOneCRHGadget<AggMTSTwoToOneHash, ConstraintF>>::OutputVar;
pub type AggMTSMerklePathVar = PathVar<AggMTSMerkleConfig, AggMTSLeafHashGadget, AggMTSTwoToOneHashGadget, ConstraintF>;
pub type AggMTSLeafHashParamsVar = <AggMTSLeafHashGadget as CRHGadget<AggMTSLeafHash, ConstraintF>>::ParametersVar;
pub type AggMTSTwoToOneHashParamsVar =
    <AggMTSTwoToOneHashGadget as TwoToOneCRHGadget<AggMTSTwoToOneHash, ConstraintF>>::ParametersVar;

/// The parameters that are used in transaction creation and validation.
pub struct AggMTSParametersVar {
    pub leaf_crh_params: AggMTSLeafHashParamsVar,
    pub two_to_one_crh_params: AggMTSTwoToOneHashParamsVar,
}

impl AllocVar<AggMTSMerkleParameters, ConstraintF> for AggMTSParametersVar {
    //#[tracing::instrument(target = "r1cs", skip(cs, f, _mode))]
    fn new_variable<T: Borrow<AggMTSMerkleParameters>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T>,
        _mode: AllocationMode,
    ) -> Result<Self> {
        let cs = cs.into();
        f().and_then(|params| {
            let params: &AggMTSMerkleParameters = params.borrow();
            let leaf_crh_params =
                AggMTSLeafHashParamsVar::new_constant(cs.clone(), &params.leaf_crh_params)?;
            let two_to_one_crh_params =
                AggMTSTwoToOneHashParamsVar::new_constant(cs.clone(), &params.two_to_one_crh_params)?;
            Ok(Self {
                leaf_crh_params,
                two_to_one_crh_params,
            })
        })
    }
}

pub struct AggregateMTS<const NUM_SIGS: usize> {
    pub pp: AggMTSMerkleParameters,
    pub vk_0s: Vec<ark_bls12_377::G1Projective>,
    pub vk_1s: Vec<ark_bls12_377::G2Projective>,
    pub weights: Vec<ark_bls12_377::Fq>,
    pub h_of_ms: Vec<ark_bls12_377::G2Projective>,
    pub sigma_primes: Vec<ark_bls12_377::G2Projective>,
    pub sigma_0_primes: Vec<ark_bls12_377::G1Projective>,
    pub sigma_1_primes: Vec<ark_bls12_377::G1Projective>,
    pub merkle_paths: Vec<Path<AggMTSMerkleConfig>>,
    pub merkle_path_params: Path<AggMTSMerkleConfig>,
    pub merkle_root: UniRoot,
    pub total_signing_weight: u64
}

impl<const NUM_SIGS: usize> AggregateMTS<NUM_SIGS> {
    pub fn new() -> Self {

        let mut rng = ark_std::test_rng();

        let mut vk_0s = Vec::with_capacity(NUM_SIGS);
        let mut vk_1s = Vec::with_capacity(NUM_SIGS);
        let mut weights = Vec::with_capacity(NUM_SIGS);
        let mut sigma_primes = Vec::with_capacity(NUM_SIGS);
        let mut sigma_0_primes = Vec::with_capacity(NUM_SIGS);
        let mut sigma_1_primes = Vec::with_capacity(NUM_SIGS);
        let mut h_of_ms = Vec::with_capacity(NUM_SIGS);

        let mut merkle_paths = Vec::with_capacity(NUM_SIGS);

        let pp = AggMTSMerkleParameters::sample(&mut rng);
        let mut state = AggMTSState::new(NUM_UNIVERSES, &pp);

        let g1_generator: ark_bls12_377::G1Projective = 
                ark_bls12_377::G1Affine::prime_subgroup_generator().into();
        let g2_generator: ark_bls12_377::G2Projective = 
            ark_bls12_377::G2Affine::prime_subgroup_generator().into();
        
        let h_of_m = ark_bls12_377::G2Projective::rand(&mut rng);

        let zero_weight = ark_bls12_377::Fq::new(BigInteger384::try_from(0 as u64).unwrap());
        state.register_universe(g1_generator, g2_generator, zero_weight);

        let mut total_signing_weight: u64 = 0;
        //sample universe parameters and a satisfying signature
        //here we are also registering universes for which we have sigs
        for _i in 0..NUM_SIGS {
            let weight = ark_bls12_377::Fq::new(BigInteger384::try_from(_i as u64).unwrap());
            total_signing_weight += _i as u64;
            //Fp384::new(BigInteger384::try_from(weight_u64).unwrap());;

            let k = ark_bls12_377::Fr::rand(&mut rng);
            let x = ark_bls12_377::Fr::rand(&mut rng);
            let y = ark_bls12_377::Fr::rand(&mut rng);
            let s = x + y;

            let vk_0 = g1_generator.mul(&s.into_repr());
            let vk_1 = g2_generator.mul(&k.into_repr());

            let sigma_0_prime = g1_generator.mul(&x.into_repr());
            let sigma_1_prime = sigma_0_prime.mul(&k.into_repr());
            let sigma_prime = h_of_m.mul(&y.into_repr());

            state.register_universe(vk_0, vk_1, weight);

            vk_0s.push(vk_0);
            vk_1s.push(vk_1);
            weights.push(weight);
            h_of_ms.push(h_of_m);
            sigma_0_primes.push(sigma_0_prime);
            sigma_1_primes.push(sigma_1_prime);
            sigma_primes.push(sigma_prime);
        }

        //register a bunch of other universes
        for _i in NUM_SIGS..NUM_UNIVERSES {
            let weight = ark_bls12_377::Fq::new(BigInteger384::try_from(2 as u64).unwrap());

            let k = ark_bls12_377::Fr::rand(&mut rng);
            let s = ark_bls12_377::Fr::rand(&mut rng);

            let vk_0 = g1_generator.mul(&s.into_repr());
            let vk_1 = g2_generator.mul(&k.into_repr());

            state.register_universe(vk_0, vk_1, weight);
        }

        let merkle_path_params = state.universe_merkle_tree.generate_proof(0).unwrap();
        //compute merkle paths only when all universes are registered, else the paths will be bogus
        for i in 0..NUM_SIGS {
            let universe_id: usize = i + 1;
            let path = state.universe_merkle_tree.generate_proof(universe_id).unwrap();
            merkle_paths.push(path);
        }
        let merkle_root = state.root();

        Self { 
            pp, 
            vk_0s, 
            vk_1s, 
            weights, 
            h_of_ms, 
            sigma_primes, 
            sigma_0_primes, 
            sigma_1_primes, 
            merkle_paths,
            merkle_path_params,
            merkle_root,
            total_signing_weight
        }
    }
}


impl<const NUM_SIGS: usize> ConstraintSynthesizer<ConstraintF> for AggregateMTS<NUM_SIGS> {
    //#[tracing::instrument(target = "r1cs", skip(self, cs))]
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<()> {

        let g1_generator: ark_bls12_377::G1Projective = 
            ark_bls12_377::G1Affine::prime_subgroup_generator().into();
        let g2_generator: ark_bls12_377::G2Projective = 
            ark_bls12_377::G2Affine::prime_subgroup_generator().into();

        let ledger_params = AggMTSParametersVar::new_constant(
            ark_relations::ns!(cs, "ledger_params"),
            &self.pp,
        )?;

        let zero_weight = ark_bls12_377::Fq::new(BigInteger384::try_from(0 as u64).unwrap());
        
        //merkle root is a public variable shared with the verifier
        let merkle_root_var = 
            AggMTSMerkleRootVar::new_input(ark_relations::ns!(cs, "universe_root"), || Ok(self.merkle_root))?;

        let g1_generator_const = G1Var::new_witness(
            ark_relations::ns!(cs, "g1_generator"), || Ok(g1_generator))?;
        let g2_generator_const = G2Var::new_witness(
            ark_relations::ns!(cs, "g2_generator"), || Ok(g2_generator))?;

        let zero_weight_var = FqVar::new_witness(cs.clone(), || Ok(zero_weight))?;
        let universe_params = AggMTSUniverseVar { 
            vk_0: g1_generator_const.clone(), 
            vk_1: g2_generator_const.clone(), 
            weight: zero_weight_var 
        };

        let merkle_path = 
            AggMTSMerklePathVar::new_witness(ark_relations::ns!(cs, "universe_existence_path"), || Ok(self.merkle_path_params) )?;

        let valid = merkle_path.verify_membership(
            &ledger_params.leaf_crh_params,
            &ledger_params.two_to_one_crh_params,
            &merkle_root_var,
            &universe_params.to_bytes_le().as_slice(),
        )?;
        valid.enforce_equal(&Boolean::TRUE)?;


        let threshold_weight = Fp384::new(BigInteger384::try_from(self.total_signing_weight).unwrap());
        let threshold_weight_fpvar = FpVar::<ark_bls12_377::Fq>::new_input(
            cs.clone(), || Ok(threshold_weight))?;
        
        
        let mut aggregate_weight_fpvar = FqVar::new_witness(cs.clone(), || Ok(zero_weight))?;

        for i in 0..NUM_SIGS {
            let merkle_path = self.merkle_paths.get(i).unwrap().clone();

            let vk_0: ark_bls12_377::G1Projective = self.vk_0s.get(i).unwrap().clone();
            let vk_1: ark_bls12_377::G2Projective = self.vk_1s.get(i).unwrap().clone();
            let weight: ark_bls12_377::Fq = self.weights.get(i).unwrap().clone();

            let h_of_m: ark_bls12_377::G2Projective = self.h_of_ms.get(i).unwrap().clone();
            let sigma_0_prime: ark_bls12_377::G1Projective = self.sigma_0_primes.get(i).unwrap().clone();
            let sigma_1_prime: ark_bls12_377::G1Projective = self.sigma_1_primes.get(i).unwrap().clone();
            let sigma_prime: ark_bls12_377::G2Projective = self.sigma_primes.get(i).unwrap().clone();

            let weight_var: FqVar = FqVar::new_witness(ark_relations::ns!(cs, "weight"), || Ok(weight))?;

            let vk_0_var = G1Var::new_witness(
                ark_relations::ns!(cs, "vk_0"), || Ok(vk_0))?;
            let sigma_0_prime_var = G1Var::new_witness(
                ark_relations::ns!(cs, "sigma_0_prime"), || Ok(sigma_0_prime))?;
            let lhs_var = &vk_0_var - &sigma_0_prime_var;
            // let lhs_var = G1Var::new_witness(
            //     ark_relations::ns!(cs, "vk_0 / sigma_0_prime"), || Ok(vk_0 - sigma_0_prime))?;

            let h_of_m_var = G2Var::new_witness(
                ark_relations::ns!(cs, "h_of_m"), || Ok(h_of_m))?;
            
            let sigma_prime_var = G2Var::new_witness(
                ark_relations::ns!(cs, "sigma_prime"), || Ok(sigma_prime))?;
            
            let v1 = constraints::PairingVar::prepare_g1(&lhs_var)?;
            let v2 = constraints::PairingVar::prepare_g2(&h_of_m_var)?;

            let v3 = constraints::PairingVar::prepare_g1(&g1_generator_const)?;
            let v4 = constraints::PairingVar::prepare_g2(&sigma_prime_var)?;

            let p1 = constraints::PairingVar::pairing(v1, v2)?;
            let p2 = constraints::PairingVar::pairing(v3, v4)?;

            p1.enforce_equal(&p2)?;

            let vk_1_var = G2Var::new_witness(
                ark_relations::ns!(cs, "vk_1"), || Ok(vk_1))?;
            let sigma_0_prime_var = G1Var::new_witness(
                ark_relations::ns!(cs, "sigma_0_prime"), || Ok(sigma_0_prime))?;
            let sigma_1_prime_var = G1Var::new_witness(
                ark_relations::ns!(cs, "sigma_1_prime"), || Ok(sigma_1_prime))?;

            let v1 = constraints::PairingVar::prepare_g1(&sigma_1_prime_var)?;
            let v2 = constraints::PairingVar::prepare_g2(&g2_generator_const)?;

            let v3 = constraints::PairingVar::prepare_g1(&sigma_0_prime_var)?;
            let v4 = constraints::PairingVar::prepare_g2(&vk_1_var)?;

            let p1 = constraints::PairingVar::pairing(v1, v2)?;
            let p2 = constraints::PairingVar::pairing(v3, v4)?;

            p1.enforce_equal(&p2)?;

            let universe_info = AggMTSUniverseVar {
                vk_0: vk_0_var, 
                vk_1: vk_1_var, 
                weight: weight_var.clone()
            };

            let merkle_path = 
                AggMTSMerklePathVar::new_witness(ark_relations::ns!(cs, "universe_existence_path"), || Ok(merkle_path) )?;

            let valid = merkle_path.verify_membership(
                &ledger_params.leaf_crh_params,
                &ledger_params.two_to_one_crh_params,
                &merkle_root_var,
                &universe_info.to_bytes_le().as_slice(),
            )?;
            valid.enforce_equal(&Boolean::TRUE)?;

            aggregate_weight_fpvar.add_assign(weight_var);
        }

        threshold_weight_fpvar.enforce_equal(&aggregate_weight_fpvar)?;

        println!("circuit size: {}", cs.num_constraints());

        Ok(())
    }
}
