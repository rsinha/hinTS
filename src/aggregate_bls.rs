use std::ops::{AddAssign, Mul};
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
use ark_ff::BigInteger;

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
const NUM_PARTIES: usize = 63;
const NUM_SIGS: usize = 32;

#[test]
fn end_to_end_test() {
    end_to_end_groth();
}


fn end_to_end_groth() {
    const TOTAL_SIGNED_WEIGHT: u64 = NUM_SIGS as u64;

    let circuit_defining_cs = AggregateBLS::<NUM_PARTIES>::new();
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


    let circuit_to_verify_against = AggregateBLS::<NUM_PARTIES>::new();
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
pub struct AggBLSParty {
    /// verification key
    pub pk: ark_bls12_377::G1Projective,
    /// the weight associated with this public key
    pub weight: ark_bls12_377::Fq,
}

impl AggBLSParty {
    /// Convert the account information to bytes.
    pub fn to_bytes_le(&self) -> Vec<u8> {
        let vks = ark_ff::to_bytes![
            self.pk.into_affine(), 
            self.weight]
            .unwrap();
        [&vks[..]].concat()
    }
}

#[derive(Clone)]
pub struct AggBLSPartyVar {
    /// public key
    pub pk: G1Var,
    //weight of universe (number of parties)
    pub weight: FqVar
}

impl AggBLSPartyVar {
    /// Convert the account information to bytes.
    //#[tracing::instrument(target = "r1cs", skip(self))]
    pub fn to_bytes_le(&self) -> Vec<UInt8<ConstraintF>> {
        let pk: Vec<UInt8<ConstraintF>> = self.pk
            .to_bytes()
            .unwrap()
            .into_iter()
            .collect();
        let w: Vec<UInt8<ConstraintF>> = self.weight
            .to_bytes()
            .unwrap()
            .into_iter()
            .collect();
        [&pk[..], &w[..]].concat()
    }
}

/// The parameters that are used in transaction creation and validation.
#[derive(Clone)]
pub struct AggBLSMerkleParameters {
    pub leaf_crh_params: <AggBLSTwoToOneHash as CRH>::Parameters,
    pub two_to_one_crh_params: <AggBLSTwoToOneHash as TwoToOneCRH>::Parameters,
}

impl AggBLSMerkleParameters {
    pub fn sample<R: Rng>(rng: &mut R) -> Self {
        let leaf_crh_params = 
            <AggBLSLeafHash as CRH>::setup(rng).unwrap();
        let two_to_one_crh_params = 
            <AggBLSTwoToOneHash as TwoToOneCRH>::setup(rng).unwrap();
        Self {
            leaf_crh_params,
            two_to_one_crh_params,
        }
    }
}

pub type AggBLSTwoToOneHash = PedersenCRHCompressor<EdwardsProjective, TECompressor, AggBLSTwoToOneWindow>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AggBLSTwoToOneWindow;

// `WINDOW_SIZE * NUM_WINDOWS` = 2 * 256 bits = enough for hashing two outputs.
impl pedersen::Window for AggBLSTwoToOneWindow {
    const WINDOW_SIZE: usize = 880;
    const NUM_WINDOWS: usize = 4;
}

pub type AggBLSLeafHash = PedersenCRHCompressor<EdwardsProjective, TECompressor, AggBLSLeafWindow>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AggBLSLeafWindow;

// `WINDOW_SIZE * NUM_WINDOWS` = 2 * 256 bits = enough for hashing two outputs.
impl pedersen::Window for AggBLSLeafWindow {
    const WINDOW_SIZE: usize = 880;
    const NUM_WINDOWS: usize = 4;
}

#[derive(Clone)]
pub struct AggBLSMerkleConfig;
impl merkle_tree::Config for AggBLSMerkleConfig {
    type LeafHash = AggBLSLeafHash;
    type TwoToOneHash = AggBLSTwoToOneHash;
}

/// A Merkle tree containing account information.
pub type AggBLSMerkleTree = MerkleTree<AggBLSMerkleConfig>;
/// The root of the account Merkle tree.
pub type AggBLSMerkleRoot = <AggBLSTwoToOneHash as TwoToOneCRH>::Output;
/// A membership proof for a given account.
pub type AggBLSMerklePath = Path<AggBLSMerkleConfig>;

#[derive(Clone)]
pub struct AggBLSState {
    /// A merkle tree mapping where the i-th leaf corresponds to the i-th account's
    /// information (= balance and public key).
    pub universe_merkle_tree: AggBLSMerkleTree,
    pub num_parties: usize,
}

impl AggBLSState {
    /// Create an empty ledger that supports `num_accounts` accounts.
    pub fn new(num_parties: usize, parameters: &AggBLSMerkleParameters) -> Self {
        let height = ark_std::log2(num_parties) + 1;
        let universe_merkle_tree = MerkleTree::blank(
            &parameters.leaf_crh_params,
            &parameters.two_to_one_crh_params,
            height as usize,
        )
        .unwrap();
        Self {
            universe_merkle_tree: universe_merkle_tree,
            num_parties: 0
        }
    }

    /// Return the root of the account Merkle tree.
    pub fn root(&self) -> AggBLSMerkleRoot {
        self.universe_merkle_tree.root()
    }

    /// Create a new account with public key `pub_key`. Returns a fresh account identifier
    /// if there is space for a new account, and returns `None` otherwise.
    /// The initial balance of the new account is 0.
    pub fn register_universe(&mut self, 
        pk: ark_bls12_377::G1Projective,
        weight: ark_bls12_377::Fq) {
        // Construct account information for the new account.
        let uni_info = AggBLSParty { pk, weight };
        // Insert information into the relevant accounts.
        self.universe_merkle_tree
            .update(self.num_parties, &uni_info.to_bytes_le())
            .expect("should exist");
        self.num_parties += 1;
    }

}



pub type AggBLSTwoToOneHashGadget = PedersenCRHCompressorGadget<
    EdwardsProjective,
    TECompressor,
    AggBLSTwoToOneWindow,
    EdwardsVar,
    TECompressorGadget,
>;

pub type AggBLSLeafHashGadget = PedersenCRHCompressorGadget<
    EdwardsProjective,
    TECompressor,
    AggBLSLeafWindow,
    EdwardsVar,
    TECompressorGadget,
>;

pub type AggBLSMerkleRootVar =
    <AggBLSTwoToOneHashGadget as TwoToOneCRHGadget<AggBLSTwoToOneHash, ConstraintF>>::OutputVar;
pub type AggBLSMerklePathVar = PathVar<AggBLSMerkleConfig, AggBLSLeafHashGadget, AggBLSTwoToOneHashGadget, ConstraintF>;
pub type AggBLSLeafHashParamsVar = <AggBLSLeafHashGadget as CRHGadget<AggBLSLeafHash, ConstraintF>>::ParametersVar;
pub type AggBLSTwoToOneHashParamsVar =
    <AggBLSTwoToOneHashGadget as TwoToOneCRHGadget<AggBLSTwoToOneHash, ConstraintF>>::ParametersVar;

/// The parameters that are used in transaction creation and validation.
pub struct AggBLSParametersVar {
    pub leaf_crh_params: AggBLSLeafHashParamsVar,
    pub two_to_one_crh_params: AggBLSTwoToOneHashParamsVar,
}

impl AllocVar<AggBLSMerkleParameters, ConstraintF> for AggBLSParametersVar {
    //#[tracing::instrument(target = "r1cs", skip(cs, f, _mode))]
    fn new_variable<T: Borrow<AggBLSMerkleParameters>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T>,
        _mode: AllocationMode,
    ) -> Result<Self> {
        let cs = cs.into();
        f().and_then(|params| {
            let params: &AggBLSMerkleParameters = params.borrow();
            let leaf_crh_params =
                AggBLSLeafHashParamsVar::new_constant(cs.clone(), &params.leaf_crh_params)?;
            let two_to_one_crh_params =
                AggBLSTwoToOneHashParamsVar::new_constant(cs.clone(), &params.two_to_one_crh_params)?;
            Ok(Self {
                leaf_crh_params,
                two_to_one_crh_params,
            })
        })
    }
}

pub struct AggregateBLS<const NUM_PARTIES: usize> {
    pub pp: AggBLSMerkleParameters,
    pub pks: Vec<ark_bls12_377::G1Projective>,
    pub weights: Vec<ark_bls12_377::Fq>,
    pub h_of_m: ark_bls12_377::G2Projective,
    pub sigmas: Vec<ark_bls12_377::G2Projective>,
    pub merkle_paths: Vec<Path<AggBLSMerkleConfig>>,
    pub merkle_path_params: Path<AggBLSMerkleConfig>,
    pub merkle_root: AggBLSMerkleRoot,
    pub total_signing_weight: u64
}

impl<const NUM_PARTIES: usize> AggregateBLS<NUM_PARTIES> {
    pub fn new() -> Self {

        let mut rng = ark_std::test_rng();

        let mut pks = Vec::with_capacity(NUM_PARTIES);
        let mut weights = Vec::with_capacity(NUM_PARTIES);
        let mut sigmas = Vec::with_capacity(NUM_PARTIES);

        let mut merkle_paths = Vec::with_capacity(NUM_SIGS);

        let pp = AggBLSMerkleParameters::sample(&mut rng);
        let mut state = AggBLSState::new(NUM_PARTIES, &pp);

        let g1_generator: ark_bls12_377::G1Projective = 
                ark_bls12_377::G1Affine::prime_subgroup_generator().into();
        let g2_generator: ark_bls12_377::G2Projective = 
            ark_bls12_377::G2Affine::prime_subgroup_generator().into();
        
        let h_of_m = ark_bls12_377::G2Projective::rand(&mut rng);

        let zero_weight = ark_bls12_377::Fq::new(BigInteger384::try_from(0 as u64).unwrap());
        state.register_universe(g1_generator, zero_weight);

        let mut total_signing_weight: u64 = 0;
        //sample universe parameters and a satisfying signature
        //here we are also registering universes for which we have sigs
        for _i in 0..NUM_PARTIES {
            let weight_u64 = 1 as u64;
            let weight = ark_bls12_377::Fq::new(BigInteger384::try_from(weight_u64).unwrap());
            total_signing_weight += weight_u64;

            let s = ark_bls12_377::Fr::rand(&mut rng);
            let pk = g1_generator.mul(&s.into_repr());
            let sigma = h_of_m.mul(&s.into_repr());

            state.register_universe(pk, weight);

            pks.push(pk);
            weights.push(weight);
            sigmas.push(sigma);
        }

        let merkle_path_params = state.universe_merkle_tree.generate_proof(0).unwrap();
        //compute merkle paths only when all universes are registered, else the paths will be bogus
        for i in 0..NUM_SIGS {
            let party_id: usize = i + 1;
            let path = state.universe_merkle_tree.generate_proof(party_id).unwrap();
            merkle_paths.push(path);
        }
        let merkle_root = state.root();

        Self { 
            pp, 
            pks, 
            weights, 
            h_of_m, 
            sigmas, 
            merkle_paths,
            merkle_path_params,
            merkle_root,
            total_signing_weight
        }
    }
}


impl<const NUM_PARTIES: usize> ConstraintSynthesizer<ConstraintF> for AggregateBLS<NUM_PARTIES> {
    //#[tracing::instrument(target = "r1cs", skip(self, cs))]
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<()> {

        let g1_generator: ark_bls12_377::G1Projective = 
            ark_bls12_377::G1Affine::prime_subgroup_generator().into();
        let g2_generator: ark_bls12_377::G2Projective = 
            ark_bls12_377::G2Affine::prime_subgroup_generator().into();

        let fr_zero = ark_bls12_377::Fr::new(BigInteger256::try_from(0 as u64).unwrap());
        let g1_one = g1_generator.clone().mul(&fr_zero.into_repr());
        let g2_one = g2_generator.clone().mul(&fr_zero.into_repr());

        let ledger_params = AggBLSParametersVar::new_constant(
            ark_relations::ns!(cs, "ledger_params"),
            &self.pp,
        )?;

        let zero_weight = ark_bls12_377::Fq::new(
            BigInteger384::try_from(0 as u64).unwrap());
        
        //merkle root is a public variable shared with the verifier
        let merkle_root_var = 
            AggBLSMerkleRootVar::new_input(
                ark_relations::ns!(cs, "universe_root"), || Ok(self.merkle_root))?;

        let g1_generator_const = G1Var::new_witness(
            ark_relations::ns!(cs, "g1_generator"), || Ok(g1_generator))?;
        let g2_generator_const = G2Var::new_witness(
            ark_relations::ns!(cs, "g2_generator"), || Ok(g2_generator))?;

        let zero_weight_var = FqVar::new_witness(cs.clone(), || Ok(zero_weight))?;
        // let universe_params = AggBLSPartyVar { 
        //     pk: g1_generator_const.clone(), 
        //     weight: zero_weight_var 
        // };

        // let merkle_path = 
        //     AggBLSMerklePathVar::new_witness(
        //         ark_relations::ns!(cs, "universe_existence_path"), 
        //         || Ok(self.merkle_path_params) )?;

        // let valid = merkle_path.verify_membership(
        //     &ledger_params.leaf_crh_params,
        //     &ledger_params.two_to_one_crh_params,
        //     &merkle_root_var,
        //     &universe_params.to_bytes_le().as_slice(),
        // )?;
        // valid.enforce_equal(&Boolean::TRUE)?;


        let threshold_weight = Fp384::new(
            BigInteger384::try_from(NUM_SIGS as u64).unwrap());
        let threshold_weight_fpvar = FpVar::<ark_bls12_377::Fq>::new_input(
            cs.clone(), || Ok(threshold_weight))?;
        
        
        let mut aggregate_weight_fpvar = FqVar::new_witness(
            cs.clone(), || Ok(zero_weight))?;
        let mut aggregate_pk_var = G1Var::new_witness(
            ark_relations::ns!(cs, "aggregate_pk"), || Ok(g1_one))?;
        let mut aggregate_sigma = g2_one;

        
        let h_of_m: ark_bls12_377::G2Projective = self.h_of_m.clone();
        let h_of_m_var = G2Var::new_witness(
            ark_relations::ns!(cs, "h_of_m"), || Ok(h_of_m))?;

        let mut input = vec![];
        for i in 0..NUM_SIGS {
            let merkle_path = self.merkle_paths.get(i).unwrap().clone();
            let pk: ark_bls12_377::G1Projective = self.pks.get(i).unwrap().clone();
            let weight: ark_bls12_377::Fq = self.weights.get(i).unwrap().clone();

            let sigma: ark_bls12_377::G2Projective = self.sigmas.get(i).unwrap().clone();

            let weight_var: FqVar = FqVar::new_witness(ark_relations::ns!(cs, "weight"), || Ok(weight))?;

            let pk_var = G1Var::new_witness(
                ark_relations::ns!(cs, "pk"), || Ok(pk))?;

            let universe_info = AggBLSPartyVar {
                pk: pk_var.clone(),
                weight: weight_var.clone()
            };

            // let merkle_path = AggBLSMerklePathVar::new_witness(
            //     ark_relations::ns!(cs, "universe_existence_path"), || Ok(merkle_path) )?;

            // let valid = merkle_path.verify_membership(
            //     &ledger_params.leaf_crh_params,
            //     &ledger_params.two_to_one_crh_params,
            //     &merkle_root_var,
            //     &universe_info.to_bytes_le().as_slice(),
            // )?;
            // valid.enforce_equal(&Boolean::TRUE)?;

            let scalar: ark_bls12_377::Fr = ark_bls12_377::Fr::from(42 as u64).into();
            let scalar = ark_bls12_377::Fr::from(356356345635234 as u64).
                mul(ark_bls12_377::Fr::from(356356345635234 as u64));
            let scalar = scalar.into_repr();
            let scalar_bits: Vec<bool> = BitIteratorLE::new(&scalar).collect();
            input = Vec::new_witness(ark_relations::ns!(cs, "bits"), || Ok(scalar_bits)).unwrap();

            aggregate_weight_fpvar.add_assign(weight_var);
            pk_var.scalar_mul_le(input.iter());
            aggregate_pk_var.add_assign(pk_var);
            //aggregate_pk_var.scalar_mul_le(input.iter());
            aggregate_sigma.add_assign(sigma);
        }

        let aggregate_sigma_var = G2Var::new_witness(
            ark_relations::ns!(cs, "aggregate_sigma"), || Ok(aggregate_sigma))?;

        threshold_weight_fpvar.enforce_equal(&aggregate_weight_fpvar)?;


        let v1 = constraints::PairingVar::prepare_g1(&aggregate_pk_var)?;
        let v2 = constraints::PairingVar::prepare_g2(&h_of_m_var)?;
        let v3 = constraints::PairingVar::prepare_g1(&g1_generator_const)?;
        let v4 = constraints::PairingVar::prepare_g2(&aggregate_sigma_var)?;

        let p1 = constraints::PairingVar::pairing(v1, v2)?;
        let p2 = constraints::PairingVar::pairing(v3, v4)?;

        p1.enforce_equal(&p2)?;

        println!("circuit size: {}", cs.num_constraints());

        Ok(())
    }
}
