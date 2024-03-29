use std::time::Instant;

use sha2::{Digest, Sha256};

use ark_serialize::CanonicalSerialize;
use ark_ff::{Field, biginteger::BigInteger256};
use ark_poly::{
    Polynomial,
    univariate::DensePolynomial, 
    EvaluationDomain, 
    Radix2EvaluationDomain,
    Evaluations
};
use ark_std::rand::Rng;
use ark_std::{UniformRand, test_rng, ops::*};
use ark_bls12_377::Bls12_377;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ec::VariableBaseMSM;

use kzg::*;

mod utils;
mod kzg;

type Curve = Bls12_377;
type KZG = KZG10::<Curve, DensePolynomial<<Curve as Pairing>::ScalarField>>;
type F = ark_bls12_377::Fr;
type G1 = <Curve as Pairing>::G1Affine;
type G2 = <Curve as Pairing>::G2Affine;

/// hinTS proof structure
struct Proof {
    /// aggregate public key (aPK in the paper)
    agg_pk: G1,
    /// aggregate weight (w in the paper)
    agg_weight: F,

    /// commitment to the bitmap polynomial ([B(τ)]_1 in the paper)
    b_of_tau_com: G1,
    /// commitment to the Q_x polynomial ([Q_x(τ)]_1 in the paper)
    qx_of_tau_com: G1,
    /// commitment to the Q_x polynomial ([Q_x(τ) . τ ]_1 in the paper)
    qx_of_tau_mul_tau_com: G1,
    /// commitment to the Q_z polynomial ([Q_z(τ)]_1 in the paper)
    qz_of_tau_com: G1,
    /// commitment to the ParSum polynomial ([ParSum(τ)]_1 in the paper)
    parsum_of_tau_com: G1,

    /// commitment to the ParSum well-formedness quotient polynomial
    q1_of_tau_com: G1,
    /// commitment to the ParSum check at omega^{n-1} quotient polynomial
    q3_of_tau_com: G1,
    /// commitment to the bitmap well-formedness quotient polynomial
    q2_of_tau_com: G1,
    /// commitment to the bitmap check at omega^{n-1} quotient polynomial
    q4_of_tau_com: G1,

    /// merged opening proof for all openings at x = r
    opening_proof_r: G1,
    /// proof for the ParSum opening at x = r / ω
    opening_proof_r_div_ω: G1,

    /// polynomial evaluation of ParSum(x) at x = r
    parsum_of_r: F,
    /// polynomial evaluation of ParSum(x) at x = r / ω
    parsum_of_r_div_ω: F,
    /// polynomial evaluation of W(x) at x = r
    w_of_r: F,
    /// polynomial evaluation of bitmap B(x) at x = r
    b_of_r: F,
    /// polynomial evaluation of quotient Q1(x) at x = r
    q1_of_r: F,
    /// polynomial evaluation of quotient Q3(x) at x = r
    q3_of_r: F,
    /// polynomial evaluation of quotient Q2(x) at x = r
    q2_of_r: F,
    /// polynomial evaluation of quotient Q4(x) at x = r
    q4_of_r: F,
}

/// Hint contains all material output by a party during the setup phase
#[allow(dead_code)]
struct Hint {
    /// index in the address book
    i: usize,
    /// public key pk = [sk]_1
    pk_i: G1,
    /// [ sk_i L_i(τ) ]_1
    sk_i_l_i_of_tau_com_1: G1,
    /// [ sk_i L_i(τ) ]_2
    sk_i_l_i_of_tau_com_2: G2,
    /// qz_i_terms[i] = [ sk_i * ((L_i^2(τ) - L_i(τ)) / Z(τ)) ]_1
    /// \forall j != i, qz_i_terms[j] = [ sk_i * (L_i(τ) * L_j(τ) / Z(τ)) ]_1
    qz_i_terms: Vec<G1>,
    /// [ sk_i ((L_i(τ) - L_i(0)) / τ ]_1
    qx_i_term: G1,
    /// [ sk_i ((L_i(τ) - L_i(0))]_1
    qx_i_term_mul_tau: G1,
}

/// AggregationKey contains all material needed by Prover to produce a hinTS proof
struct AggregationKey {
    /// number of parties plus one (must be a power of 2)
    n: usize,
    /// weights has all parties' weights, where weights[i] is party i's weight
    weights: Vec<F>,
    /// pks contains all parties' public keys, where pks[i] is g^sk_i
    pks: Vec<G1>,
    /// qz_terms contains pre-processed hints for the Q_z polynomial.
    /// qz_terms[i] has the following form:
    /// [sk_i * (L_i(\tau)^2 - L_i(\tau)) / Z(\tau) + 
    /// \Sigma_{j} sk_j * (L_i(\tau) L_j(\tau)) / Z(\tau)]_1
    qz_terms : Vec<G1>,
    /// qx_terms contains pre-processed hints for the Q_x polynomial.
    /// qx_terms[i] has the form [ sk_i * (L_i(\tau) - L_i(0)) / x ]_1
    qx_terms : Vec<G1>,
    /// qx_mul_tau_terms contains pre-processed hints for the Q_x * x polynomial.
    /// qx_mul_tau_terms[i] has the form [ sk_i * (L_i(\tau) - L_i(0)) ]_1
    qx_mul_tau_terms : Vec<G1>,
}

struct VerificationKey {
    /// the universe has n - 1 parties (where n is a power of 2)
    n: usize,
    /// first G1 element from the KZG CRS (for zeroth power of tau)
    g_0: G1,
    /// first G2 element from the KZG CRS (for zeroth power of tau)
    h_0: G2,
    /// second G1 element from the KZG CRS (for first power of tau)
    h_1: G2,
    /// commitment to the L_{n-1} polynomial
    l_n_minus_1_of_tau_com: G1,
    /// commitment to the W polynomial
    w_of_tau_com: G1,
    /// commitment to the SK polynomial
    sk_of_tau_com: G2,
    /// commitment to the vanishing polynomial Z(x) = x^n - 1
    z_of_tau_com: G2,
    /// commitment to the f(x) = x, which equals [\tau]_2
    tau_com: G2
}

fn sample_weights(n: usize) -> Vec<F> {
    let mut rng = &mut test_rng();
    (0..n).map(|_| F::from(u64::rand(&mut rng))).collect()
}

/// n is the size of the bitmap, and probability is for true or 1.
fn sample_bitmap(n: usize, probability: f64) -> Vec<F> {
    let rng = &mut test_rng();
    let mut bitmap = vec![];
    for _i in 0..n {
        //let r = u64::rand(&mut rng);
        let bit = rng.gen_bool(probability);
        bitmap.push(F::from(bit));
    }
    bitmap
}

fn main() {
    let n = 32;
    println!("n = {}", n);

    // -------------- sample one-time SRS ---------------
    //run KZG setup
    let rng = &mut test_rng();
    let params = KZG::setup(n, rng).expect("Setup failed");

    // -------------- sample universe specific values ---------------
    //sample random keys
    let sk: Vec<F> = sample_secret_keys(n - 1);
    //sample random weights for each party
    let weights = sample_weights(n - 1);

    // -------------- perform universe setup ---------------
    //run universe setup
    let (vk, ak) = setup(n, &params, &weights, &sk);

    // -------------- sample proof specific values ---------------
    //samples n-1 random bits
    let bitmap = sample_bitmap(n - 1, 0.9);

    let start = Instant::now();
    let π = prove(&params, &ak, &vk, &bitmap);
    let duration = start.elapsed();
    println!("Time elapsed in prover is: {:?}", duration);
    

    let start = Instant::now();
    verify(&vk, &π);
    let duration = start.elapsed();
    println!("Time elapsed in verifier is: {:?}", duration);
}

fn setup(
    n: usize,
    params: &UniversalParams<Curve>,
    w: &Vec<F>,
    sk: &Vec<F>
) -> (VerificationKey, AggregationKey)
{
    let mut weights = w.clone();
    let mut sk = sk.clone();

    //last element must be 0
    sk.push(F::from(0));
    weights.push(F::from(0));

    let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
    let w_of_x_com = KZG::commit_g1(&params, &w_of_x).unwrap();

    //allocate space to collect setup material from all n-1 parties
    let mut qz_contributions : Vec<Vec<G1>> = vec![Default::default(); n];
    let mut qx_contributions : Vec<G1> = vec![Default::default(); n];
    let mut qx_mul_tau_contributions : Vec<G1> = vec![Default::default(); n];
    let mut pks : Vec<G1> = vec![Default::default(); n];
    let mut sk_l_of_tau_coms: Vec<G2> = vec![Default::default(); n];
    
    //collect the setup phase material from all parties
    let all_parties_setup = crossbeam::scope(|s| {
        let mut threads = Vec::new();
        for i in 0..n {
            let idx = i.clone();
            let n = n.clone();
            let sk = sk[idx];
            let thread_i = s.spawn(move |_| hint_gen(&params, n, idx, &sk));
            threads.push(thread_i);
        }

        threads.into_iter().map(|t| t.join().unwrap()).collect::<Vec<_>>()
    }).unwrap();

    for hint in all_parties_setup {
        //verify hint
        verify_hint(params, &hint);
        //extract necessary items for pre-processing
        qz_contributions[hint.i] = hint.qz_i_terms.clone();
        qx_contributions[hint.i] = hint.qx_i_term.clone();
        qx_mul_tau_contributions[hint.i] = hint.qx_i_term_mul_tau.clone();
        pks[hint.i] = hint.pk_i.clone();
        sk_l_of_tau_coms[hint.i] = hint.sk_i_l_i_of_tau_com_2.clone();
    }

    let z_of_x = utils::compute_vanishing_poly(n);
    let x_monomial = utils::compute_x_monomial();
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);

    let vp = VerificationKey {
        n: n,
        g_0: params.powers_of_g[0].clone(),
        h_0: params.powers_of_h[0].clone(),
        h_1: params.powers_of_h[1].clone(),
        l_n_minus_1_of_tau_com: KZG::commit_g1(&params, &l_n_minus_1_of_x).unwrap(),
        w_of_tau_com: w_of_x_com,
        // combine all sk_i l_i_of_x commitments to get commitment to sk(x)
        sk_of_tau_com: add_all_g2(&params, &sk_l_of_tau_coms),
        z_of_tau_com: KZG::commit_g2(&params, &z_of_x).unwrap(),
        tau_com: KZG::commit_g2(&params, &x_monomial).unwrap(),
    };

    let pp = AggregationKey {
        n: n,
        weights: w.clone(),
        pks: pks,
        qz_terms: preprocess_qz_contributions(&qz_contributions),
        qx_terms: qx_contributions,
        qx_mul_tau_terms: qx_mul_tau_contributions,
    };

    (vp, pp)

}

//RO(SK, W, B, ParSum, Qx, Qz, Qx(τ ) · τ, Q1, Q2, Q3, Q4)
fn random_oracle(
    sk_com: G2,
    w_com: G1,
    b_com: G1,
    parsum_com: G1,
    qx_com: G1,
    qz_com: G1,
    qx_mul_x_com: G1,
    q1_com: G1,
    q2_com: G1,
    q3_com: G1,
    q4_com: G1,
) -> F {

    let mut serialized_data = Vec::new();
    sk_com.serialize_compressed(&mut serialized_data).unwrap();
    w_com.serialize_compressed(&mut serialized_data).unwrap();
    b_com.serialize_compressed(&mut serialized_data).unwrap();
    parsum_com.serialize_compressed(&mut serialized_data).unwrap();
    qx_com.serialize_compressed(&mut serialized_data).unwrap();
    qz_com.serialize_compressed(&mut serialized_data).unwrap();
    qx_mul_x_com.serialize_compressed(&mut serialized_data).unwrap();
    q1_com.serialize_compressed(&mut serialized_data).unwrap();
    q2_com.serialize_compressed(&mut serialized_data).unwrap();
    q3_com.serialize_compressed(&mut serialized_data).unwrap();
    q4_com.serialize_compressed(&mut serialized_data).unwrap();

    let mut hash_result = Sha256::digest(serialized_data.as_slice());
    hash_result[31] = 0u8; //this makes sure we get a number below modulus
    let hash_bytes = hash_result.as_slice();

    let mut hash_values: [u64; 4] = [0; 4];
    hash_values[0] = u64::from_le_bytes(hash_bytes[0..8].try_into().unwrap());
    hash_values[1] = u64::from_le_bytes(hash_bytes[8..16].try_into().unwrap());
    hash_values[2] = u64::from_le_bytes(hash_bytes[16..24].try_into().unwrap());
    hash_values[3] = u64::from_le_bytes(hash_bytes[24..32].try_into().unwrap());
    //hash_values[3] = u64::from(0u64);

    let bi = BigInteger256::new(hash_values);

    //let input: [u8; 32] = [0u8; 32];
    F::try_from(bi).unwrap()
}

fn prove(
    params: &UniversalParams<Curve>,
    ak: &AggregationKey,
    vk: &VerificationKey,
    bitmap: &Vec<F>) -> Proof {
    // compute the nth root of unity
    let n = ak.n;

    //adjust the weights and bitmap polynomials
    let mut weights = ak.weights.clone();
    //compute sum of weights of active signers
    let total_active_weight = bitmap
        .iter()
        .zip(weights.iter())
        .fold(F::from(0), |acc, (&x, &y)| acc + (x * y));
    //weight's last element must the additive inverse of active weight
    weights.push(F::from(0) - total_active_weight);

    let mut bitmap = bitmap.clone();
    //bitmap's last element must be 1 for our scheme
    bitmap.push(F::from(1));

    //compute all the scalars we will need in the prover
    let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
    let ω: F = domain.group_gen;
    let ω_inv: F = F::from(1) / ω;

    //compute all the polynomials we will need in the prover
    let z_of_x = utils::compute_vanishing_poly(n); //returns Z(X) = X^n - 1
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);
    let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
    let b_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap);
    let psw_of_x = compute_psw_poly(&weights, &bitmap);
    let psw_of_x_div_ω = utils::poly_domain_mult_ω(&psw_of_x, &ω_inv);


    //ParSumW(X) = ParSumW(X/ω) + W(X) · b(X) + Z(X) · Q1(X)
    let t_of_x = psw_of_x.sub(&psw_of_x_div_ω).sub(&w_of_x.mul(&b_of_x));
    let psw_wff_q_of_x = t_of_x.div(&z_of_x);

    //L_{n−1}(X) · ParSumW(X) = Z(X) · Q2(X) 
    let t_of_x = l_n_minus_1_of_x.mul(&psw_of_x);
    let psw_check_q_of_x = t_of_x.div(&z_of_x);

    //b(X) · b(X) − b(X) = Z(X) · Q3(X)
    let t_of_x = b_of_x.mul(&b_of_x).sub(&b_of_x);
    let b_wff_q_of_x = t_of_x.div(&z_of_x);

    //L_{n−1}(X) · (b(X) - 1) = Z(X) · Q4(X)
    let t_of_x = l_n_minus_1_of_x.clone().mul(
        &b_of_x.clone().sub(&utils::compute_constant_poly(&F::from(1))));
    let b_check_q_of_x = t_of_x.div(&z_of_x);

    let qz_com = filter_and_add(&params, &ak.qz_terms, &bitmap);
    let qx_com = filter_and_add(&params, &ak.qx_terms, &bitmap);
    let qx_mul_tau_com = filter_and_add(&params, &ak.qx_mul_tau_terms, &bitmap);
    let agg_pk = compute_apk(&ak, &bitmap);

    let parsum_of_tau_com = KZG::commit_g1(&params, &psw_of_x).unwrap();
    let b_of_tau_com = KZG::commit_g1(&params, &b_of_x).unwrap();
    let q1_of_tau_com = KZG::commit_g1(&params, &psw_wff_q_of_x).unwrap();
    let q2_of_tau_com = KZG::commit_g1(&params, &b_wff_q_of_x).unwrap();
    let q3_of_tau_com = KZG::commit_g1(&params, &psw_check_q_of_x).unwrap();
    let q4_of_tau_com = KZG::commit_g1(&params, &b_check_q_of_x).unwrap();

    // RO(SK, W, B, ParSum, Qx, Qz, Qx(τ ) · τ, Q1, Q2, Q3, Q4)
    let r = random_oracle(
        vk.sk_of_tau_com, 
        vk.w_of_tau_com,
        b_of_tau_com,
        parsum_of_tau_com,
        qx_com,
        qz_com,
        qx_mul_tau_com,
        q1_of_tau_com,
        q2_of_tau_com,
        q3_of_tau_com,
        q4_of_tau_com
    );
    let r_div_ω: F = r / ω;

    let psw_of_r_proof = KZG::compute_opening_proof(&params, &psw_of_x, &r).unwrap();
    let w_of_r_proof = KZG::compute_opening_proof(&params, &w_of_x, &r).unwrap();
    let b_of_r_proof = KZG::compute_opening_proof(&params, &b_of_x, &r).unwrap();
    let psw_wff_q_of_r_proof = KZG::compute_opening_proof(&params, &psw_wff_q_of_x, &r).unwrap();
    let psw_check_q_of_r_proof = KZG::compute_opening_proof(&params, &psw_check_q_of_x, &r).unwrap();
    let b_wff_q_of_r_proof = KZG::compute_opening_proof(&params, &b_wff_q_of_x, &r).unwrap();
    let b_check_q_of_r_proof = KZG::compute_opening_proof(&params, &b_check_q_of_x, &r).unwrap();

    let merged_proof: G1 = (psw_of_r_proof
        + w_of_r_proof.mul(r.pow([1]))
        + b_of_r_proof.mul(r.pow([2]))
        + psw_wff_q_of_r_proof.mul(r.pow([3]))
        + psw_check_q_of_r_proof.mul(r.pow([4]))
        + b_wff_q_of_r_proof.mul(r.pow([5]))
        + b_check_q_of_r_proof.mul(r.pow([6]))).into();

    Proof {
        agg_pk: agg_pk.clone(),
        agg_weight: total_active_weight,
        
        parsum_of_r_div_ω: psw_of_x.evaluate(&r_div_ω),
        opening_proof_r_div_ω: KZG::compute_opening_proof(&params, &psw_of_x, &r_div_ω).unwrap(),

        parsum_of_r: psw_of_x.evaluate(&r),
        w_of_r: w_of_x.evaluate(&r),
        b_of_r: b_of_x.evaluate(&r),
        q1_of_r: psw_wff_q_of_x.evaluate(&r),
        q3_of_r: psw_check_q_of_x.evaluate(&r),
        q2_of_r: b_wff_q_of_x.evaluate(&r),
        q4_of_r: b_check_q_of_x.evaluate(&r),
        
        opening_proof_r: merged_proof.into(),

        parsum_of_tau_com: parsum_of_tau_com,
        b_of_tau_com: b_of_tau_com,
        q1_of_tau_com: q1_of_tau_com,
        q3_of_tau_com: q3_of_tau_com,
        q2_of_tau_com: q2_of_tau_com,
        q4_of_tau_com: q4_of_tau_com,

        qz_of_tau_com: qz_com,
        qx_of_tau_com: qx_com,
        qx_of_tau_mul_tau_com: qx_mul_tau_com,
    }
}

fn verify_opening(
    vp: &VerificationKey, 
    commitment: &G1,
    point: &F, 
    evaluation: &F,
    opening_proof: &G1) {
    let eval_com: G1 = vp.g_0.clone().mul(evaluation).into();
    let point_com: G2 = vp.h_0.clone().mul(point).into();

    let lhs = <Curve as Pairing>::pairing(commitment.clone() - eval_com, vp.h_0);
    let rhs = <Curve as Pairing>::pairing(opening_proof.clone(), vp.h_1 - point_com);
    assert_eq!(lhs, rhs);
}

fn verify_openings_in_proof(vp: &VerificationKey, π: &Proof, r: F) {
    //adjust the w_of_x_com
    let adjustment = F::from(0) - π.agg_weight;
    let adjustment_com = vp.l_n_minus_1_of_tau_com.mul(adjustment);
    let w_of_x_com: G1 = (vp.w_of_tau_com + adjustment_com).into();

    let psw_of_r_argument = π.parsum_of_tau_com - vp.g_0.clone().mul(π.parsum_of_r).into_affine();
    let w_of_r_argument = w_of_x_com - vp.g_0.clone().mul(π.w_of_r).into_affine();
    let b_of_r_argument = π.b_of_tau_com - vp.g_0.clone().mul(π.b_of_r).into_affine();
    let psw_wff_q_of_r_argument = π.q1_of_tau_com - vp.g_0.clone().mul(π.q1_of_r).into_affine();
    let psw_check_q_of_r_argument = π.q3_of_tau_com - vp.g_0.clone().mul(π.q3_of_r).into_affine();
    let b_wff_q_of_r_argument = π.q2_of_tau_com - vp.g_0.clone().mul(π.q2_of_r).into_affine();
    let b_check_q_of_r_argument = π.q4_of_tau_com - vp.g_0.clone().mul(π.q4_of_r).into_affine();

    let merged_argument: G1 = (psw_of_r_argument
        + w_of_r_argument.mul(r.pow([1]))
        + b_of_r_argument.mul(r.pow([2]))
        + psw_wff_q_of_r_argument.mul(r.pow([3]))
        + psw_check_q_of_r_argument.mul(r.pow([4]))
        + b_wff_q_of_r_argument.mul(r.pow([5]))
        + b_check_q_of_r_argument.mul(r.pow([6]))).into_affine();

    let lhs = <Curve as Pairing>::pairing(
        merged_argument, 
        vp.h_0);
    let rhs = <Curve as Pairing>::pairing(
        π.opening_proof_r, 
        vp.h_1 - vp.h_0.clone().mul(r).into_affine());
    assert_eq!(lhs, rhs);

    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = r / ω;
    verify_opening(vp, 
        &π.parsum_of_tau_com, 
        &r_div_ω, 
        &π.parsum_of_r_div_ω, 
        &π.opening_proof_r_div_ω);
}

fn verify(vp: &VerificationKey, π: &Proof) {
    // compute root of unity
    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;

    //RO(SK, W, B, ParSum, Qx, Qz, Qx(τ ) · τ, Q1, Q2, Q3, Q4)
    let r = random_oracle(
        vp.sk_of_tau_com, 
        vp.w_of_tau_com,
        π.b_of_tau_com,
        π.parsum_of_tau_com,
        π.qx_of_tau_com,
        π.qz_of_tau_com,
        π.qx_of_tau_mul_tau_com,
        π.q1_of_tau_com,
        π.q2_of_tau_com,
        π.q3_of_tau_com,
        π.q4_of_tau_com
    );

    // verify the polynomial openings at r and r / ω
    verify_openings_in_proof(vp, π, r);

    let n: u64 = vp.n as u64;
    // this takes logarithmic computation, but concretely efficient
    let vanishing_of_r: F = r.pow([n]) - F::from(1);

    // compute L_i(r) using the relation L_i(x) = Z_V(x) / ( Z_V'(x) (x - ω^i) )
    // where Z_V'(x)^-1 = x / N for N = |V|.
    let ω_pow_n_minus_1 = ω.pow([n-1]);
    let l_n_minus_1_of_r = (ω_pow_n_minus_1 / F::from(n)) * (vanishing_of_r / (r - ω_pow_n_minus_1));

    //assert polynomial identity B(x) SK(x) = ask + Q_z(x) Z(x) + Q_x(x) x
    let lhs = <Curve as Pairing>::pairing(&π.b_of_tau_com, &vp.sk_of_tau_com);
    let x1 = <Curve as Pairing>::pairing(&π.qz_of_tau_com, &vp.z_of_tau_com);
    let x2 = <Curve as Pairing>::pairing(&π.qx_of_tau_com, &vp.tau_com);
    let x3 = <Curve as Pairing>::pairing(&π.agg_pk, &vp.h_0);
    let rhs = x1.add(x2).add(x3);
    assert_eq!(lhs, rhs);

    //assert checks on the public part

    //ParSumW(r) − ParSumW(r/ω) − W(r) · b(r) = Q(r) · (r^n − 1)
    let lhs = π.parsum_of_r - π.parsum_of_r_div_ω - π.w_of_r * π.b_of_r;
    let rhs = π.q1_of_r * vanishing_of_r;
    assert_eq!(lhs, rhs);

    //Ln−1(X) · ParSumW(X) = Z(X) · Q2(X)
    //TODO: compute l_n_minus_1_of_r in verifier -- dont put it in the proof.
    let lhs = l_n_minus_1_of_r * π.parsum_of_r;
    let rhs = vanishing_of_r * π.q3_of_r;
    assert_eq!(lhs, rhs);

    //b(r) * b(r) - b(r) = Q(r) · (r^n − 1)
    let lhs = π.b_of_r * π.b_of_r - π.b_of_r;
    let rhs = π.q2_of_r * vanishing_of_r;
    assert_eq!(lhs, rhs);

    //Ln−1(X) · (b(X) − 1) = Z(X) · Q4(X)
    let lhs = l_n_minus_1_of_r * (π.b_of_r - F::from(1));
    let rhs = vanishing_of_r * π.q4_of_r;
    assert_eq!(lhs, rhs);

    //run the degree check e([Qx(τ)]_1, [τ]_2) ?= e([Qx(τ)·τ]_1, [1]_2)
    let lhs = <Curve as Pairing>::pairing(&π.qx_of_tau_com, &vp.h_1);
    let rhs = <Curve as Pairing>::pairing(&π.qx_of_tau_mul_tau_com, &vp.h_0);
    assert_eq!(lhs, rhs);

}


fn compute_apk(
    pp: &AggregationKey, 
    bitmap: &Vec<F>) -> G1 {
    let n = bitmap.len();
    let mut exponents: Vec<F> = vec![];
    let n_inv = F::from(1) / F::from(n as u64);
    for i in 0..n {
        //let l_i_of_x = cache.lagrange_polynomials[i].clone();
        //let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
        let l_i_of_0 = n_inv;
        let active = bitmap[i] == F::from(1);
        exponents.push(if active { l_i_of_0 } else { F::from(0) });
    }

    <<Curve as Pairing>::G1 as VariableBaseMSM>
        ::msm(&pp.pks[..], &exponents).unwrap().into_affine()
}

fn preprocess_qz_contributions(
    q1_contributions: &Vec<Vec<G1>>
) -> Vec<G1> {
    let n = q1_contributions.len();
    let mut q1_coms = vec![];

    for i in 0..n {
        // extract party i's hints, from which we extract the term for i.
        let mut party_i_q1_com = q1_contributions[i][i].clone();
        for j in 0..n {
            if i != j {
                // extract party j's hints, from which we extract cross-term for party i
                let party_j_contribution = q1_contributions[j][i].clone();
                party_i_q1_com = party_i_q1_com.add(party_j_contribution).into();
            }
        }
        // the aggregation key contains a single term that 
        // is a product of all cross-terms and the ith term
        q1_coms.push(party_i_q1_com);
    }
    q1_coms
}

fn filter_and_add(
    params: &UniversalParams<Curve>, 
    elements: &Vec<G1>, 
    bitmap: &Vec<F>) -> G1 {
    let mut com = get_zero_poly_com_g1(&params);
    for i in 0..bitmap.len() {
        if bitmap[i] == F::from(1) {
            com = com.add(elements[i]).into_affine();
        }
    }
    com
}

fn add_all_g2(
    params: &UniversalParams<Curve>, 
    elements: &Vec<G2>) -> G2 {
    let mut com = get_zero_poly_com_g2(&params);
    for i in 0..elements.len() {
        com = com.add(elements[i]).into_affine();
    }
    com
}

fn get_zero_poly_com_g1(params: &UniversalParams<Curve>) -> G1 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g1(&params, &zero_poly).unwrap()
}

fn get_zero_poly_com_g2(params: &UniversalParams<Curve>) -> G2 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g2(&params, &zero_poly).unwrap()
}

fn sample_secret_keys(num_parties: usize) -> Vec<F> {
    let mut rng = test_rng();
    let mut keys = vec![];
    for _ in 0..num_parties {
        keys.push(F::rand(&mut rng));
    }
    keys
}

fn compute_psw_poly(weights: &Vec<F>, bitmap: &Vec<F>) -> DensePolynomial<F> {
    let n = weights.len();
    let mut parsum = F::from(0);
    let mut evals = vec![];
    for i in 0..n {
        let w_i_b_i = bitmap[i] * weights[i];
        parsum += w_i_b_i;
        evals.push(parsum);
    }

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()    
}

fn hint_gen(
    params: &UniversalParams<Curve>,
    n: usize, 
    i: usize, 
    sk_i: &F) -> Hint {
    //let us compute the q1 term
    let l_i_of_x = utils::lagrange_poly(n, i);
    let z_of_x = utils::compute_vanishing_poly(n);

    let mut qz_terms = vec![];
    //let us compute the cross terms of q1
    for j in 0..n {
        let num: DensePolynomial<F>;// = compute_constant_poly(&F::from(0));
        if i == j {
            num = l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x);
        } else { //cross-terms
            let l_j_of_x = utils::lagrange_poly(n, j);
            num = l_j_of_x.mul(&l_i_of_x);
        }

        let f = num.div(&z_of_x);
        let sk_times_f = utils::poly_eval_mult_c(&f, &sk_i);

        let com = KZG::commit_g1(&params, &sk_times_f)
            .expect("commitment failed");

        qz_terms.push(com);
    }

    let x_monomial = utils::compute_x_monomial();
    let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);

    //numerator is l_i(x) - l_i(0)
    let num = l_i_of_x.sub(&l_i_of_0_poly);
    //denominator is x
    let den = x_monomial.clone();
    //qx_term = sk_i * (l_i(x) - l_i(0)) / x
    let qx_term = utils::poly_eval_mult_c(&num.div(&den), &sk_i);
    //qx_term_mul_tau = sk_i * (l_i(x) - l_i(0)) / x
    let qx_term_mul_tau = utils::poly_eval_mult_c(&num, &sk_i);
    //qx_term_com = [ sk_i * (l_i(τ) - l_i(0)) / τ ]_1
    let qx_term_com = KZG::commit_g1(&params, &qx_term).expect("commitment failed");
    //qx_term_mul_tau_com = [ sk_i * (l_i(τ) - l_i(0)) ]_1
    let qx_term_mul_tau_com = KZG::commit_g1(&params, &qx_term_mul_tau).expect("commitment failed");

    //release my public key
    let sk_as_poly = utils::compute_constant_poly(&sk_i);
    let pk = KZG::commit_g1(&params, &sk_as_poly).expect("commitment failed");

    let sk_times_l_i_of_x = utils::poly_eval_mult_c(&l_i_of_x, &sk_i);
    let com_sk_l_i_g1 = KZG::commit_g1(&params, &sk_times_l_i_of_x).expect("commitment failed");
    let com_sk_l_i_g2 = KZG::commit_g2(&params, &sk_times_l_i_of_x).expect("commitment failed");

    Hint {
        i: i,
        pk_i: pk,
        sk_i_l_i_of_tau_com_1: com_sk_l_i_g1,
        sk_i_l_i_of_tau_com_2: com_sk_l_i_g2,
        qz_i_terms: qz_terms,
        qx_i_term: qx_term_com,
        qx_i_term_mul_tau: qx_term_mul_tau_com,
    }
}

fn verify_hint(params: &UniversalParams<Curve>, hint: &Hint) {
    let i = hint.i;
    let n = hint.qz_i_terms.len();

    //e([sk_i L_i(τ)]1, [1]2) = e([sk_i]1, [L_i(τ)]2)
    let l_i_of_x = utils::lagrange_poly(n, i);
    let z_of_x = utils::compute_vanishing_poly(n);

    let l_i_of_tau_com = KZG::commit_g2(&params, &l_i_of_x).expect("commitment failed");
    let lhs = <Curve as Pairing>::pairing(hint.sk_i_l_i_of_tau_com_1, params.powers_of_h[0]);
    let rhs = <Curve as Pairing>::pairing(hint.pk_i, l_i_of_tau_com);
    assert_eq!(lhs, rhs);

    for j in 0..n {
        let num: DensePolynomial<F>;
        if i == j {
            num = l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x);
        } else { //cross-terms
            let l_j_of_x = utils::lagrange_poly(n, j);
            num = l_j_of_x.mul(&l_i_of_x);
        }
        let f = num.div(&z_of_x);

        //f = li^2 - l_i / z or li lj / z
        let f_com = KZG::commit_g2(&params, &f).expect("commitment failed");
        
        let lhs = <Curve as Pairing>::pairing(hint.qz_i_terms[j], params.powers_of_h[0]);
        let rhs = <Curve as Pairing>::pairing(hint.pk_i, f_com);
        assert_eq!(lhs, rhs);
    }

    let x_monomial = utils::compute_x_monomial();
    let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);

    //numerator is l_i(x) - l_i(0)
    let num = l_i_of_x.sub(&l_i_of_0_poly);
    //denominator is x
    let den = x_monomial.clone();

    //qx_term = (l_i(x) - l_i(0)) / x
    let qx_term = &num.div(&den);
    //qx_term_com = [ sk_i * (l_i(τ) - l_i(0)) / τ ]_1
    let qx_term_com = KZG::commit_g2(&params, &qx_term).expect("commitment failed");
    let lhs = <Curve as Pairing>::pairing(hint.qx_i_term, params.powers_of_h[0]);
    let rhs = <Curve as Pairing>::pairing(hint.pk_i, qx_term_com);
    assert_eq!(lhs, rhs);

    //qx_term_mul_tau = (l_i(x) - l_i(0))
    let qx_term_mul_tau = &num;
    //qx_term_mul_tau_com = [ (l_i(τ) - l_i(0)) ]_1
    let qx_term_mul_tau_com = KZG::commit_g2(&params, &qx_term_mul_tau).expect("commitment failed");
    let lhs = <Curve as Pairing>::pairing(hint.qx_i_term_mul_tau, params.powers_of_h[0]);
    let rhs = <Curve as Pairing>::pairing(hint.pk_i, qx_term_mul_tau_com);
    assert_eq!(lhs, rhs);

}

#[cfg(test)]
mod tests {
    use super::*;

    fn aggregate_sk(sk: &Vec<F>, bitmap: &Vec<F>) -> F {
        let n = sk.len();
        let mut agg_sk = F::from(0);
        for i in 0..sk.len() {
            let l_i_of_x = utils::lagrange_poly(n, i);
            let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
            agg_sk += bitmap[i] * sk[i] * l_i_of_0;
        }
        agg_sk
    }

    fn sanity_test_poly_domain_mult(
        f_of_x: &DensePolynomial<F>, 
        f_of_ωx: &DensePolynomial<F>, 
        ω: &F) {
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
        let ωr: F = ω.clone() * r;
        assert_eq!(f_of_x.evaluate(&ωr), f_of_ωx.evaluate(&r));
    }

    fn sanity_test_b(
        b_of_x: &DensePolynomial<F>,
        q_of_x: &DensePolynomial<F>
    ) {
    
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
    
        let n: u64 = (b_of_x.degree() + 1) as u64;
    
        let b_of_r = b_of_x.evaluate(&r);
        let q_of_r = q_of_x.evaluate(&r);
        let vanishing_of_r: F = r.pow([n]) - F::from(1);
    
        //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
        let left = b_of_r * b_of_r - b_of_r;
        let right = q_of_r * vanishing_of_r;
        //println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
        //println!("Q(r) · (r^n - 1) = {:?}", tmp2);
        assert_eq!(left, right);
    
    }
    
    fn sanity_test_psw(
        w_of_x: &DensePolynomial<F>,
        b_of_x: &DensePolynomial<F>,
        psw_of_x: &DensePolynomial<F>,
        q_of_x: &DensePolynomial<F>
    ) {
    
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
    
        let n: u64 = (b_of_x.degree() + 1) as u64;
        let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
        let ω: F = domain.group_gen;
        let ω_pow_n_minus_1: F = ω.pow([n-1]);
        let ωr: F = ω * r;
    
        let psw_of_r = psw_of_x.evaluate(&r);
        let psw_of_ωr = psw_of_x.evaluate(&ωr);
        let w_of_ωr = w_of_x.evaluate(&ωr);
        let b_of_ωr = b_of_x.evaluate(&ωr);
        let q_of_r = q_of_x.evaluate(&r);
        let vanishing_of_r: F = r.pow([n]) - F::from(1);
    
        //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
        let tmp1 = psw_of_ωr - psw_of_r - w_of_ωr * b_of_ωr;
        let tmp2 = q_of_r * vanishing_of_r;
        //println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
        //println!("Q(r) · (r^n - 1) = {:?}", tmp2);
        assert_eq!(tmp1, tmp2);
    
        //ParSumW(ωn−1) = 0
        let psw_of_ω_pow_n_minus_1 = psw_of_x.evaluate(&ω_pow_n_minus_1);
        //println!("ParSumW(ω^(n-1)) = {:?}", psw_of_ω_pow_n_minus_1);
        assert_eq!(psw_of_ω_pow_n_minus_1, F::from(0));
    
        //b(ωn−1) = 1
        let b_of_ω_pow_n_minus_1 = b_of_x.evaluate(&ω_pow_n_minus_1);
        assert_eq!(b_of_ω_pow_n_minus_1, F::from(1));
    
    }

    #[test]
    fn sanity_test_public_part() {
        // compute the nth root of unity
        //println!("The nth root of unity is: {:?}", ω);
        //println!("The omega_n_minus_1 of unity is: {:?}", ω.pow([n-1]));
        //println!("The omega_n of unity is: {:?}", ω_pow_n_minus_1 * ω);

        let weights: Vec<F> = vec![
            F::from(2), 
            F::from(3), 
            F::from(4), 
            F::from(5), 
            F::from(4), 
            F::from(3), 
            F::from(2), 
            F::from(0)-F::from(15)
        ];
        let bitmap: Vec<F> = vec![
            F::from(1),
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(1), 
            F::from(1)
        ];

        let n: u64 = bitmap.len() as u64;
        let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
        let ω: F = domain.group_gen;

        let w_of_x = utils::interpolate_poly_over_mult_subgroup(&weights);
        let w_of_ωx = utils::poly_domain_mult_ω(&w_of_x, &ω);

        let b_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap);
        let b_of_ωx = utils::poly_domain_mult_ω(&b_of_x, &ω);

        let psw_of_x = compute_psw_poly(&weights, &bitmap);
        let psw_of_ωx = utils::poly_domain_mult_ω(&psw_of_x, &ω);

        //t(X) = ParSumW(ω · X) − ParSumW(X) − W(ω · X) · b(ω · X)
        let t_of_x = psw_of_ωx.sub(&psw_of_x).sub(&w_of_ωx.mul(&b_of_ωx));
        let z_of_x = utils::compute_vanishing_poly(n as usize); //returns Z(X) = X^n - 1
        let q2_of_x = t_of_x.div(&z_of_x);

        let t_of_x = b_of_x.mul(&b_of_x).sub(&b_of_x);
        let q1_of_x = t_of_x.div(&z_of_x);
        
        sanity_test_poly_domain_mult(&w_of_x, &w_of_ωx, &ω);
        sanity_test_poly_domain_mult(&b_of_x, &b_of_ωx, &ω);
        sanity_test_poly_domain_mult(&psw_of_x, &psw_of_ωx, &ω);

        sanity_test_psw(&w_of_x, &b_of_x, &psw_of_x, &q2_of_x);
        sanity_test_b(&b_of_x, &q1_of_x);
    }

    fn sanity_test_pssk(
        sk_of_x: &DensePolynomial<F>,
        b_of_x: &DensePolynomial<F>,
        q1_of_x: &DensePolynomial<F>,
        q2_of_x: &DensePolynomial<F>,
        agg_sk: &F
    ) {
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
        let n: u64 = (sk_of_x.degree() + 1) as u64;

        //SK(x) · B(x) − aSK = Q1(x) · Z(x) + Q2(x) · x
        let sk_of_r = sk_of_x.evaluate(&r);
        let b_of_r = b_of_x.evaluate(&r);
        let q1_of_r = q1_of_x.evaluate(&r);
        let z_of_r: F = r.pow([n]) - F::from(1);
        let q2_of_r = q2_of_x.evaluate(&r);

        let left = sk_of_r * b_of_r;
        let right = (q1_of_r * z_of_r) + (q2_of_r * r) + agg_sk;
        assert_eq!(left, right);
    
    }

    #[test]
    fn sanity_test_secret_part() {
        //let weights: Vec<u64> = vec![2, 3, 4, 5, 4, 3, 2];
        let bitmap: Vec<F> = vec![
            F::from(1),
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(1), 
            F::from(1)
        ];

        let n = bitmap.len();

        let mut secret_keys: Vec<F> = sample_secret_keys(n - 1);
        secret_keys.push(F::from(0));

        let agg_sk = aggregate_sk(&secret_keys, &bitmap);
        let sk_of_x = utils::interpolate_poly_over_mult_subgroup(&secret_keys);
        let b_of_x = utils::interpolate_poly_over_mult_subgroup(&bitmap);
        let q1_of_x = compute_pssk_q1_poly(&secret_keys, &bitmap);
        let q2_of_x = compute_pssk_q2_poly(&secret_keys, &bitmap);

        sanity_test_pssk(&sk_of_x, &b_of_x, &q1_of_x, &q2_of_x, &agg_sk);
    }

    fn compute_pssk_q1_poly(
        sk: &Vec<F>, 
        bitmap: &Vec<F>
    ) -> DensePolynomial<F> {
        let n = sk.len();
        let z_of_x = utils::compute_vanishing_poly(n);
        //Li(x) · Li(x) − Li(x) / Z(x)
        let mut q1 = utils::compute_constant_poly(&F::from(0));

        for i in 0..n {
            if bitmap[i] == F::from(0) { continue; }

            let l_i_of_x = utils::lagrange_poly(n, i);
            let num = l_i_of_x.mul(&l_i_of_x).sub(&l_i_of_x);
            //let num = num.sub(&l_i_of_x);
            let f_i = num.div(&z_of_x);
            let sk_i_f_i = utils::poly_eval_mult_c(&f_i, &sk[i]);

            q1 = q1.add(sk_i_f_i);

            let mut q1_inner = utils::compute_constant_poly(&F::from(0));
            for j in 0..n {
                if i == j { continue; } //i != j

                let l_j_of_x = utils::lagrange_poly(n, j);
                let num = l_j_of_x.mul(&l_i_of_x);
                let f_j = num.div(&z_of_x);
                let sk_j_f_j = utils::poly_eval_mult_c(&f_j, &sk[j]);

                q1_inner = q1_inner.add(sk_j_f_j);
            }

            q1 = q1.add(q1_inner);
        }
        q1
    }

    fn compute_pssk_q2_poly(
        sk: &Vec<F>, 
        bitmap: &Vec<F>
    ) -> DensePolynomial<F> {
        let n = sk.len();
        let x_monomial = utils::compute_x_monomial();

        let mut q2 = utils::compute_constant_poly(&F::from(0));

        for i in 0..n {
            if bitmap[i] == F::from(0) { continue; }

            let l_i_of_x = utils::lagrange_poly(n, i);
            let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
            let l_i_of_0 = utils::compute_constant_poly(&l_i_of_0);
            let num = l_i_of_x.sub(&l_i_of_0);
            let den = x_monomial.clone();
            let f_i = num.div(&den);
            let sk_i_f_i = utils::poly_eval_mult_c(&f_i, &sk[i]);

            q2 = q2.add(sk_i_f_i);
        }
        q2
    }

}
