// The polynomial evaluation argument is used to prove set membership or non-membership in zero knowledge
// First construct a polynomial with roots as the elements of the set, i.e. if set has items i_0, i_1, i_2, .., i_n, polynomial P(X) = (X-i_0)*(X-i_1)*(X-i_2)*(X-i_n)
// For proving membership of a committed item u with commitment c_0, prove that the polynomial evaluates to 0 at u, i.e. P(u) = 0.
// For proving non-membership of a committed item u with commitment c_0, prove that the polynomial evaluates to non-zero value at u, i.e. P(u) != 0


use amcl_wrapper::field_elem::FieldElement;
use crate::univar_poly_eval_arg::{CommitmentKey, UnivarPolyEvalArgProtocol, UnivarPolyEvalArg};
use amcl_wrapper::univar_poly::UnivarPolynomial;
use amcl_wrapper::group_elem::GroupElement;
use amcl_wrapper::group_elem_g1::{G1, G1Vector};
use std::iter;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SetMembershipProtocol {
    pub poly: UnivarPolynomial,
    pub poly_eval_arg_protocol: UnivarPolyEvalArgProtocol,
    /// randomness for proving evaluation is 0 using Schnorr Id protocol
    z: FieldElement,
    /// h^z, commitment to randomness for above Schnorr id protocol
    t: G1
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SetMembershipArg {
    pub poly_eval_arg: UnivarPolyEvalArg,
    /// Commitment to the evaluation. This should be proved a commitment to 0
    pub comm_evaluation: G1,
    pub t: G1,
    pub s: FieldElement,
}

fn construct_polynomial_for_set(set: &[FieldElement]) -> UnivarPolynomial {
    assert!(set.len().is_power_of_two());
    // Construct a polynomial with roots as the elements of the set
    UnivarPolynomial::new_with_roots(set)
}

impl SetMembershipProtocol {
    /// Initialize protocol to prove that element `member` is part of the set `set` and is committed in `comm_member` with blinding `blinding_member`
    pub fn init(set: &[FieldElement], member: FieldElement, blinding_member: FieldElement, comm_member: G1, comm_key: &CommitmentKey) -> Self {
        let poly = construct_polynomial_for_set(set);
        // To prove comm_evaluation is a commitment to 0, it is sufficient to prove that comm_evaluation
        // is of the form {comm_key.h}^blinding_evaluation which can be done with Schnorr's
        // identification protocol.
        let z = FieldElement::random();
        let t = &comm_key.h * &z;

        // Prove that the polynomial evaluates to 0 at `member`
        let evaluation = FieldElement::zero();
        let blinding_evaluation = FieldElement::random();
        let comm_evaluation = comm_key.commit(&evaluation, &blinding_evaluation);

        let poly_eval_arg_protocol = UnivarPolyEvalArgProtocol::init_with_given_commitments(&poly, member, evaluation, blinding_member, blinding_evaluation, comm_member, comm_evaluation, comm_key);

        Self {poly, poly_eval_arg_protocol, z, t}
    }

    pub fn respond(self, challenge: &FieldElement) -> SetMembershipArg {
        let comm_evaluation = self.poly_eval_arg_protocol.comm_evaluation().clone();
        // response for Schnorr's Id protocol for proving commitment to evaluation is a commitment to 0
        let s = &self.z + &(challenge * self.poly_eval_arg_protocol.blinding_evaluation());

        // response for Polynomial evaluation argument
        let poly_eval_arg = self.poly_eval_arg_protocol.respond(&challenge);

        SetMembershipArg {poly_eval_arg, comm_evaluation, t: self.t, s}
    }

    pub fn get_bytes_for_challenge(&self, comm_key: &CommitmentKey) -> Vec<u8> {
        let mut bytes = vec![];
        bytes.append(&mut self.t.to_bytes());
        bytes.append(&mut self.poly_eval_arg_protocol.get_bytes_for_challenge(&self.poly, comm_key));
        bytes
    }
}

impl SetMembershipArg {
    // TODO: Abstract the following code in macros so it can be shared with SetNonMembershipArg
    pub fn get_bytes_for_challenge(&self, set: &[FieldElement], comm_variable: &G1, comm_key: &CommitmentKey) -> Vec<u8> {
        let poly = construct_polynomial_for_set(set);
        self.get_bytes_for_challenge_with_poly_constructed(&poly, comm_variable, comm_key)
    }

    pub fn verify(&self, challenge: &FieldElement, set: &[FieldElement], comm_variable: &G1, comm_key: &CommitmentKey) -> bool {
        let poly = construct_polynomial_for_set(set);
        self.verify_with_poly_constructed(challenge, &poly, comm_variable,comm_key)
    }

    pub fn get_bytes_for_challenge_with_poly_constructed(&self, poly: &UnivarPolynomial, comm_variable: &G1, comm_key: &CommitmentKey) -> Vec<u8> {
        let mut bytes = vec![];
        bytes.append(&mut self.t.to_bytes());
        bytes.append(&mut self.poly_eval_arg.get_bytes_for_challenge(poly, comm_variable, &self.comm_evaluation, comm_key));
        bytes
    }

    pub fn verify_with_poly_constructed(&self, challenge: &FieldElement, poly: &UnivarPolynomial, comm_variable: &G1, comm_key: &CommitmentKey) -> bool {
        // check that self.comm_evaluation is a commitment to 0 i.e. check h^s == t * {comm_evaluation}^challenge
        // which is equivalent to the check t * {comm_evaluation}^challenge * {1/h}^s == 1
        if !G1Vector::multi_scalar_mul_var_time_without_precomputation(
            iter::once(&self.t).chain(iter::once(&self.comm_evaluation)).chain(iter::once(&(-&comm_key.h))),
            iter::once(&FieldElement::one()).chain(iter::once(challenge)).chain(iter::once(&self.s))
        ).unwrap().is_identity() {
            return false
        }

        // verify polynomial evaluation argument
        self.poly_eval_arg.verify(challenge, poly, comm_variable, &self.comm_evaluation, comm_key)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SetNonMembershipProtocol {
    pub poly: UnivarPolynomial,
    pub poly_eval_arg_protocol: UnivarPolyEvalArgProtocol,
    /// randomness for proving evaluation is non-zero
    y: FieldElement,
    z: FieldElement,
    /// comm_evaluation^y * h^-z, commitment to s with blinding -z
    t: G1
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SetNonMembershipArg {
    pub poly_eval_arg: UnivarPolyEvalArg,
    /// Commitment to the evaluation. This should be proved a commitment to a non-zero value
    pub comm_evaluation: G1,
    pub t: G1,
    pub s_1: FieldElement,
    pub s_2: FieldElement,
}

impl SetNonMembershipProtocol {
    /// Initialize protocol to prove that element `non_member` is not part of the set `set` and is committed in `comm_non_member` with blinding `blinding_non_member`
    pub fn init(set: &[FieldElement], non_member: FieldElement, blinding_non_member: FieldElement, comm_non_member: G1, comm_key: &CommitmentKey) -> Self {
        let poly = construct_polynomial_for_set(set);

        // The polynomial evaluates to `evaluation` at `non_member`
        let evaluation = poly.eval(&non_member);
        // Commit to the evaluation
        let blinding_evaluation = FieldElement::random();
        let comm_evaluation = comm_key.commit(&evaluation, &blinding_evaluation);

        // Prove comm_evaluation is a commitment to a non-zero value implying `evaluation` != 0.
        // `evaluation` != 0 implies `evaluation`^-1 exists in the field
        let y = FieldElement::random();
        let z = FieldElement::random();
        // t = comm_evaluation^y * h^-z
        let t = G1Vector::multi_scalar_mul_const_time_without_precomputation(
            iter::once(&comm_evaluation).chain(iter::once(&comm_key.h)),
            iter::once(&y).chain(iter::once(&(-&z)))
        ).unwrap();

        let poly_eval_arg_protocol = UnivarPolyEvalArgProtocol::init_with_given_commitments(&poly, non_member, evaluation, blinding_non_member, blinding_evaluation, comm_non_member, comm_evaluation, comm_key);

        Self { poly, poly_eval_arg_protocol, y, z, t}
    }

    pub fn respond(self, challenge: &FieldElement) -> SetNonMembershipArg {
        let comm_evaluation = self.poly_eval_arg_protocol.comm_evaluation().clone();

        // {v^-1}
        let eval_inverse = self.poly_eval_arg_protocol.evaluation().inverse();

        // challenge*{v^-1}
        let chal_v_inv = challenge * &eval_inverse;
        // s_1 = y + challenge*{v^-1}
        let s_1 = &self.y + &chal_v_inv;
        // s_2 = z + challenge*{v^-1}*{blinding for v}
        let s_2 = &self.z + &(&chal_v_inv * self.poly_eval_arg_protocol.blinding_evaluation());

        // response for Polynomial evaluation argument
        let poly_eval_arg = self.poly_eval_arg_protocol.respond(&challenge);

        SetNonMembershipArg {poly_eval_arg, comm_evaluation, t: self.t, s_1, s_2}
    }

    pub fn get_bytes_for_challenge(&self, comm_key: &CommitmentKey) -> Vec<u8> {
        let mut bytes = vec![];
        bytes.append(&mut self.t.to_bytes());
        bytes.append(&mut self.poly_eval_arg_protocol.get_bytes_for_challenge(&self.poly, comm_key));
        bytes
    }
}

impl SetNonMembershipArg {
    pub fn get_bytes_for_challenge(&self, set: &[FieldElement], comm_variable: &G1, comm_key: &CommitmentKey) -> Vec<u8> {
        let poly = construct_polynomial_for_set(set);
        self.get_bytes_for_challenge_with_poly_constructed(&poly, comm_variable, comm_key)
    }

    pub fn verify(&self, challenge: &FieldElement, set: &[FieldElement], comm_variable: &G1, comm_key: &CommitmentKey) -> bool {
        let poly = construct_polynomial_for_set(set);
        self.verify_with_poly_constructed(challenge, &poly, comm_variable,comm_key)
    }

    pub fn get_bytes_for_challenge_with_poly_constructed(&self, poly: &UnivarPolynomial, comm_variable: &G1, comm_key: &CommitmentKey) -> Vec<u8> {
        let mut bytes = vec![];
        bytes.append(&mut self.t.to_bytes());
        bytes.append(&mut self.poly_eval_arg.get_bytes_for_challenge(poly, comm_variable, &self.comm_evaluation, comm_key));
        bytes
    }

    pub fn verify_with_poly_constructed(&self, challenge: &FieldElement, poly: &UnivarPolynomial, comm_variable: &G1, comm_key: &CommitmentKey) -> bool {
        // check that t * g^challenge * h^s_2 == comm_evaluation^s_1
        // which is equivalent to the check t * g^challenge * h^s_2 * comm_evaluation^{-s_1} == 1
        if !G1Vector::multi_scalar_mul_var_time_without_precomputation(
            iter::once(&self.t).chain(iter::once(&comm_key.g)).chain(iter::once(&comm_key.h)).chain(iter::once(&self.comm_evaluation)),
            iter::once(&FieldElement::one()).chain(iter::once(challenge)).chain(iter::once(&self.s_2)).chain(iter::once(&(-&self.s_1)))
        ).unwrap().is_identity() {
            return false
        }

        // verify polynomial evaluation argument
        self.poly_eval_arg.verify(challenge, poly, comm_variable, &self.comm_evaluation, comm_key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;
    use std::time::{Duration, Instant};
    use amcl_wrapper::field_elem::{FieldElementVector, FieldElement};

    #[test]
    fn test_prove_set_membership() {
        let mut rng = rand::thread_rng();
        let comm_key = CommitmentKey::new("test".as_bytes());

        for set_size in vec![2, 4, 8, 16, 32, 64, 128, 256, 512, 1024] {
            let set: Vec<FieldElement> = FieldElementVector::random(set_size).into();
            // pick random member of the set to prove membership
            let member_idx = rng.gen_range(0, set_size);
            let member = set[member_idx].clone();

            // Commit to member. In practice, this commitment (with blinding) will come from another protocol
            let blinding_member = FieldElement::random();
            let comm_member = comm_key.commit(&member, &blinding_member);

            let start_prover = Instant::now();

            let protocol = SetMembershipProtocol::init(&set, member, blinding_member, comm_member.clone(), &comm_key);
            let challenge_by_prover = FieldElement::from_msg_hash(&protocol.get_bytes_for_challenge(&comm_key));
            let zk_argument = protocol.respond(&challenge_by_prover);

            let prover_time = start_prover.elapsed();

            let start_verifier = Instant::now();

            let challenge_by_verifier = FieldElement::from_msg_hash(&zk_argument.get_bytes_for_challenge(&set, &comm_member, &comm_key));
            assert_eq!(challenge_by_prover, challenge_by_verifier);
            assert!(zk_argument.verify(&challenge_by_verifier, &set, &comm_member, &comm_key));

            let verifier_time = start_verifier.elapsed();

            let start_verifier = Instant::now();

            // Construct a polynomial with roots as the elements of the set. The polynomial can be constructed
            // once for both `get_bytes_for_challenge_with_poly_constructed` and `verify_with_poly_constructed`
            let poly = construct_polynomial_for_set(&set);
            let challenge_by_verifier = FieldElement::from_msg_hash(&zk_argument.get_bytes_for_challenge_with_poly_constructed(&poly, &comm_member, &comm_key));
            assert_eq!(challenge_by_prover, challenge_by_verifier);
            assert!(zk_argument.verify_with_poly_constructed(&challenge_by_verifier, &poly, &comm_member, &comm_key));

            let verifier_time_with_poly_construction_once = start_verifier.elapsed();

            println!("For set size {}, proving time is {:?}, naive verification time is {:?}, verification time with polynomial computed only once is {:?}", set_size, prover_time, verifier_time, verifier_time_with_poly_construction_once);
        }
    }

    #[test]
    fn test_prove_set_non_membership() {
        let mut rng = rand::thread_rng();
        let comm_key = CommitmentKey::new("test".as_bytes());

        for set_size in vec![2, 4, 8, 16, 32, 64, 128, 256, 512, 1024] {
            let set: Vec<FieldElement> = FieldElementVector::random(set_size).into();
            // pick random element and ensure its not member of the set
            let mut non_member = FieldElement::random();
            while set.contains(&non_member) {
                non_member = FieldElement::random();
            }

            // Commit to non_member. In practice, this commitment (with blinding) will come from another protocol
            let blinding_non_member = FieldElement::random();
            let comm_non_member = comm_key.commit(&non_member, &blinding_non_member);

            let start_prover = Instant::now();

            let protocol = SetNonMembershipProtocol::init(&set, non_member, blinding_non_member, comm_non_member.clone(), &comm_key);
            let challenge_by_prover = FieldElement::from_msg_hash(&protocol.get_bytes_for_challenge(&comm_key));
            let zk_argument = protocol.respond(&challenge_by_prover);

            let prover_time = start_prover.elapsed();

            let start_verifier = Instant::now();

            let challenge_by_verifier = FieldElement::from_msg_hash(&zk_argument.get_bytes_for_challenge(&set, &comm_non_member, &comm_key));
            assert_eq!(challenge_by_prover, challenge_by_verifier);
            assert!(zk_argument.verify(&challenge_by_verifier, &set, &comm_non_member, &comm_key));

            let verifier_time = start_verifier.elapsed();

            let start_verifier = Instant::now();

            // Construct a polynomial with roots as the elements of the set. The polynomial can be constructed
            // once for both `get_bytes_for_challenge_with_poly_constructed` and `verify_with_poly_constructed`
            let poly = construct_polynomial_for_set(&set);
            let challenge_by_verifier = FieldElement::from_msg_hash(&zk_argument.get_bytes_for_challenge_with_poly_constructed(&poly, &comm_non_member, &comm_key));

            assert_eq!(challenge_by_prover, challenge_by_verifier);
            assert!(zk_argument.verify_with_poly_constructed(&challenge_by_verifier, &poly, &comm_non_member, &comm_key));

            let verifier_time_with_poly_construction_once = start_verifier.elapsed();

            println!("For set size {}, proving time is {:?}, naive verification time is {:?}, verification time with polynomial computed only once is {:?}", set_size, prover_time, verifier_time, verifier_time_with_poly_construction_once);
        }
    }
}