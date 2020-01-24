# [Zero-Knowledge Argument for Polynomial Evaluation with Application to Blacklists](http://www0.cs.ucl.ac.uk/staff/J.Groth/PolynomialZK.pdf)

Special honest verifier zero-knowledge argument of knowledge for two committed values u, v satisfying P(u) = v for a given 
polynomial P(X) of degree D. Is a 3-move sigma protocol and has logarithmic communication complexity. The polynomial evaluation argument is then used to 
prove set membership and non-membership by encoding the set as a polynomial. The degree of the resulting polynomial is equal 
to the cardinality of the set.

## API
1. To initialize a polynomial evaluation argument, use `UnivarPolyEvalArgProtocol::init`. After receiving/computing the challenge, 
use `UnivarPolyEvalArgProtocol::respond` to generate the argument. The verifier will then use `UnivarPolyEvalArg::verify` 
to verify the argument. Look at test `test_prove_evaluation`
    ```rust
    let comm_key = CommitmentKey::new("test".as_bytes());
   
    let poly = UnivarPolynomial::random(degree);
    let u = FieldElement::random();
    let v = poly.eval(&u);
    let protocol = UnivarPolyEvalArgProtocol::init(&poly, u, v, &comm_key);
    
    let challenge_by_prover = FieldElement::from_msg_hash(&protocol.get_bytes_for_challenge(&poly, &comm_key));
    let zk_argument = protocol.respond(&challenge_by_prover);
    
    let challenge_by_verifier = FieldElement::from_msg_hash(&zk_argument.get_bytes_for_challenge(&poly, &c_0, &c_v, &comm_key));
    assert!(zk_argument.verify(&challenge_by_verifier, &poly, &c_0, &c_v, &comm_key));
    ``` 

1. To initialize a set membership argument, follow similar steps as the polynomial evaluation argument and use `SetMembershipProtocol::init`. 
After receiving/computing the challenge, use `SetMembershipProtocol::respond` to generate the argument. The verifier will 
then use `SetMembershipProtocol::verify` to verify the argument. Look at test `test_prove_set_membership`
    ```rust
        let comm_key = CommitmentKey::new("test".as_bytes());
       
        let set: Vec<FieldElement> = FieldElementVector::random(set_size).into();
        // member is a member of the set, comm_member is the commitment to the member with blinding blinding_member 
        let protocol = SetMembershipProtocol::init(&set, member, blinding_member, comm_member, &comm_key);
                    
        let challenge_by_prover = FieldElement::from_msg_hash(&protocol.get_bytes_for_challenge(&comm_key));
        let zk_argument = protocol.respond(&challenge_by_prover);
        
        let challenge_by_verifier = FieldElement::from_msg_hash(&zk_argument.get_bytes_for_challenge(&set, &comm_member, &comm_key));
        assert!(zk_argument.verify(&challenge_by_verifier, &set, &comm_member, &comm_key));
    ``` 

1. Proving non membership has a similar API as membership using `SetNonMembershipProtocol`. Look at test `test_prove_set_non_membership`

The tests print timing info. Run with `cargo test --release -- --nocapture`

## TODO:
1. More documentation
1. Tests for failure cases
1. Handle arbitrary degree
1. Address various TODOs for optimization
1. Convert asserts to errors
1. Abstract the commitment group such that the argument can be used for commitments in group G2 