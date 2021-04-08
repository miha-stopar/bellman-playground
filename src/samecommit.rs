use bignat::hash::circuit::CircuitHasher;
use bignat::hash::Hasher;
use sapling_crypto::bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use sapling_crypto::bellman::{
    Circuit, ConstraintSystem, SynthesisError, Variable,
};
use sapling_crypto::circuit::{boolean, ecc, num, Assignment};
use sapling_crypto::jubjub::{
    edwards, FixedGenerators, JubjubEngine, JubjubParams, PrimeOrder,
};

pub struct SameCommitSnark<E, H1, H2>
where
    E: JubjubEngine,
    H1: Hasher,
    H2: Hasher,
{
    pub preimage: Option<E::Fr>,
    pub hash1: Option<E::Fr>,
    pub hash2: Option<E::Fr>,
    pub hasher1: H1,
    pub hasher2: H2,
}

impl<E, H1, H2> Circuit<E> for SameCommitSnark<E, H1, H2>
where
    E: JubjubEngine,
    H1: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    H2: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let preimage =
            num::AllocatedNum::alloc(cs.namespace(|| "preimage"), || {
                let value = self.preimage;
                Ok(*value.get()?)
            })?;
        let hash1 = num::AllocatedNum::alloc(cs.namespace(|| "hash"), || {
            let value = self.hash1;
            Ok(*value.get()?)
        })?;
        hash1.inputize(cs.namespace(|| "hash1 input"))?;
        let preimage_clone = preimage.clone();
        let calculated1 = self
            .hasher1
            .allocate_hash(cs.namespace(|| "inputs 1"), &[preimage])?;
        cs.enforce(
            || "add constraint between input and pedersen hash output",
            |lc| lc + calculated1.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + hash1.get_variable(),
        );

        let hash2 = num::AllocatedNum::alloc(cs.namespace(|| "hash"), || {
            let value = self.hash2;
            Ok(*value.get()?)
        })?;
        hash2.inputize(cs.namespace(|| "hash2 input"))?;
        let calculated2 = self
            .hasher2
            .allocate_hash(cs.namespace(|| "inputs 2"), &[preimage_clone])?;
        cs.enforce(
            || "add constraint between input and pedersen hash output",
            |lc| lc + calculated2.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + hash2.get_variable(),
        );
        Ok(())
    }
}

#[test]
fn test_samecommit_snark_bls12() {
    use bignat::hash::hashes::Pedersen;
    use bignat::hash::hashes::Sha256;
    use rand::{Rand, SeedableRng, XorShiftRng};
    use sapling_crypto::bellman::groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key,
        verify_proof,
    };
    use sapling_crypto::bellman::pairing::bls12_381::{Bls12, Fr};
    use sapling_crypto::circuit::test::TestConstraintSystem;
    use sapling_crypto::jubjub::JubjubBls12;
    let mut rng = XorShiftRng::from_seed([
        0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654,
    ]);
    let hasher1 = Sha256::<Bls12>::default();
    let hasher2 = Pedersen::<Bls12>::default();
    let (public_inputs, circuit) = {
        let secret = Fr::rand(&mut rng);
        let output1 = hasher1.hash(&[secret]);
        let output2 = hasher2.hash(&[secret]);
        let instance = SameCommitSnark::<Bls12, Sha256<Bls12>, Pedersen<Bls12>> {
            preimage: Some(secret.clone()),
            hash1: Some(output1.clone()),
            hash2: Some(output2.clone()),
            hasher1: hasher1.clone(),
            hasher2: hasher2.clone(),
        };
        (vec![output1.clone(), output2.clone()], instance)
    };

    let circuit_parameters = {
        let empty_circuit =
            SameCommitSnark::<Bls12, Sha256<Bls12>, Pedersen<Bls12>> {
                preimage: None,
                hash1: None,
                hash2: None,
                hasher1: hasher1.clone(),
                hasher2: hasher2.clone(),
            };
        generate_random_parameters(empty_circuit, &mut rng).unwrap()
    };

    let verifing_key = prepare_verifying_key(&circuit_parameters.vk);

    let proof =
        create_random_proof(circuit, &circuit_parameters, &mut rng).unwrap();

    let is_valid = verify_proof(&verifing_key, &proof, &public_inputs).unwrap();
    assert!(is_valid);
}
