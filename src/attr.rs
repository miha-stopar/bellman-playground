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

pub struct AttrSnark<E, H>
where
    E: JubjubEngine,
    H: Hasher,
{
    pub attrs: Vec<Option<E::Fr>>,
    pub attr1: Option<E::Fr>,
    pub hash: Option<E::Fr>,
    pub hasher: H,
}

impl<E, H> Circuit<E> for AttrSnark<E, H>
where
    E: JubjubEngine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let attr1 = num::AllocatedNum::alloc(cs.namespace(|| "attr1"), || {
            let value = self.attrs[0];
            Ok(*value.get()?)
        })?;
        let attr2 = num::AllocatedNum::alloc(cs.namespace(|| "attr2"), || {
            let value = self.attrs[1];
            Ok(*value.get()?)
        })?;

        let a1 = num::AllocatedNum::alloc(cs.namespace(|| "a1"), || {
            let value = self.attr1;
            Ok(*value.get()?)
        })?;
        a1.inputize(cs.namespace(|| "a1 input"))?;
        cs.enforce(
            || "attr ...",
            |lc| lc + attr1.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + a1.get_variable(),
        );

        let hash = num::AllocatedNum::alloc(cs.namespace(|| "hash"), || {
            let value = self.hash;
            Ok(*value.get()?)
        })?;
        hash.inputize(cs.namespace(|| "hash input"))?;
        let calculated = self
            .hasher
            .allocate_hash(cs.namespace(|| "inputs"), &[attr1, attr2])?;
        cs.enforce(
            || "add constraint between input and pedersen hash output",
            |lc| lc + calculated.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + hash.get_variable(),
        );

        Ok(())
    }
}

#[test]
fn test_attr_snark_bls12_poseidon() {
    use bignat::hash::hashes::Poseidon;
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
    let hasher = Poseidon::<Bls12>::default();

    let attr1 = Fr::rand(&mut rng);
    let attr2 = Fr::rand(&mut rng);
    let mut attrsv = Vec::new();
    attrsv.push(Some(attr1));
    attrsv.push(Some(attr2));
    let output = hasher.hash(&[attr1, attr2]);
    let circuit = AttrSnark::<Bls12, Poseidon<Bls12>> {
        // preimage: Some(secret.clone()),
        attrs: attrsv,
        attr1: Some(attr1),
        hash: Some(output.clone()),
        hasher: hasher.clone(),
    };

    let public_inputs = vec![attr1.clone(), output.clone()];

    let circuit_parameters = {
        let attrsv = Vec::new();
        let empty_circuit = AttrSnark::<Bls12, Poseidon<Bls12>> {
            attrs: attrsv,
            attr1: None,
            hash: None,
            hasher: hasher.clone(),
        };
        generate_random_parameters(empty_circuit, &mut rng).unwrap()
    };

    let verifing_key = prepare_verifying_key(&circuit_parameters.vk);

    let proof =
        create_random_proof(circuit, &circuit_parameters, &mut rng).unwrap();

    let is_valid = verify_proof(&verifing_key, &proof, &public_inputs).unwrap();
    assert!(is_valid);
}
