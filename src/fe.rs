use bellman::{Circuit, ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::{boolean, ecc, num};
use sapling_crypto::jubjub::{
    edwards, FixedGenerators, JubjubEngine, PrimeOrder,
};

pub struct DLSnark<'a, E: JubjubEngine> {
    pub params: &'a E::Params,
    pub x: Option<E::Fs>,
    pub r: Option<E::Fs>,
    pub pub_key: Option<edwards::Point<E, PrimeOrder>>,
    pub enc_rand: Option<edwards::Point<E, PrimeOrder>>,
    pub enc: Option<edwards::Point<E, PrimeOrder>>,
}

impl<'a, E: JubjubEngine + 'a> Clone for DLSnark<'a, E> {
    fn clone(&self) -> Self {
        DLSnark {
            params: self.params,
            x: self.x.clone(),
            r: self.r.clone(),
            pub_key: self.pub_key.clone(),   // sG
            enc_rand: self.enc_rand.clone(), // rG
            enc: self.enc.clone(),           // xG + r(sG)
        }
    }
}

impl<'a, E: JubjubEngine> Circuit<E> for DLSnark<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let c_r = boolean::field_into_boolean_vec_le(
            cs.namespace(|| "private key"),
            self.r,
        )?;

        let c_x = boolean::field_into_boolean_vec_le(
            cs.namespace(|| "message x"),
            self.x,
        )?;

        let c_enc_rand_calculated = ecc::fixed_base_multiplication(
            cs.namespace(|| "calculated enc rand"),
            FixedGenerators::ValueCommitmentValue,
            &c_r,
            self.params,
        )?;

        let c_xg_calculated = ecc::fixed_base_multiplication(
            cs.namespace(|| "calculated xG"),
            FixedGenerators::ValueCommitmentValue,
            &c_x,
            self.params,
        )?;

        let c_pub_key = ecc::EdwardsPoint::witness(
            cs.namespace(|| "pub key"),
            self.pub_key.clone(),
            self.params,
        )
        .unwrap();

        let c_enc_rand_claimed = ecc::EdwardsPoint::witness(
            cs.namespace(|| "claimed public enc rand"),
            self.enc_rand,
            self.params,
        )?;
        c_enc_rand_claimed
            .inputize(cs.namespace(|| "public input enc rand"))?;

        let c_rsg = c_pub_key
            .mul(cs.namespace(|| "scalar mul r(sG)"), &c_r, self.params)
            .unwrap();

        let c_enc_calculated = c_xg_calculated
            .add(cs.namespace(|| "addition xG + r(sG)"), &c_rsg, self.params)
            .unwrap();

        let c_enc_claimed = ecc::EdwardsPoint::witness(
            cs.namespace(|| "claimed public enc"),
            self.enc,
            self.params,
        )?;
        c_enc_claimed.inputize(cs.namespace(|| "public input enc"))?;

        let x_eq = num::AllocatedNum::equals(
            cs.namespace(|| "compare x coord of enc rand"),
            c_enc_rand_claimed.get_x(),
            c_enc_rand_calculated.get_x(),
        )?;
        let y_eq = num::AllocatedNum::equals(
            cs.namespace(|| "compare y coord of enc rand"),
            c_enc_rand_claimed.get_y(),
            c_enc_rand_calculated.get_y(),
        )?;
        let xy_eq = boolean::Boolean::and(
            cs.namespace(|| "compress bools"),
            &x_eq,
            &y_eq,
        )?;
        boolean::Boolean::enforce_equal(
            cs.namespace(|| "last check"),
            &xy_eq,
            &boolean::Boolean::constant(true),
        )?;

        let x1_eq = num::AllocatedNum::equals(
            cs.namespace(|| "compare x coord of enc"),
            c_enc_claimed.get_x(),
            c_enc_calculated.get_x(),
        )?;
        let y1_eq = num::AllocatedNum::equals(
            cs.namespace(|| "compare y coord of enc"),
            c_enc_claimed.get_y(),
            c_enc_calculated.get_y(),
        )?;
        let xy1_eq = boolean::Boolean::and(
            cs.namespace(|| "compress bools 1"),
            &x1_eq,
            &y1_eq,
        )?;
        boolean::Boolean::enforce_equal(
            cs.namespace(|| "last check 1"),
            &xy1_eq,
            &boolean::Boolean::constant(true),
        )?;
        Ok(())
    }
}

#[test]
fn test_fe_circuit_bls12() {
    use bellman::groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key,
        verify_proof,
    };
    use bellman::pairing::bls12_381::Bls12;
    use rand::{Rand, SeedableRng, XorShiftRng};
    use sapling_crypto::circuit::test::TestConstraintSystem;
    use sapling_crypto::jubjub::{
        fs::Fs, FixedGenerators, JubjubBls12, JubjubParams,
    };

    let curve_params = &JubjubBls12::new();
    let mut rng = XorShiftRng::from_seed([
        0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654,
    ]);

    let (public_inputs, circuit) = {
        let x = Fs::rand(&mut rng);
        // pub_key should come from outside, s is secret
        let s = Fs::rand(&mut rng);
        let r = Fs::rand(&mut rng);
        let generator =
            curve_params.generator(FixedGenerators::ValueCommitmentValue);
        let pub_key = generator.mul(s, curve_params);
        let enc_rand = generator.mul(r, curve_params);

        let xg = generator.mul(x, curve_params);
        let rsg = pub_key.mul(r, curve_params);

        // xG + r(sG):
        let enc = xg.add(&rsg, curve_params);

        let instance = DLSnark::<Bls12> {
            params: curve_params,
            x: Some(x.clone()),
            r: Some(r.clone()),
            pub_key: Some(pub_key.clone()),
            enc_rand: Some(enc_rand.clone()),
            enc: Some(enc.clone()),
        };
        let (x, y) = enc_rand.into_xy();
        let (x1, y1) = enc.into_xy();
        (vec![x, y, x1, y1], instance)
    };

    {
        let mut cs = TestConstraintSystem::<Bls12>::new();
        let circuit = circuit.clone();

        circuit.synthesize(&mut cs).expect("to be synthesized");
        assert!(cs.find_unconstrained() == "");

        let unsatisfied = cs.which_is_unsatisfied();
        if unsatisfied.is_some() {
            panic!("{}", unsatisfied.unwrap());
        }
    };

    let circuit_parameters = {
        let empty_circuit = DLSnark::<Bls12> {
            params: curve_params,
            x: None,
            r: None,
            pub_key: None,
            enc_rand: None,
            enc: None,
        };
        generate_random_parameters(empty_circuit, &mut rng).unwrap()
    };

    let verifing_key = prepare_verifying_key(&circuit_parameters.vk);

    let proof =
        create_random_proof(circuit, &circuit_parameters, &mut rng).unwrap();

    let is_valid = verify_proof(&verifing_key, &proof, &public_inputs).unwrap();
    assert!(is_valid);
}
