//! Embedding field for the MNT4-753, a degree 4 extension of Fq.
//!
//! Constructed as degree 2 extension of the base field Fq2 of the quadratic
//! twist.
//! Contrary to the definition of `NONRESIDUE` below, this extension is achieved
//! by adding a square root Y of X in Fq2, see the comments in the Fp4 model.

use crate::field_new;
use crate::{
    biginteger::BigInteger768 as BigInteger,
    fields::{
        fp4::{Fp4, Fp4Parameters},
        mnt4753::{
            fq::Fq,
            fq2::{Fq2, Fq2Parameters},
        },
    },
};

pub type Fq4 = Fp4<Fq4Parameters>;

pub struct Fq4Parameters;

impl Fp4Parameters for Fq4Parameters {
    type Fp2Params = Fq2Parameters;

    /// NONRESIDUE = (8,1)
    /// however, it does no harm as the arithmetics of fp4 does not rely on it
    const NONRESIDUE: Fq2 = field_new!(Fq2,
        field_new!(Fq, BigInteger([
            587330122779359758,
            14352661462510473462,
            17802452401246596498,
            18018663494943049411,
            17948754733747257098,
            10253180574146027531,
            6683223122694781837,
            13573468617269213174,
            5059368039312883748,
            950479668716233863,
            9936591501985804621,
            88719447132658
        ])),

        field_new!(Fq, BigInteger([
            11000302312691101506,
            10506108233708684934,
            10935835699472258862,
            8743905913029047809,
            17088517996127229807,
            2166035204362411368,
            3606323059104122201,
            6452324570546309730,
            4644558993695221281,
            1127165286758606988,
            10756108507984535957,
            135547536859714
        ]))
    );
    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP4_C1: [Fq; 4] = [

        // NONRESIDUE^((q^0 - 1)/4)
        field_new!(Fq, BigInteger([
            11000302312691101506,
            10506108233708684934,
            10935835699472258862,
            8743905913029047809,
            17088517996127229807,
            2166035204362411368,
            3606323059104122201,
            6452324570546309730,
            4644558993695221281,
            1127165286758606988,
            10756108507984535957,
            135547536859714,
        ])),

        // NONRESIDUE^((q^1 - 1)/4)
        field_new!(Fq, BigInteger([
            2732208433323581659,
            2172983777736624684,
            14351170316343013496,
            6345300643186282385,
            3197292113538174065,
            1887663496013421009,
            16627860175048929982,
            1842296636815120666,
            13463717484107308085,
            721000253033730237,
            1214767992212094798,
            163570781165682,
        ])),

        // NONRESIDUE^((q^2 - 1)/4)
        field_new!(Fq, BigInteger([
            14260497802974073023,
            5895249896161266456,
            14682908860938702530,
            17222385991615618722,
            14621060510943733448,
            10594887362868996148,
            7477357615964975684,
            12570239403004322603,
            2180620924574446161,
            12129628062772479841,
            8853285699251153944,
            362282887012814,
        ])),

        // NONRESIDUE^((q^3 - 1)/4)
        field_new!(Fq, BigInteger([
            4081847608632041254,
            14228374352133326707,
            11267574244067947896,
            1174247187748832530,
            10065542319823237575,
            10873259071217986508,
            12902564573729719519,
            17180267336735511666,
            11808206507871910973,
            12535793096497356591,
            18394626215023595103,
            334259642706846
        ])),
    ];
}