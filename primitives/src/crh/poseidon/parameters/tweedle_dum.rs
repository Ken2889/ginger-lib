use crate::crh::{
    PoseidonParameters,
    FieldBasedHashParameters, PoseidonHash, batched_crh::PoseidonBatchHash,
    PoseidonQuinticSBox, PoseidonSponge
};
use algebra::fields::tweedle::Fq as TweedleFq;

use algebra::biginteger::BigInteger256 as BigInteger;
use algebra::field_new;

#[derive(Clone)]
// x^5-POSEIDON-128 parameters for scalar field of the Tweedle Dum (=the Tweedle Dee Fq ).
// 
// The number of rounds are computed by ./evidence/calc_round_numbers.py, round constants and matrix 
// are generated using the script ./evidence/generate_parameters_grain.
pub struct TweedleFqPoseidonParameters;

impl FieldBasedHashParameters for TweedleFqPoseidonParameters {
    type Fr = TweedleFq;
    const R:usize = 2;  // The rate of the hash function
}

impl PoseidonParameters for TweedleFqPoseidonParameters {

    const T:usize = 3;  // Size of the internal state (in field elements)
    const R_F:i32 = 4;  // Half number of full rounds (the R_f in the paper)
    const R_P:i32 = 56; // Number of partial rounds

    // The zero element of the field
    const ZERO:TweedleFq = field_new!(TweedleFq, BigInteger([0x0, 0x0, 0x0, 0x0]));


    // State vector after permutation of zero state vector (Montgomery representation)
    const AFTER_ZERO_PERM: &'static [TweedleFq] = &[
        TweedleFq::new(BigInteger([0x46ef7b471f039f54,0x7516283cc67869f2,0x561a6334ba7a39f1,0x293842a1538ac01b,])),
        TweedleFq::new(BigInteger([0x6f10ff3b97995e3b,0x7650f70901d51a88,0x9f13555ea4caf2eb,0x14ed7f5560a0a1e1,])),
        TweedleFq::new(BigInteger([0x815126351fe00f44,0x921a5f3ad5a6e83c,0x5f614c0b1bdaf5f7,0x7733c69a8892f0e,])),
    ];

    // Array of round constants
    const ROUND_CST: &'static[TweedleFq]  = &[
        // Constants in Montgomery representation. 
        field_new!(TweedleFq,BigInteger([0xd06520c09450cbc9,0xcf4444f399d4b067,0xed3cdecf2c2ad3cf,0x2a922c6f74bce817,])),
        field_new!(TweedleFq,BigInteger([0x60bde2740b39213d,0xba122180e7af3753,0x40090228e9cc5a42,0x177c72bbace07027,])),
        field_new!(TweedleFq,BigInteger([0x5ebd43b701d85141,0x5ef573127baabe65,0xa2d0ea9e7ce5b31a,0x137d99e551df3b8c,])),
        field_new!(TweedleFq,BigInteger([0x3b8cb91b343e1f20,0x331bd86e427016ce,0xa4840e40ad9803f4,0x394532179f75f4e9,])),
        field_new!(TweedleFq,BigInteger([0x1ec59497ae56b237,0x8ecb653b831ff765,0x481804c446de69d6,0x29589666c81a56c0,])),
        field_new!(TweedleFq,BigInteger([0xad127e17f428be96,0xe2c5762dce6fe30e,0xc4d71e24928723f9,0x221845f927a179e9,])),
        field_new!(TweedleFq,BigInteger([0x44271158d30f729f,0xb406e2965f4375c4,0x4375f933a3a34235,0x57365228fa6b986,])),
        field_new!(TweedleFq,BigInteger([0xcc9f09612486f55d,0x2ffd2a714c682c93,0xb5ed16b39623a446,0x263d2157ccacb99a,])),
        field_new!(TweedleFq,BigInteger([0x9e0bd6388f96fdd8,0xf4929cda447d1ce5,0x6b19d7b86355bac9,0x2619b62891a9d045,])),
        field_new!(TweedleFq,BigInteger([0x9b5fb0992b601a32,0xbd510112e9cf6070,0x67d04ffc1ea9d28f,0x1ca921e9af729fa9,])),
        field_new!(TweedleFq,BigInteger([0x560e6fd9725a0309,0x6cf6d3c57b84652f,0x62aaf714fad16095,0xa7aa6c278e231ed,])),
        field_new!(TweedleFq,BigInteger([0xa28bd230465173d8,0x3bc04513e6ce1021,0x214c1c122428f2e7,0x3165e00d7a5dd413,])),
        field_new!(TweedleFq,BigInteger([0x4cecdb283a5a69db,0x9521b4517de78f68,0xa8bb82a76b3eed88,0x231cd67b00b98aa2,])),
        field_new!(TweedleFq,BigInteger([0x8e77be72728462c2,0xc52aa77caf405120,0x14a07963ad5d358e,0x102aa22546b7d719,])),
        field_new!(TweedleFq,BigInteger([0x5b68c4bb0f9d5e5,0xc74945e354355556,0x6b7d9835abe4d632,0xd238d491116c462,])),
        field_new!(TweedleFq,BigInteger([0xa3887726bbe187e8,0x7864f962bc5df66f,0x7241b616fe237fdf,0x2c7302787042fefc,])),
        field_new!(TweedleFq,BigInteger([0xaa60569d6e50c258,0x1a44fb8b57610147,0x59d036dce864e680,0x20ac6feef3b08be4,])),
        field_new!(TweedleFq,BigInteger([0x8f272b18b5a21f7b,0xeff039bd961c59c0,0x7646e69e44f7067a,0x37e219036dc9d3d9,])),
        field_new!(TweedleFq,BigInteger([0xe25ce8aba319b6be,0x4be8b7875763a64b,0xe187c96ddb272453,0x1d2e584b7a041675,])),
        field_new!(TweedleFq,BigInteger([0xebabf749daf0d178,0xcaba4fe3d5bea6d9,0x1fee8dbf56bd1f8c,0x2c1d40320004af3e,])),
        field_new!(TweedleFq,BigInteger([0x168887748abaecb8,0x5e6ff7fca8e44137,0x8873401c63b97f39,0x13af33d3f2377c1,])),
        field_new!(TweedleFq,BigInteger([0x39c4beab8e437f52,0x6559c1909c79549f,0x596137029e44e4eb,0x152533e4bf376143,])),
        field_new!(TweedleFq,BigInteger([0x152961fd5bda963e,0xf544a973034a0d84,0x2c63bb6abb3496ef,0xf41b4dc92158ecf,])),
        field_new!(TweedleFq,BigInteger([0xbb2a82becc608b67,0x13227f8aad64efa9,0x9f74aaf9c5fb9327,0x13c82e3b22c41d6a,])),
        field_new!(TweedleFq,BigInteger([0x4dce4021efdd1280,0x52b76e0989f74799,0x4a776ae91aaa507e,0xceace17b7b7a764,])),
        field_new!(TweedleFq,BigInteger([0xc5b13e5ddf7b56dd,0x5dc878e444e6e6f1,0xc49444149accf9b6,0xa64b772af5d8572,])),
        field_new!(TweedleFq,BigInteger([0xa93427ccd919b65d,0xd8a9bb882d024ef7,0x8d958861fc922d93,0x267dfa69a8ef550d,])),
        field_new!(TweedleFq,BigInteger([0x8f7b037f277a6f8b,0x1e4da49ecad22320,0xd283993f470ca915,0x134914b4f3ba4d90,])),
        field_new!(TweedleFq,BigInteger([0x7ec3247567085f75,0xe30f7d76f181b151,0x25284eed3e384a08,0x176f66b52c0b46fa,])),
        field_new!(TweedleFq,BigInteger([0x2142adb9b1341668,0x591d0777c42566cc,0x6305acc460e4ac20,0x3458b9cb48eaaa92,])),
        field_new!(TweedleFq,BigInteger([0xd70bd8df51d0bdcf,0xeaf18757227db4e3,0x402420db973d9abc,0x36e078236490d83,])),
        field_new!(TweedleFq,BigInteger([0xa9d0af02a7975e25,0x775418692bdc072a,0x4c298c4ac7ef4d7e,0x1d9b69654b092496,])),
        field_new!(TweedleFq,BigInteger([0xf5c57af0cb60207c,0xfb68232f1b658a36,0xca25a272d5cddc,0x1963116a927059e4,])),
        field_new!(TweedleFq,BigInteger([0x49c23fd1c153a321,0x9d46ecb476087ea9,0x22ec5f03909ec1cf,0x1675657f03cc5429,])),
        field_new!(TweedleFq,BigInteger([0x8b52631a8d0ef397,0x7aacb3eaf1a08300,0x6b16ddddc870d480,0x277fbd29939286ef,])),
        field_new!(TweedleFq,BigInteger([0x62e3a2f5aa1af950,0xe18d6a90ba48b83b,0x208ee3982fa0c318,0x3ebaf313e212d0b2,])),
        field_new!(TweedleFq,BigInteger([0xf0c8a432f5df17af,0x13706b0503c3f2fa,0xe71a6613bf1b48f7,0x1ac0630ec731f387,])),
        field_new!(TweedleFq,BigInteger([0x9f92c6e38ff496a1,0x6f2b45d0e9f3f47b,0xe5b2fdb9402a5c55,0x251cbcf87cbf779c,])),
        field_new!(TweedleFq,BigInteger([0x7f98d620d8605a53,0x22ee5bdb61a35e31,0x385a4034e6608dce,0x1355ab32c6fc7e32,])),
        field_new!(TweedleFq,BigInteger([0xea4b91b36a316c16,0xabbd60800c7d2fec,0xb18a56b4d6b7f110,0x23bdf09f30cde6e9,])),
        field_new!(TweedleFq,BigInteger([0xdc92f469c4e0993a,0xe27c4a1eb3bdb3ef,0xc456c9c418efafca,0x3414d3678bfd22b0,])),
        field_new!(TweedleFq,BigInteger([0xe28e6e3b448c37a8,0x92a2cc8999ea5357,0xa52fdf68d625769,0x15845caaf5801b79,])),
        field_new!(TweedleFq,BigInteger([0x2acb2a5f60478d13,0x7be04faeb4726db8,0x241039d5336a1818,0x7b37d5b9c5ac89d,])),
        field_new!(TweedleFq,BigInteger([0xfdffe38f8f533391,0x3b555532c0629b3f,0x8d5c25204cd29ee6,0x8d6b43544d677a3,])),
        field_new!(TweedleFq,BigInteger([0x622977857648fe76,0xab82905055e2835f,0x6de310a09c5e8ecd,0x119b72b411823820,])),
        field_new!(TweedleFq,BigInteger([0x9540cf3e69c4cf64,0x78fa112a4d3c083f,0xd40cdb21b368fd97,0x187ab4574a382fb,])),
        field_new!(TweedleFq,BigInteger([0xf70d118aa8dd0391,0xed5a78d9fd07ce64,0x25004cbb7c17784c,0x1d7ddcca9f892ba6,])),
        field_new!(TweedleFq,BigInteger([0xed8b92c25cd6990c,0x5a4f8f6165037502,0xfa51afe6a59322ef,0x7bad5e6ab209a5b,])),
        field_new!(TweedleFq,BigInteger([0xaf8b68cbcd165cd2,0xd9af037799bb5016,0x4252fde7f1b8deb5,0x18276cf868cda059,])),
        field_new!(TweedleFq,BigInteger([0x473770910ad44d20,0xf6f11a221c2b76a4,0xaf7ea8799372fb02,0xb922b4baa02fe4a,])),
        field_new!(TweedleFq,BigInteger([0x4bcb851aed6af574,0xac0400295712babb,0xe137d528d9afdc77,0x51b55216f3b3e93,])),
        field_new!(TweedleFq,BigInteger([0xf4ea5fa58f6cd6d,0xc3178acb7474c919,0x1a78bc8d9509399e,0x3db8037d9c38ff34,])),
        field_new!(TweedleFq,BigInteger([0x3c6c749ed14eba46,0x344bdf3052afb8d9,0xf3977e67a9ebf8bb,0x16df4d7e98c80bf6,])),
        field_new!(TweedleFq,BigInteger([0x7baf3f8824575a0,0xcde0f99b13c6e28,0x548747dea88e6079,0xaee01ab05c6dea4,])),
        field_new!(TweedleFq,BigInteger([0x7e061d9435def279,0xf3a24b07424e6ae,0x2100c0d0934960d3,0x1f3b1dcad7f56f8a,])),
        field_new!(TweedleFq,BigInteger([0x655452f15d0764c3,0x909466bbdc1ba576,0x62174b4f659b8c35,0x3f6f0c7888ec2fa1,])),
        field_new!(TweedleFq,BigInteger([0xa855b2cd69a4eb1f,0x29460295f793ad00,0x604d356e35d54832,0xd13d12b349693db,])),
        field_new!(TweedleFq,BigInteger([0x32333b51dd9aaa45,0x32e806b7150aa1e,0xc8abc5e9050d23f7,0x1344a43160574a6,])),
        field_new!(TweedleFq,BigInteger([0x97a9e3cf1825b286,0x5bbac70af2e88c38,0xe58a38a5639f7b32,0x2019ea88a902e9fc,])),
        field_new!(TweedleFq,BigInteger([0xf0a46acac474f69d,0x3a3a61e8b06db5f8,0xf1eaa93c477ae56e,0x2e42b0ae69081932,])),
        field_new!(TweedleFq,BigInteger([0xdb1ea311949b205b,0x21562d0ee469b95a,0x2c63f424bffbe637,0x3523c2ed61af226d,])),
        field_new!(TweedleFq,BigInteger([0x222dddb1e4672218,0x86041d7a33c374d1,0xe60299662516084c,0x2dbd4098256d08a8,])),
        field_new!(TweedleFq,BigInteger([0x6b8d0990380db1e2,0xdf3fc37d9964c8e,0xa3b6829c7c33b207,0x10280a8f1427bb50,])),
        field_new!(TweedleFq,BigInteger([0xf3d0b271a7080558,0x39161202da1ad393,0x760bcf59312828ca,0x13adf40dd6f38e57,])),
        field_new!(TweedleFq,BigInteger([0x974b96f23ff5810c,0x12764c15bbf0e1f,0xf2ef1a6b29656c55,0x1af98f964186f4e7,])),
        field_new!(TweedleFq,BigInteger([0x37e75583964de4dc,0xc56d3cff9c0c15a2,0x5ab38905add1989b,0x27f9202b19a8c1fc,])),
        field_new!(TweedleFq,BigInteger([0x4857f3c962a2a53d,0xa3b93bc71ecbae06,0x315133542bb793f2,0x3b1e0a0663ea9b42,])),
        field_new!(TweedleFq,BigInteger([0xaec4b261ff7474a5,0xe7a70488b002fbb5,0x344cf0f6ade03bf9,0x1499398f55ce277b,])),
        field_new!(TweedleFq,BigInteger([0x672c47ad3cb7d1d0,0xe0c18723e952133b,0xd3687190eb364496,0x2cc90a81db68a944,])),
        field_new!(TweedleFq,BigInteger([0x1c46b006e3195a07,0x27bb8d1ce9758971,0x48f1eb13322429bb,0x2b98bf75fdcf851e,])),
        field_new!(TweedleFq,BigInteger([0xb833c5e926e4c10,0x5611aa3077b80bd5,0xa7f6ff554ac0562d,0x1e000473b2d32d2,])),
        field_new!(TweedleFq,BigInteger([0x353b6a3ebce1ced6,0x13725e68b968f853,0xdc8f79d8f5dad13d,0x166624ef6c67a00a,])),
        field_new!(TweedleFq,BigInteger([0x38c4fbeb056345b6,0x11a02e57dd2f11e0,0xfede403f3374f85f,0x3eb7c21e913c5c35,])),
        field_new!(TweedleFq,BigInteger([0xdccae5e8386703b,0xb31a1ea50d2a7717,0x47d019bd99985fed,0x114fb255c324d577,])),
        field_new!(TweedleFq,BigInteger([0xee56bf8139a77a2e,0x98510872852a95e,0x6663e5c4f8bffda1,0x1b8bf2c55d150961,])),
        field_new!(TweedleFq,BigInteger([0x54088598ab82479e,0x7de6d0dd599868a6,0x64757056522a99a7,0x567d6d7e5214c67,])),
        field_new!(TweedleFq,BigInteger([0x90fbd2ab160a2077,0x56d8c1a682154058,0x8ea74449f95fd241,0x8d2decd7346979e,])),
        field_new!(TweedleFq,BigInteger([0x4c26cd2feaee9bb4,0x6eb27cf9baa6617b,0xc53f3a92480249b4,0x7955b221ccd2f2a,])),
        field_new!(TweedleFq,BigInteger([0x82d7e1e46119f4c9,0x94bc612484c75c05,0x913de5436beb861d,0x2f2585bb4972bee2,])),
        field_new!(TweedleFq,BigInteger([0xb279e5a794487fcd,0x8b24792325c36a79,0xa714537f6011940c,0xc8c2492b4879b99,])),
        field_new!(TweedleFq,BigInteger([0x63d57e521e8ae9a1,0xa1e752bac816b754,0xba29a03d2aa2fb57,0xdcf386abcb7cb8d,])),
        field_new!(TweedleFq,BigInteger([0x347c9986b49599f8,0x72f2ef2559ed4ec8,0x56264735a89c1ac4,0x99687949ceb4068,])),
        field_new!(TweedleFq,BigInteger([0x6ec1f7ff744a1735,0xb1e6de016c01c75b,0x78a8dbd5aa80dddd,0x38514a23bcc8f4b0,])),
        field_new!(TweedleFq,BigInteger([0x302dadeaf69adebd,0x5452b2650e6ca229,0x5500a3254c516a1b,0x2409c023148c951e,])),
        field_new!(TweedleFq,BigInteger([0x7dbec6915ec97f9b,0x943e2e5c6a356ff2,0x317efe07141b1ec5,0x324c1efdea46ce88,])),
        field_new!(TweedleFq,BigInteger([0xd0f50a6d462127b2,0x9446c3021a7bf53f,0x416c7f50add287f3,0x17b731a8aafc706e,])),
        field_new!(TweedleFq,BigInteger([0xc1eeba59730beccb,0xc24b94e34ed65702,0x28a4f7cca26c7953,0x257306c8c1d3af19,])),
        field_new!(TweedleFq,BigInteger([0xbc52b1d38df16d31,0x21a3c7ccf0d891,0xca545364eaeb6df3,0x2c88eebdc6af1ee,])),
        field_new!(TweedleFq,BigInteger([0xfcd67066cc2bb61,0xfe68b37e40e711ee,0xabda35ca0ddcc38,0x2ffc09d76b75e90f,])),
        field_new!(TweedleFq,BigInteger([0xa624fdad219fcb93,0x6460ef69d345c2f6,0x4dbc49f470f0a7e1,0x387961b68350aa51,])),
        field_new!(TweedleFq,BigInteger([0x43d6e7c05d9266d0,0xa5a163692450138b,0xf82a116a5afc87e8,0x3de40560ef761d40,])),
        field_new!(TweedleFq,BigInteger([0xd8d6ffc8eb6e6277,0xe8e18a799fc5126f,0xa9644a81e16b5b9c,0x3f993383a7c23972,])),
        field_new!(TweedleFq,BigInteger([0x3a0ac5eb4766ec7d,0x3198ff53b2adb167,0xf28ef94d26097a4c,0x2fbd3be0053d5a6,])),
        field_new!(TweedleFq,BigInteger([0xb49d8797431a0c9,0xba1c1410d56745f3,0x3b1065f2dd7c0ff2,0x2114b5e8751567c8,])),
        field_new!(TweedleFq,BigInteger([0x8bbde30b582dfe6,0x5b1e5d060df2e44b,0x1281cde698090095,0x2f464d231935fefa,])),
        field_new!(TweedleFq,BigInteger([0x2b791ee66481197a,0x6cd4f83218728e42,0x8fc1eea2ba579e57,0x3537f3b7c8b77cd9,])),
        field_new!(TweedleFq,BigInteger([0xe5e684314cb7d1f6,0x8f8773bd865a3e0d,0xd5457110a73e7a36,0x9e631f8f59385a3,])),
        field_new!(TweedleFq,BigInteger([0xc70d2c6c76351f37,0xeadeb120a3a288cd,0xfa45f33187d73e4b,0x34d19d6b2bb6891a,])),
        field_new!(TweedleFq,BigInteger([0x4c145703a0f65c5a,0x872a7b73d65ae391,0xc04a9502be8d11d3,0x382b732fd703049f,])),
        field_new!(TweedleFq,BigInteger([0x8bd255cd5c63b046,0xa73376ab63955f78,0xf596f19f3b322255,0x1b4022852b574238,])),
        field_new!(TweedleFq,BigInteger([0x2e9ffe0734efb324,0x328eb136d62f8075,0xc4775aaf9e3479db,0x318956d4778a2c4d,])),
        field_new!(TweedleFq,BigInteger([0x6580d026a737d4f9,0x79ff495e98bd481d,0xfe371e26ec7f82f3,0x35824fb613f62887,])),
        field_new!(TweedleFq,BigInteger([0x2b49570d9a864279,0x51bdc7586eeccec3,0x6e238aa8ca3b9266,0x35b9f3e72eb83a20,])),
        field_new!(TweedleFq,BigInteger([0x49a386f863fc31b0,0xf03b8c3fa990ad5b,0xa3032bca0ecf90d2,0x2ee469b7ba351d26,])),
        field_new!(TweedleFq,BigInteger([0x73e32f07f72a7583,0x351c5de9bb53ab35,0x645e44709c8c1321,0x3c321a08b1de4a7f,])),
        field_new!(TweedleFq,BigInteger([0x1b67e844c7db0975,0xce362d81642fbefd,0xfa7b8dc0a81a016f,0x126455549205b031,])),
        field_new!(TweedleFq,BigInteger([0x55e9a479f9c97e08,0x7816f197174e64c9,0x1ad279dd615311ce,0x2064e6cbb65804f0,])),
        field_new!(TweedleFq,BigInteger([0xce6cd4e3d4fce9a7,0xe822393f9ebf762f,0x59a2eddda1e5b1d5,0x2106feb2fe430571,])),
        field_new!(TweedleFq,BigInteger([0xa1ef764c23b78010,0x8e9e9642a952c712,0x83cb5bdfdfd6d5b7,0x1e6d5fc4bdd0ac79,])),
        field_new!(TweedleFq,BigInteger([0x336046e9c07665c3,0xde0c19de2b08125f,0x478f0e4b0f4f5d1e,0x237ed53601cd9347,])),
        field_new!(TweedleFq,BigInteger([0x45797d563e19873e,0x279f598657e17fd,0x3f11b7190e4bbcc5,0x1a5d4e4281453891,])),
        field_new!(TweedleFq,BigInteger([0x2f113e422ac0200c,0xa2911f8b511524c5,0x1dfabcd02b236da3,0x1228e490d474145d,])),
        field_new!(TweedleFq,BigInteger([0x44fcd6809d2f58b9,0x9c67df8aac844c77,0x23aa14ac3e8eaaed,0x3a38c40931533cd8,])),
        field_new!(TweedleFq,BigInteger([0x6f2ace017f84e43,0x82ca7f271c4ce0d4,0xe4455173b7d37f55,0x378c060065995c33,])),
        field_new!(TweedleFq,BigInteger([0x84122df7651efff4,0xa1262065add3756b,0x2870f402fbe4b098,0x85772dcd28b5f43,])),
        field_new!(TweedleFq,BigInteger([0x23ced22bd196effe,0xfabc1691caf72b64,0x2675bbff45185873,0x16827abbe8bf5c1a,])),
        field_new!(TweedleFq,BigInteger([0x78bf51313432c0c9,0xb45b87b5b331720,0x628226b161aa6f1c,0x147018c558346aeb,])),
        field_new!(TweedleFq,BigInteger([0xcb0dc3eed4a78c5d,0xe5d819a9da1e4d01,0xff5760a100c27dbd,0x1a0573012c72716a,])),
        field_new!(TweedleFq,BigInteger([0x8a64b2c2bcbf3965,0x71052e7d4cc7324b,0x7d72e3d1b7a2c673,0x12624be5b6dba8a7,])),
        field_new!(TweedleFq,BigInteger([0xc40f02933b05559d,0x2b0ac41d1064a05e,0xa2c93e3f43b0cce9,0x2bfb08a933a97133,])),
        field_new!(TweedleFq,BigInteger([0xe9cc32cea9ecd4e,0x64c96e64475949de,0x80959f26a7498cc3,0x3abf81aa0061f45e,])),
        field_new!(TweedleFq,BigInteger([0xb8b025060eef4267,0x5526fd662193d888,0xd51ef595dd0609bc,0x127e4687f8cee79a,])),
        field_new!(TweedleFq,BigInteger([0xd3c3a03feae61bda,0xe7ee363f94744c47,0x1cca28c045b2652d,0xe83f1ecbaaf15c3,])),
        field_new!(TweedleFq,BigInteger([0xb8dce07aae9fb29e,0xcc273bf01dddf4dd,0x9fbaa628af7d8990,0x1b02d39bbe351d22,])),
        field_new!(TweedleFq,BigInteger([0x20260191440c142e,0x3cc7bb9baeb18aca,0xebcd13882b77cf77,0x13fe5eead4e48752,])),
        field_new!(TweedleFq,BigInteger([0xe1ab2499382e60ab,0x768c97276ef2af71,0x4be0a137b500e491,0xd4735c4c884f86a,])),
        field_new!(TweedleFq,BigInteger([0x33877ec29306f25d,0x1b05f5fbf1c42533,0x64a9bec0fc89e32c,0x1a82259ca44cea68,])),
        field_new!(TweedleFq,BigInteger([0x95dcf75be6cfea9a,0x85d3423677c948cb,0xd9060847bc119750,0x1ac7532b644135ee,])),
        field_new!(TweedleFq,BigInteger([0x82faccfc948bc871,0x85e3a8ac48c9d96c,0x983fc71ec52b86d4,0x517e5205a9b73c9,])),
        field_new!(TweedleFq,BigInteger([0x2f749915c1b09e72,0x6fd8fdfe9f58582d,0xaada9b529cf03ff6,0x23a81033de4de7b0,])),
        field_new!(TweedleFq,BigInteger([0x376c83ee452272e,0x3e3fc0dbb30a0f78,0xecf7524be524ed25,0x3080a89317e433c7,])),
        field_new!(TweedleFq,BigInteger([0x30ee0f65f95d9409,0x7d6d3a6f89645231,0x178183d19706d785,0x26304249500b9fe1,])),
        field_new!(TweedleFq,BigInteger([0x9259f0791f526219,0xe53940a0a630a03a,0x29d3382a1fc137b6,0x3075f4ccf349baa4,])),
        field_new!(TweedleFq,BigInteger([0xb195e1cec008c269,0x9395fc394104e7d,0x86a76ac3cb3d9211,0x112b313fe0fd4110,])),
        field_new!(TweedleFq,BigInteger([0x35e2dec796f93e24,0x832bb9a48c157d3b,0x5d676a5936642407,0x1f1b0229254a5190,])),
        field_new!(TweedleFq,BigInteger([0x85586e4db0530b22,0x72fcde33fe4c8f,0xd2965b5ab52860cb,0x3a02938b8b0ef048,])),
        field_new!(TweedleFq,BigInteger([0x70ef952ad71afe4,0x75b1141ac27ea57,0x11a86faeaf6f4f6c,0x8b134fcf59d0a74,])),
        field_new!(TweedleFq,BigInteger([0x33d5cbea9812649d,0xf6d9a5ddc7eee06f,0x7a34d1a9a0ba83b0,0x309c21af5733505d,])),
        field_new!(TweedleFq,BigInteger([0x51bc324ea9aef8eb,0x1437004a299d1c64,0xd80781855426fe19,0x1d01df8b6551bd88,])),
        field_new!(TweedleFq,BigInteger([0x34140103e51a2232,0x1beacaba435204ff,0xf066911073342009,0x1c857e675ffff50e,])),
        field_new!(TweedleFq,BigInteger([0x5cb195a5a797436,0x29a185af45a71cbe,0x9fff4289eb38c32b,0x9d8670c9d9357fb,])),
        field_new!(TweedleFq,BigInteger([0xda8043acf95ed2f4,0x34c7e40853516c24,0x264e7e31dfe9eccc,0x9292a89d8766587,])),
        field_new!(TweedleFq,BigInteger([0x81080c771ce4e004,0xdfec5c0dd45e7da,0x6280878e6fc33f10,0xdf457da6ca530ef,])),
        field_new!(TweedleFq,BigInteger([0x1ab27ee1cabbf602,0xc0b363a5dd618d0e,0xea010da956e611b0,0x1eccbe1724454cb5,])),
        field_new!(TweedleFq,BigInteger([0x40e47d5653be560c,0xba93eeea04016d41,0x5ea05eb3d24bd272,0x30c6a7b21358c962,])),
        field_new!(TweedleFq,BigInteger([0xfb6f0008570bb08f,0x26111a979ba489b5,0xdc3c4f80422afc9b,0x14277969cedd9b93,])),
        field_new!(TweedleFq,BigInteger([0xec5f1716d9201408,0x14f2713b7733b2bb,0xa241b936abe355ad,0x512e1b932fe7699,])),
        field_new!(TweedleFq,BigInteger([0x3cd445aa3129ee6c,0x2690b0285247652c,0x66c718618dd9b107,0x183d9558881fe158,])),
        field_new!(TweedleFq,BigInteger([0x98701005d2aeae05,0x5219e22901202204,0x7acfbbc506eb7c11,0x4fc9e9026e21c2d,])),
        field_new!(TweedleFq,BigInteger([0x78d2380de1e458d0,0xe1ce04cb4bb74633,0xf9c4732072a62349,0x237234667744fee5,])),
        field_new!(TweedleFq,BigInteger([0x7f9dc29787eb031f,0x1f39fc6147476c6b,0xebdd8eaab42a7024,0x32f7561d6cfccbaf,])),
        field_new!(TweedleFq,BigInteger([0xd10a3f72235adf0,0x461e588f2a5f48a2,0xe5494be3a6c95ec4,0xcb33f596537242b,])),
        field_new!(TweedleFq,BigInteger([0x4fbcab519fcc6d57,0x9b81a91c4988c028,0xe28657e4039958ea,0x19b15cceba8b0483,])),
        field_new!(TweedleFq,BigInteger([0x61e1df6f33c06bf6,0x44b547593fb293b,0x8b780846db7d404e,0x2daae30726a68f6,])),
        field_new!(TweedleFq,BigInteger([0x11b2973c32b898d,0x340c0438b56cd0d3,0x821d2c15b8f34241,0x1d5437f9a47eeed3,])),
        field_new!(TweedleFq,BigInteger([0xcf0e6ea1da84213c,0xfac4e4304058fe36,0x151986f461f70125,0xfb7e4a58ca307f8,])),
        field_new!(TweedleFq,BigInteger([0x58d496e2096ab4c2,0xc676bff4f0011d33,0xb2ce66bf96b67181,0x13daf0071fae4fc3,])),
        field_new!(TweedleFq,BigInteger([0x9329204a6e3c1f1e,0xbd40c63c1ba7b888,0x6e18819ddc9733ef,0x3538899738f6d55a,])),
        field_new!(TweedleFq,BigInteger([0xf562f88a527d106f,0xbb9e9c9faa5d622,0x1111bf774e4eb0c1,0x20a5d0cb91f43e84,])),
        field_new!(TweedleFq,BigInteger([0xfc3160148d5fae9f,0xc1709b0a7776a1ce,0xe48ab968f709fede,0x745ac72c84bf4fd,])),
        field_new!(TweedleFq,BigInteger([0x81b565c10a4e043c,0x727804fd87b0bf19,0xe5d5abf0a1c3f365,0x338e5f28390f4754,])),
        field_new!(TweedleFq,BigInteger([0xb049493743a007fb,0xad40da98d3ef18a2,0x6909e583e26716de,0x14e1c7592b5ed097,])),
        field_new!(TweedleFq,BigInteger([0xf962ad243b775c10,0xa25ba5a903a96250,0xe0622b1e16f0dc50,0xff616b27de572b5,])),
        field_new!(TweedleFq,BigInteger([0xfc534d0353f33b41,0xdf10e5229db8ad41,0xaa0530bd095ee54b,0x2e67afa178595796,])),
        field_new!(TweedleFq,BigInteger([0x9f98afba65cff6a6,0x6fa75451d0763a2,0xb2a09f94da0ca724,0x1caa4d7d714d35c7,])),
        field_new!(TweedleFq,BigInteger([0x85786aa62b5916c3,0x9aa72049ff22b4ec,0xdea1c5fb69569640,0x37a23002f991bae2,])),
        field_new!(TweedleFq,BigInteger([0x7989abbeccad71d5,0xfcf81f66987b24c8,0x3dec6360a6330095,0x1810e3285fcf76d4,])),
        field_new!(TweedleFq,BigInteger([0x2ca0d21c1b00c2be,0xe10bacda19ca4dcd,0xd7ebeee67e78143,0x142716ce713fe09a,])),
        field_new!(TweedleFq,BigInteger([0x594affb623548671,0x6c20594401790915,0x9c5755f1d34936af,0x1b74ab0d83fee593,])),
        field_new!(TweedleFq,BigInteger([0x9e3ed1c1b092fee1,0xc317b27fa3319bc2,0x417a19eff88c039,0x346b91833576d143,])),
        field_new!(TweedleFq,BigInteger([0xb838b53580c4ff4a,0xd2b22f2e8813a33,0xda63b724dd4a8fe,0x1ce3f057b035eff3,])),
        field_new!(TweedleFq,BigInteger([0xc2921ca7c6745455,0x8a791dace9deac85,0x23d4cea43cb1af4f,0x178ec2ac99498fea,])),
        field_new!(TweedleFq,BigInteger([0x54ace3c36650034f,0x64fb9abdc2b3107e,0x895b5f9dd7db0bd2,0x32f5caf5fca100c4,])),
        field_new!(TweedleFq,BigInteger([0xa630e1dd6f53e70a,0x6435af7d6f3d7488,0x6964840f11899405,0x31e033fc232eec89,])),
        field_new!(TweedleFq,BigInteger([0x7a803b7f415df6c4,0x19a54556e1770d9f,0x44eece378ec7bfff,0x2186f08bacfa113,])),
        field_new!(TweedleFq,BigInteger([0x5cf8ab8f0d6088,0xc516dd5cb19de234,0xf8c4087f093cc96,0xa6acb79530d8e13,])),
        field_new!(TweedleFq,BigInteger([0xc61e5e028144670f,0xb0e6ebe550008399,0xe0a711e26f3807bc,0x257e2454f8b55cb9,])),
        field_new!(TweedleFq,BigInteger([0xe74e3836a27b1bb5,0xc4b2f2ee1f2517b4,0xc698101bfc18dcf5,0x33030caaf369168a,])),
        field_new!(TweedleFq,BigInteger([0x8c70022989fb1873,0x689cddd1ff5364e6,0xe43915e779987cd2,0xad70e658ca6fd5c,])),
        field_new!(TweedleFq,BigInteger([0xfc809c9d2f122624,0x845541d87548a95f,0x807666ca0684c278,0x28f8db02d716f24a,])),
        field_new!(TweedleFq,BigInteger([0x7f3cc106a057f763,0x95ff928143f13764,0xe78eb2931e4c48e3,0x18b6de0c9b8e51d3,])),
        field_new!(TweedleFq,BigInteger([0xcad66b0f478d4938,0x679ceaf32b89ed02,0xc60d2aecdc6ae645,0x3a4f37edcef5fa6,])),
        field_new!(TweedleFq,BigInteger([0xeb6f3accbb533090,0xe782b5cb3d80508,0xf6b0b0068cbe491a,0xbadc9d01924aca9,])),
        field_new!(TweedleFq,BigInteger([0x8d6ec1034e6ee87b,0xdda576220a46f2bf,0x3b51df2a54e053e8,0x12ee47b96e8d9e01,])),
        field_new!(TweedleFq,BigInteger([0x3685322867e98a64,0xbbdd37884e1f5315,0xa5b3251567724e8b,0x15db57f19953bab8,])),
        field_new!(TweedleFq,BigInteger([0x1d69dcabdb96377e,0x84ca7f27ceacf2c4,0xe822a15978266d24,0x1d21c65affccf4e3,])),
        field_new!(TweedleFq,BigInteger([0xe2c41ca381b9c749,0x3a03b66bb412d9df,0x9562225e852bac08,0x3113525ee441505e,])),
        field_new!(TweedleFq,BigInteger([0x633a8256bca97d22,0xbc0b2a9d0eb546b8,0x709b703c8f011356,0x37bc0b8358f942cd,])),
        field_new!(TweedleFq,BigInteger([0x1f3b9e5d89c6f992,0x393621c83ddf849,0x9786715da3a90989,0x1de654f726c14f93,])),
        field_new!(TweedleFq,BigInteger([0x2d75ea8c4aead3da,0x8a06ee203ed7b3b0,0xe64881c6db3b5a3b,0x130186a1146523f2,])),
        field_new!(TweedleFq,BigInteger([0x3afbc5adc5b66808,0x912bb29349446cc1,0x929d5727c17918d8,0x2dc89ed2282199ac,])),
        field_new!(TweedleFq,BigInteger([0x57bbf8ee06cd5c1f,0xd443e91f71c98ab3,0x1d4a56187d6ffd47,0x29a32694e73c8c3,])),
    ];

    // The MDS matrix constants
    const MDS_CST: &'static [TweedleFq] = &[
        // Constants in Montgomery representation 
        field_new!(TweedleFq,BigInteger([0x29d29e3fc4327f37,0x4a71f5a80543ba53,0x28343f4d85113153,0x146244617e3208b3,])),
        field_new!(TweedleFq,BigInteger([0xa139e38b29f41c27,0x789fab6072d358b4,0x2dcb2167e0b29b48,0x280dfccf1f6b9be1,])),
        field_new!(TweedleFq,BigInteger([0x694c5a0ae9e2d07d,0xbb9d5f60decb65ca,0x45ab7d7951a783bb,0x17fa6ca9e15ab684,])),
        field_new!(TweedleFq,BigInteger([0xb2faa16f5c3a45b1,0xd86b1eb52901aefe,0x1b45401c83c8af87,0x28e5fc140911a0bd,])),
        field_new!(TweedleFq,BigInteger([0x4df780dc63cc6487,0xeb0e2f581e5c0167,0xb295a2dac1ae122d,0x2583cbe2f6410dcd,])),
        field_new!(TweedleFq,BigInteger([0xfb3433ff98df4158,0x4f1e9cbb7bd9d830,0xd6c392b56e511eaf,0x29603ea841f482fc,])),
        field_new!(TweedleFq,BigInteger([0x5d0f8c21f3103c0a,0x4bd7e380363ee1fa,0xbb51c3e6961a11e,0x147e0cefa92d20f7,])),
        field_new!(TweedleFq,BigInteger([0xe3b5c1497d6063c8,0x50786edf4424e90,0x25767b9e7a9f6350,0x32d6a4ef51ad361d,])),
        field_new!(TweedleFq,BigInteger([0x22d506c126f41925,0x68b0be1808f21e30,0xdf7490986a2a1e52,0x3f7d2f6090dde3f5,])),
    ];
}

pub type TweedleFqQuinticSbox = PoseidonQuinticSBox<TweedleFq, TweedleFqPoseidonParameters>;
pub type TweedleFqPoseidonHash = PoseidonHash<TweedleFq, TweedleFqPoseidonParameters, TweedleFqQuinticSbox>;
pub type TweedleFqBatchPoseidonHash = PoseidonBatchHash<TweedleFq, TweedleFqPoseidonParameters, TweedleFqQuinticSbox>;
pub type TweedleFqPoseidonSponge = PoseidonSponge<TweedleFq, TweedleFqPoseidonParameters, TweedleFqQuinticSbox>;