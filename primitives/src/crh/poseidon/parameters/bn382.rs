use crate::crh::{
    PoseidonParameters,
    FieldBasedHashParameters, PoseidonHash, batched_crh::PoseidonBatchHash,
    PoseidonQuinticSBox,
};
use algebra::fields::bn_382::Fr as BN382Fr;

use algebra::biginteger::BigInteger384 as BigInteger;
use algebra::field_new;

#[derive(Clone)]
// x^5-POSEIDON-128 parameters for scalar field of the BN382(= Fr).
//
// The number of rounds are computed by ./scripts/calc_round_numbers.py, round constants and matrix
// are generated using the script ./scripts/generate_parameters_grain.
pub struct BN382FrPoseidonParameters;

impl FieldBasedHashParameters for BN382FrPoseidonParameters {
    type Fr = BN382Fr;
    const R: usize = 2;  // The rate of the hash function
}

impl PoseidonParameters for BN382FrPoseidonParameters {

    const T: usize = 3; // Size of the internal state (in field elements)
    const R_F: i32 = 4; // Half number of full rounds (the R_f in the paper)
    const R_P: i32 = 56; // Number of partial rounds

    // The zero element of the field
    const ZERO: BN382Fr = field_new!(BN382Fr, BigInteger([0x0, 0x0, 0x0, 0x0, 0x0, 0x0]));

    // State vector after permutation of zero state vector
    const AFTER_ZERO_PERM: &'static [BN382Fr] = &[
        BN382Fr::new(BigInteger([0x3600ae9dea9ba41a,0x17a35e3bedfc2e1,0x7ee93e40052b3867,0xc555ef28f09e84e9,0x1ef349664ad402cf,0x1c49706c59f09b25,])),
        BN382Fr::new(BigInteger([0xbb6f865c755b9100,0x6f6ccbea5f0c5847,0x4cfd3606c21c2573,0x3512ec3dc6889f67,0xc7981de6b0710b5f,0x109fe23f817aa0cf,])),
        BN382Fr::new(BigInteger([0x39de13d041934215,0x5370089a3da7c4fe,0x512952ce97e48c03,0xe1c26f50f4c9c4c1,0x1f008942e907b93e,0x1910b7b5453ff08f,])),
    ];

    // Array of round constants
    const ROUND_CST: &'static [BN382Fr] = &[
        // Constants in Montgomery representation.
        field_new!(BN382Fr,BigInteger([0x612594bbb1b6e471,0x378e47c761bde158,0x3bc6646891051db3,0x5a4b437eff423c1e,0x9872641294446a72,0x10dc628330a637a0,])),
        field_new!(BN382Fr,BigInteger([0x648b925a912409e4,0x3137eb5e72da8291,0x58d3c520be2d4e86,0xb68fbeb1ab564e98,0xc47730e1b98e2804,0x20e7bb9a467b3926,])),
        field_new!(BN382Fr,BigInteger([0x1d51c18e15d84b89,0xb679e453773a1166,0x2e7a43308fdef5b5,0xfc1727f11c11bebe,0x34438c67b8107cdb,0x217f841af91c5293,])),
        field_new!(BN382Fr,BigInteger([0x187fec8936804a9e,0x4fad22235608d500,0x53eb48d5a7e0f37b,0xb540d80d00de0206,0xc718c0ea9b4d8ffa,0x14f78a64836e832e,])),
        field_new!(BN382Fr,BigInteger([0x21b11c3f5923a641,0x82421ecfad69dcec,0x6054cc7043a10170,0x414c0d35d1af8a48,0x3d3b2e5b0344ae4b,0x2539bfc1d203ef3,])),
        field_new!(BN382Fr,BigInteger([0x6242abe27a3fde78,0x6ac220eb054337dc,0x68ec76e4f7ab3367,0xeaf43afa8ed9f4b9,0x69b4c57bd8ffec75,0x244402235244c6c,])),
        field_new!(BN382Fr,BigInteger([0xd03b987b146a036a,0x5e1a6737273007dc,0x6b3c110658ea8329,0x28b86415ce76e590,0xb4c299a0f4b35288,0xb277b8b1dc45b54,])),
        field_new!(BN382Fr,BigInteger([0x1851ccbf8ac0c4a0,0x7bfbabc08b8e1820,0x5f9e8f70cc0d89e6,0x6a60d3e9b2efab9d,0x5f00532bf5c3e7b7,0x163c93f958fe6165,])),
        field_new!(BN382Fr,BigInteger([0x2e025a1b9fc1cf7e,0x9d2a3926c8e4873d,0x815247d8b3ed282b,0xbcea0d05bb60e6e0,0x641d40f393b70f0b,0x49937dc4336efc4,])),
        field_new!(BN382Fr,BigInteger([0xc4fe4660dc170c54,0x6466c8bf6bae65e6,0xe0b937fbe714c317,0x1b5c3c9e3bd86eb1,0xed6d009f6c0f689c,0x1a2e64b8e1160157,])),
        field_new!(BN382Fr,BigInteger([0xc2677abcce729473,0xcc2ad5dcd10e8138,0xbc00ff9a08251b0e,0xab06e89754bdafda,0xaf9ee29407761667,0x1a91142192f16d77,])),
        field_new!(BN382Fr,BigInteger([0x5d3924656b2e96b5,0xf07dce7e5b93e084,0x11cb47794099c628,0x1a51be34bcd1f11,0xfb6c4a29847ed8bd,0xf8cd5fb058a687,])),
        field_new!(BN382Fr,BigInteger([0x4b6abf73349047c5,0xfb00fb1d0ce00e97,0x2c80aa15dc10fd27,0x6c1c172bf58bf5db,0xc5afa80758f61cc1,0x101ab8639da5903b,])),
        field_new!(BN382Fr,BigInteger([0xee84aab656871f2b,0x7b59847da780fa09,0x9ed2e4ef8c67a6ac,0xd1d5e4983fb63d56,0x918ef129484f6416,0x4ed575d596b0602,])),
        field_new!(BN382Fr,BigInteger([0x58f3f554d7c5b733,0x7691b6862724e884,0xdeef90c871cb4e65,0x1e13cfc8f6e08cd5,0x46885ac1ae81376b,0x3b58110b0de832e,])),
        field_new!(BN382Fr,BigInteger([0x446e0dd315118672,0x34362a3a5782fcc,0x869e30e64061f70f,0xa2d416d4ac47e503,0x26e45bd23d2d5e72,0x1e942e7f440e111e,])),
        field_new!(BN382Fr,BigInteger([0xbbbef86dad29c116,0xafccad57e6e0e283,0x55db744a8ae16107,0xc334fcc6fe3e1d33,0xba84412daa85c437,0xf83004f4d48bfd1,])),
        field_new!(BN382Fr,BigInteger([0xb1f4a46da7d16e93,0x6aa9efa28eceea77,0x3f5a7def907b0fec,0xc04ad03d8e686b12,0xe2867b73d9b9a42c,0x1842fe7d5ee870f4,])),
        field_new!(BN382Fr,BigInteger([0xa4cab7e77ad91d2b,0xcc939045d9622fc0,0x4dfd4554bccbec82,0xa082bef06a3aa21f,0x2495c409d9b20891,0x1eb8aac188034c7a,])),
        field_new!(BN382Fr,BigInteger([0xc220e4cd7cea36bd,0xd7ddf157d467b5e0,0x9cda30e4db26a535,0x501d52e6919d3d85,0x8e3341dcf7cdcfcd,0x19c18a87cb0f478a,])),
        field_new!(BN382Fr,BigInteger([0xc4434445afe11416,0x93d860a5f1808a15,0x76a6f908b263c167,0x3c535ecedfcc7474,0xdff4b09337bb69fd,0x1d8146147a732b6b,])),
        field_new!(BN382Fr,BigInteger([0x53869b602d088ead,0x34562e6fdf6c489a,0x2746687a5902c65,0x52fcb012dc77ea19,0x3932aa1140bd8740,0x42b278db02964d0,])),
        field_new!(BN382Fr,BigInteger([0x663001807d2d112a,0xc582d9dc8bf0fa09,0x2084c427cdffe861,0x78c456b8c3b2525d,0xc7758eb65b16edee,0x13cdf833fb9b7b02,])),
        field_new!(BN382Fr,BigInteger([0xc102214b726d6540,0xe1756cf3989385b6,0xaba456a472886b86,0xe69fc37dc73c9d97,0x7a8fa6d7359914e2,0xe5689850df5d1a7,])),
        field_new!(BN382Fr,BigInteger([0x1c9e227aa38dc007,0xbb2289a1aaf0a6b8,0x7c2c107cc99c14cb,0x46feeb0231bdb907,0xecf91543b2399e6d,0x260e275c81141e3,])),
        field_new!(BN382Fr,BigInteger([0xd4209b6bf5e09b4a,0xc4d65edcaef6f4b2,0x7d6c16c833bb04d2,0x76f8559c97e8bc5,0x993a8698b0af0ff2,0x91b038ba5c6fbb5,])),
        field_new!(BN382Fr,BigInteger([0x6a66939c2a3e8234,0x6e36f00a8c275e35,0x84e0cbe222635c19,0x64567200b6471bd5,0xfcae76b4aa74cbd0,0xc5bc9f742bf7dda,])),
        field_new!(BN382Fr,BigInteger([0xbe090d890c1fbb82,0x5f466d9dbeb0f41f,0x95a1b4467bc8f316,0xb4394875c87737b9,0x9eed654652634c31,0x21ddf7aeb3256046,])),
        field_new!(BN382Fr,BigInteger([0xecbd0679d0cc2e2f,0xb100a1ed21b586da,0x38954a366b39c0d5,0xf1199b459e8ca278,0xcef14e9c83fbafa0,0x1b06bce55c89647a,])),
        field_new!(BN382Fr,BigInteger([0xb5fb0ccc085896d2,0x17d57df63f346658,0x59cb1ea93e0b8ea7,0x480042e193b0a945,0x352257c21f74ac58,0x18ec5afb2a583fd,])),
        field_new!(BN382Fr,BigInteger([0xf29704cee883c5f9,0x4cdea6c79755e0c6,0xabb0de810e531941,0x870fb7b6310a798a,0x91b1f1aa665000ac,0x22df418d022c49c3,])),
        field_new!(BN382Fr,BigInteger([0xb0e5b193025cf63e,0x70e6498ca19ec864,0xdc620e0e6c661bb9,0x2ae93e3bc005351e,0x16ea0c602ffa4c56,0x1c1c3ffea1ccbaa8,])),
        field_new!(BN382Fr,BigInteger([0x12209b68ba85fbc7,0x59cf50d6cb4e97de,0x60a0db7096520aec,0xc18b7bb5fd86bf94,0x17cd558db842f379,0x10a08f25a0cc9f9,])),
        field_new!(BN382Fr,BigInteger([0xb2283575aae39034,0xb00e40d02a1aebad,0x47fb96740c989d41,0x8feecc9254494342,0xc3a3641a41d83c15,0x17c5acd67472548c,])),
        field_new!(BN382Fr,BigInteger([0x908b884bf8495e02,0x4fedd1613523eb2a,0xdf9e7857d5b4901b,0x1da985a29f773b6f,0xce5bd199e3640c8,0xa87bd4fc26b35db,])),
        field_new!(BN382Fr,BigInteger([0x939945437ccadce,0x25e9ed3e56dd88e4,0x540eed7468cde940,0xec37670dd2e43309,0xf1fc0a5beda99cd1,0x105dbc5c778ea0db,])),
        field_new!(BN382Fr,BigInteger([0x3c1023ff94b35ed9,0x245407c49b2d2acb,0x9ebd77aaed0fc04c,0x496e72558c5ec89a,0xd41ed7f1dd9d5436,0x1a5f1ed7d8aff27b,])),
        field_new!(BN382Fr,BigInteger([0x61d199a03b8ea301,0xdebf75191444d05c,0xde221b14381951c0,0xbe532ad1c7c2fbb2,0xbc03d6b8a664b3ca,0xf2f0523c2f3b8b6,])),
        field_new!(BN382Fr,BigInteger([0x85ae87462afa2675,0xa4a639046e7177b6,0xb58292f4b192d5ec,0x4bcd2ff0c329e04f,0x87e1cfdc670e8333,0x56ad8723efc665c,])),
        field_new!(BN382Fr,BigInteger([0x14eee3f1fa623589,0xfae4dbad19ac9796,0xf793271c6996f743,0xc5c55d0ea1b714d2,0x597475995b5ad044,0x2139a591e4311498,])),
        field_new!(BN382Fr,BigInteger([0x87ce55ad4f9f95af,0xde157639400314a2,0x20474aa26d1d83ea,0xf5cbb4a5e03c9636,0xfeb4568697e45e31,0x8af3f7bea74fd70,])),
        field_new!(BN382Fr,BigInteger([0x434a2cc78d712030,0x6e0d22f536b573f7,0xe0b1dc67d929947f,0x6884a2f7c44f353c,0xd46fdd9ce1d5b6a5,0x13ef30c2ed69dbff,])),
        field_new!(BN382Fr,BigInteger([0x7a040f4d6d94f86f,0x27c1ce564ddf4262,0xa81b7f221c69617,0x57c9ce680180abb0,0xdf3325058728863f,0x23dccc19d0bc5ea9,])),
        field_new!(BN382Fr,BigInteger([0x539fbfa2a87db0f5,0xa57f6e213f3bb620,0xc34c6cb5ddc5c2cc,0xf40ccbca5bbda6b2,0x3e306ad129c8ff11,0x408c61bfc775733,])),
        field_new!(BN382Fr,BigInteger([0x46e61f5887d07b9b,0xc96b76d4c5f08401,0xc74f6d63103d19d8,0xb8459c6564c47b85,0xfc5f6901c0b4379b,0x1da94c36fc845606,])),
        field_new!(BN382Fr,BigInteger([0x2d795708468a266b,0x961a55c7e1219e39,0xae6f2d01860872d3,0xab7800372cf73559,0x48f717b74e679149,0xeda31ac67ae5315,])),
        field_new!(BN382Fr,BigInteger([0x7137f30d73d73f81,0xeecb48eb237cd378,0x1637a75145b62358,0xbd580295215776de,0xf95009ba8b9089e7,0xbf303de2dabc0c,])),
        field_new!(BN382Fr,BigInteger([0x4dd5f94cf3e3b24e,0xf02fcb016625225d,0x8a2f20c64b044caa,0x82ab8c456706ab8e,0x9f95f6bcbd936b1a,0x94add9e4777f3ec,])),
        field_new!(BN382Fr,BigInteger([0x72cec38fc44ae9fd,0x524c561c05b3ee03,0x335c6503d6ff69e0,0x68b763fb63724d9c,0x3e1d47f963a16b93,0x17005cec6551b146,])),
        field_new!(BN382Fr,BigInteger([0x8d45f8b369ddbb5d,0xcd6da2f230c4791e,0x2e75ad84501b4cb3,0xfb6f16ad8af05c68,0xf43ae1565f6b4198,0x9c663df67c79ae0,])),
        field_new!(BN382Fr,BigInteger([0x744bda0fa1185896,0xa54e5d9454a4a5f,0x486c322adab592c7,0x49f15ba85bda0074,0xbb548ebcde301c96,0x1d42d55c1d34128d,])),
        field_new!(BN382Fr,BigInteger([0xdcdf4a8bfcc014a9,0x5731a326cd0f6091,0x59e4fe149f9fd6cd,0x37ee92e10f1f3bef,0x2ea7d49a2b35dcb3,0x1e3807bbb0193b6c,])),
        field_new!(BN382Fr,BigInteger([0x947e60321e5db74d,0xeb8d9dbd8663c6e2,0x181a6b7b22756fa0,0xba33ae95d315c6c3,0x6f8adabe4603a166,0x200f79799699f8d2,])),
        field_new!(BN382Fr,BigInteger([0x48f46aa4c5b7edcf,0x81f6079017544d02,0xf44dc26c65bcc111,0x5ccb22f8e2342245,0x6cdfd3b3e088fa73,0x5dfa8d483b29d9e,])),
        field_new!(BN382Fr,BigInteger([0x46f9c1d6dc3a3635,0xdb744fdfe3a39cae,0x90135be4a873578b,0x5a9a6d05af9d75fc,0xd56b6c884a05cf30,0x128ba26e0aaff223,])),
        field_new!(BN382Fr,BigInteger([0x1b9ef2e1fdcad621,0x22fc1ed56a7c3271,0xb5a12609a2d85cc0,0xeb940b6d340c1ba8,0xf0c5210206945b36,0x56423779cbc31b9,])),
        field_new!(BN382Fr,BigInteger([0x29b6515a963138b4,0x82a4f40a10483963,0xaf3f3ac9f947d89c,0x9306458f32ecd397,0x993b226bd8984495,0x23910c546f06701b,])),
        field_new!(BN382Fr,BigInteger([0x9a8064a6e0e0cdf0,0xca2db5ff06cb19b5,0x4ad1b252db8bcefc,0xa125bd8c6ee80cd,0xdb2b447da09ea5df,0x1973b1f2fc25dca0,])),
        field_new!(BN382Fr,BigInteger([0xefa6fc1bc0692d14,0xfbeacbcde0f07b9d,0x4da046680b1daa6b,0xfa142ee742f4f49c,0x9dec9e73eda83945,0x1b3ec0ffa7d9aeaf,])),
        field_new!(BN382Fr,BigInteger([0x9814b0e799d15a4,0x3848483e9e34c1d2,0x6f82cd22ea499b17,0xbff924dbb25ee1a0,0x29b340d84e573aeb,0x1a4a3b9b9a612267,])),
        field_new!(BN382Fr,BigInteger([0x25e1603d2672c8d4,0xd2a6a53a75cb5b51,0xf5c4c73dbb0a9e35,0x5c9c03c61fa094dc,0xbb02f422986b4d34,0x15f0105f67207436,])),
        field_new!(BN382Fr,BigInteger([0x8e3b556b0e951eae,0xfbcd9bd056290492,0x9f3730541b1f9da5,0x8ae8e49dded74ba9,0x171b39226325e1b8,0x3b71540db8272f8,])),
        field_new!(BN382Fr,BigInteger([0xe801f84196a415b5,0xc853b94a1fcd3a7c,0x9562f03fd0432bf5,0xd9b5ce252ef78b77,0xe57608a901117f27,0x1c2b311ff94b347a,])),
        field_new!(BN382Fr,BigInteger([0xe2799af45bf5f7d2,0x479541284a76235e,0xf0a9940508e04519,0xd2d212f8be526b70,0xcd2f5f564c2eba9f,0x5080a96532ff18b,])),
        field_new!(BN382Fr,BigInteger([0x332175a4423c8923,0x6cbe63b275c0d82d,0xbec33a42798f65fe,0x132e172ca2b60e2a,0x51cbbd900cc2c75,0x2dfa65296c60e99,])),
        field_new!(BN382Fr,BigInteger([0xe0a11f06a9ee6d32,0x44e2f4545749bac7,0xf8a8e15a15ccb7a,0x15d7111b564d06da,0xd7acbc538912e7f,0xd9b432f044de0bd,])),
        field_new!(BN382Fr,BigInteger([0x165a83a1ec85d1fa,0x106ba5c124610036,0xf4b65d8666c1127b,0x539454aa40c802e5,0x52b7cb09a98ef05a,0x40606e30fdd2590,])),
        field_new!(BN382Fr,BigInteger([0xe2180fd4b11735e,0x1d4e8d9294054096,0x522d0d21c472caf9,0xd974eca535c80945,0xc235e94823a37ab1,0x1afe8df0b43f34b1,])),
        field_new!(BN382Fr,BigInteger([0xa76cacf57c6d42b6,0x69a31cab5ffec23e,0x847382df32999bef,0xf8a5b4629ebe83a0,0x9a56273965d1a8af,0xe3fcf60b082db41,])),
        field_new!(BN382Fr,BigInteger([0x8c7654b932e5a0e7,0x83f6d3395b0fbbca,0x319b957a385b7f9c,0xaf3e99f27aff72e0,0x2321cad504dcd5c7,0x2e00ce72a6be2af,])),
        field_new!(BN382Fr,BigInteger([0xa2cf2778231357d2,0xd0392de753e2fdc6,0x48e5271c1306beec,0x703038931cd972e6,0x5b40bbc31ed1424a,0x11a32d36858681b6,])),
        field_new!(BN382Fr,BigInteger([0xefa9b4f0ddfd2702,0xc9d3e274ac5b5e32,0xd4ef26276dc1a95b,0x9d85956870fa6309,0x538402d6a4f95f87,0x20ef3e759e2b5774,])),
        field_new!(BN382Fr,BigInteger([0x2f60c3d89d527633,0xa3e0be9226ecca86,0xf1689ad9efa4c39a,0x5169a21bce1fe136,0x6e3540a32f9e4aca,0x1c975d864f6a9908,])),
        field_new!(BN382Fr,BigInteger([0xa08b2ea220ec0f01,0x86632b185d09b55e,0x3d0ab9907cf80762,0xb2f25baca5f2a8b3,0x604fde4a028521a7,0x17e1b72b82b07098,])),
        field_new!(BN382Fr,BigInteger([0x9035d4d6b225e113,0x199b7c8dad453c0e,0xb0124646645d7d8e,0xfeffddbef7fbb9ed,0xf7c8e24de35d28b,0x17946871be482e29,])),
        field_new!(BN382Fr,BigInteger([0x68cb8cf32f1fa3ca,0x8410a35992e64198,0x1656e4c3c8809d1c,0x5a7a593ea5160028,0x6f9884fec64ad87,0x68f342a7d9c1578,])),
        field_new!(BN382Fr,BigInteger([0x6aa1649a239a3994,0xf3873ada62153606,0xd4f0605c7c2e6f90,0x942229d8c0244a22,0x4be923475c5f8097,0x4c543a99bf453e1,])),
        field_new!(BN382Fr,BigInteger([0xc6aacfbf3df91e60,0xcdc8779b251de05d,0x490ce8abcbd485bf,0xe07f2f206b0a0000,0xce85478b8702534,0x1fe00bbda79ba428,])),
        field_new!(BN382Fr,BigInteger([0xa365d86d6c8c4ab0,0x1df5e4d2f04cc1e3,0xdbb4ce154979385e,0x2b5184972a069c50,0x8aac4c3dce9136fd,0x2a3b121f3358ffc,])),
        field_new!(BN382Fr,BigInteger([0xbf66da9421be42ed,0x226d53670264f514,0x5a781ad5bd473d6b,0xf4d62ad2a6af1bb6,0x3380da9a0c1a6c10,0x16f0e7d19f26d09c,])),
        field_new!(BN382Fr,BigInteger([0xe644fa4d4fb7342a,0x15e768944458bb5c,0xd528cc6f453699c,0xc4b9157132f26c6a,0xc31528ac8f8d8b3f,0x945a72e10891225,])),
        field_new!(BN382Fr,BigInteger([0xb321b56b8f98610c,0x3ec88e37031b97fd,0x85c0e7cfba951245,0xa6d89f69de3e394b,0xfa3ae8fc7b87e7fe,0x212cc2675acfa9cc,])),
        field_new!(BN382Fr,BigInteger([0x357863050cee0503,0x1e9fc0db7868b869,0x586e7953b8e42ac,0x87386dcbd2b79642,0xafd688ea111ad0e7,0x23f60a02b4a4fe59,])),
        field_new!(BN382Fr,BigInteger([0xaf6a37deeb831a81,0x881b385fb805b87a,0x4701bfe082a43e05,0x41650f00a2d6e8db,0xbb2ca998e39e13b0,0x232f4f9687b47327,])),
        field_new!(BN382Fr,BigInteger([0x4f8605c1f2ca166,0xbbef46f7849737df,0x4b0fdee02ed2ac0a,0x532c2e3af6785dc1,0x7510d9520a1c3ddf,0x15f653783e92ba13,])),
        field_new!(BN382Fr,BigInteger([0x4067cab4773020b3,0xe5c29073725ec874,0xa7abb978a061096f,0x1c587a24de3a3b6f,0xfd33c6fc2986a8e3,0xa5fa65cce47aa42,])),
        field_new!(BN382Fr,BigInteger([0x533dedcc81369bd0,0xbdf53837b9d23058,0xe27b721a005b5faf,0xd21b8da39f0debe8,0x8f7f95eb502a4d53,0x877f53f518ac833,])),
        field_new!(BN382Fr,BigInteger([0xdb570121e5620ca5,0x4cc42224d164e33e,0x1e0fababde2a1608,0x9f0b888d97f43a5d,0x7d7d77d695f1a40b,0x1187a307034c3250,])),
        field_new!(BN382Fr,BigInteger([0x3bf4d0689f992368,0x3028683c9bf5f61c,0x753ab3b520ad87c4,0xb0ea236abf05170b,0x78cd2cf60bcb65ba,0xaba26bcf92961be,])),
        field_new!(BN382Fr,BigInteger([0xaa04a6057e9a5895,0x6020909871225d55,0x7c934fefedfcb2f7,0x35be567d72ee7f68,0x3a3ae567bf722173,0x23f5342de659b66e,])),
        field_new!(BN382Fr,BigInteger([0xbb1b0a89f8f674ef,0xb218e7f698309305,0x212f47513733f4e4,0xd7b2c046fc3c8198,0xdd0f369360ba052e,0x148adaa1a5d07646,])),
        field_new!(BN382Fr,BigInteger([0x3d2b35dbb9f9f32c,0x1df6064e3b7883f0,0xaeeef2fc5b7cda5f,0x5f569f59490867ad,0xab41c3c99ff1a7b,0x1f6af01b4069f01c,])),
        field_new!(BN382Fr,BigInteger([0x7b08f7196f95f250,0xebd998a94641b216,0xecd17f2f0e6b7be2,0xd45567f5aa54063a,0xe7dfacc677a37ea6,0x131d85807f2536d2,])),
        field_new!(BN382Fr,BigInteger([0x85385038acab36f2,0xa9d46b0a174ab171,0x2aec8efde8e83eaa,0x535702cf318b0449,0x791e65318aadaa29,0x11cc5aaabe45a470,])),
        field_new!(BN382Fr,BigInteger([0x8f47e1abf7eeae37,0xf81d797cfd12fd6d,0x1f403efbcea531ef,0x12242501b075fecf,0xcba721d0e59ec56e,0x1d95cca7805931a1,])),
        field_new!(BN382Fr,BigInteger([0xd20a477c6171f257,0xf3733e0aec025177,0x58a7c392f84a3100,0x9e44fb173a2de05f,0xa5b0e85f7e550abd,0x775c9caf7ae3540,])),
        field_new!(BN382Fr,BigInteger([0x7ad7c44ee12ddbf8,0xc685d908e1c0257d,0xd21db1d7d01e1c7d,0x4f49944f6bd9773f,0x7178542947e4489b,0x7628c430703efc7,])),
        field_new!(BN382Fr,BigInteger([0x299be442511a549,0x7eecf2053e4f9fdb,0xfcda10b863099df7,0x893ecda9e309edb6,0xdfd6d782c3fc588,0xe064ef8fed04cae,])),
        field_new!(BN382Fr,BigInteger([0x208ab9b77971c005,0x11a5e62003b6177e,0xa03468532c04561e,0xf241db89cbbee228,0xe14a9a8790b67ba8,0x3b9ebf739eadde2,])),
        field_new!(BN382Fr,BigInteger([0xcfdd3f19dcfe7200,0xcbd8ed1a0fe60cc3,0xd89719d2ae246454,0x82bf01f10ae3d89,0x3cd3795a60c92a93,0x6146368a87304fb,])),
        field_new!(BN382Fr,BigInteger([0x69ec3312c6016ef4,0xfa5bc3577cded484,0xa7c91d6c06a093a0,0x6af99c6916f16e96,0xb18c021e88a175c7,0x1c76d7686ed24a21,])),
        field_new!(BN382Fr,BigInteger([0x97b3eba6b93daef6,0x9bb66787f505a5d7,0x1dcd50ca8f8b7a04,0xc2d2f0cb3282e2d2,0xe38f6b1b5b28bce7,0x113d44625996b66d,])),
        field_new!(BN382Fr,BigInteger([0xdf57996b93afc1ad,0xaf30f4ff3b168631,0xa931c3e1e775bcc1,0x7adce239e718404a,0x7c7a6a32c80a0397,0x1f96cd3f39c5c93c,])),
        field_new!(BN382Fr,BigInteger([0xc5c2f205e08455b2,0x6fd98f231c9bbf5a,0xe9160824fc9537af,0x530b6a7df23676a9,0x36b9a6ee3f8377fe,0x1d1e1dead541740f,])),
        field_new!(BN382Fr,BigInteger([0xce22230822007509,0xac72ea574a7ce9cb,0xe818ca23600e10c5,0x5f101b62bc4256ee,0x2edf5dc78c2423ce,0x858f27f979a1ff5,])),
        field_new!(BN382Fr,BigInteger([0xfb99e91588851f92,0x334de6ac473e5ba2,0xb5987498886b2763,0x4b3dc539e53d3763,0x1b2f2b45c1788b82,0x1bf8e8124a6f04be,])),
        field_new!(BN382Fr,BigInteger([0x8b26faf7d19cf85f,0xd0153d21f912ed09,0x7e29be298642eaf9,0x9e16e137643a57f9,0xeb50ba0623229882,0xf2cd70c90e5c137,])),
        field_new!(BN382Fr,BigInteger([0xed5975879d4c9335,0xbe147ec26265105,0xb9558ccabc1c9d57,0x7fa00c926e0f6ebd,0xb4b628e17306abf0,0x17156fd3629203c2,])),
        field_new!(BN382Fr,BigInteger([0x289c6f8d69ddaf35,0x1e389db66f6417cd,0x15840b36d2b04b1a,0xebdc1ac5c474f652,0x8cbeb6a72a503fa,0x16a41a19459c7f31,])),
        field_new!(BN382Fr,BigInteger([0x3d9801d7761cc606,0x8051e52278a87b74,0xab13d148e96d8058,0x3453fd74e5dedd7e,0x48bb90eb7286187,0x22460c3a490b161b,])),
        field_new!(BN382Fr,BigInteger([0xdf286f0c78c02975,0x13050e707ca121ef,0xcd7950cc3f022cab,0x75f58ef17509e38a,0x11de934ccf45dae0,0x299ac12badbb5cd,])),
        field_new!(BN382Fr,BigInteger([0x91684a0c014dc61d,0x75df2538a72a421,0x12c39c7bbc30e033,0x12000da5d041967b,0xdeec8ba0d47a3c46,0x11c74d47691149f9,])),
        field_new!(BN382Fr,BigInteger([0xe613c4e3dd026369,0xd9cbe6fb91d0c4f6,0xa6d7cbb5ec4e707b,0xf08f73238bb560e3,0xf5c9bab7aac2dd3d,0x2909fa265a93ebf,])),
        field_new!(BN382Fr,BigInteger([0x5cf20fbd0d0d48b2,0xbc5fa7e7c70898a7,0x8e264b6c284ab7f,0x3483a690e97713ce,0xcd7ba5a6fbdab1f1,0x4161814bdcaff4c,])),
        field_new!(BN382Fr,BigInteger([0xf5933f81aaf94238,0x1ef53b2aff05625a,0x51400e271d42eda6,0x56d38c87cc4fde24,0x52f37e6fd7c369be,0x4ff1d5e02f92ce1,])),
        field_new!(BN382Fr,BigInteger([0x8d0bbce67d7fa5af,0xbd8171f1d66fbae7,0x6510c52bc3406195,0x7a34305832edf74,0x22c815ae2893d67c,0xe0a06c13b0590de,])),
        field_new!(BN382Fr,BigInteger([0x63a5acef15bd163f,0x5e1292e82b660d02,0x7008fb440cdb92f,0xa722012e2b46f69d,0x9b3562fa323495cc,0xaa3b17b1693a9f,])),
        field_new!(BN382Fr,BigInteger([0xe5276a57d8326b2d,0x24216cbd2b2b3386,0xc6a03b315c24b23,0xbd6ef4ff9bb0b420,0xf30d7cf1ddeef03f,0x1836f0533b24db24,])),
        field_new!(BN382Fr,BigInteger([0x81a3799217ebe001,0x5b130e3e2b989267,0x39d1e9e36cb21487,0x4e5f75781535f1ec,0x588a839951b2d619,0x229910365618a427,])),
        field_new!(BN382Fr,BigInteger([0xa5c15385b840fb15,0xd13718215429bedf,0x253e95be77bbc624,0xf4baceb37c1f046a,0x5a3bfd255ab0782e,0xd8a4c4c43a4ba72,])),
        field_new!(BN382Fr,BigInteger([0xf003d683557c00a7,0x2e65eeff293d4c0a,0x782240b45e7bdc89,0x924b1f6b64f3e901,0x164db2bcb6533af4,0x43991de11efce49,])),
        field_new!(BN382Fr,BigInteger([0xfd2782d5e0d4e8d5,0x6da02e0ceef5deed,0xbfeef7aaa6316117,0xbf072772f2ef3700,0x15d320ca38578a78,0x29afde87db3e525,])),
        field_new!(BN382Fr,BigInteger([0x390972e93a070537,0x820cf65537fd40f2,0x9834888c10c3ed1c,0x612d06a291a63e8e,0x43223bfd0df37c7b,0x11a49225d8578fc4,])),
        field_new!(BN382Fr,BigInteger([0x32eeb2908138d2ac,0x3dc1c46f1bd91d96,0x3c9b7fdff2c894ca,0x69ab314018fb277a,0x9aa35d2992dd6f67,0x55a2460cc63c607,])),
        field_new!(BN382Fr,BigInteger([0xdb31badf8b3fcae9,0xb1d0eaedebb52841,0x720147e41b5c7ac7,0xb091b6e5ec8d6254,0xad26104dc2ab12a4,0x1a6ce6bfafc654d,])),
        field_new!(BN382Fr,BigInteger([0x27d211809720fc52,0x4abb28d977c17853,0x94e1bb63cc3c0bb0,0xeaf11f4190d56fde,0x55c0782e7ea21b50,0x3bccc01d96f4313,])),
        field_new!(BN382Fr,BigInteger([0xb68bc0459ca55cd5,0x2b05f7835969ed72,0xe62bd13014fd3617,0xad8d2b9749f8142e,0xc7c169b169139f39,0x206668d88617eb11,])),
        field_new!(BN382Fr,BigInteger([0xb2a3de5de36bf48,0xdd88d6ca0ab87eef,0x89404fc445070ef3,0xb148f5cd3ffa3aaa,0xebcef82c8cd243f7,0x1e33db199c53a413,])),
        field_new!(BN382Fr,BigInteger([0x2e4c1b10fc98ac9d,0x886165d8f5ff092a,0xaad87a9b145fee16,0x530c6e6999ada6f3,0xc648ce9ce59623f7,0xabe7b5c9f447b18,])),
        field_new!(BN382Fr,BigInteger([0x3b870ddd75a8f5a6,0x88a013fa5eb99e9e,0x338fa0e41c0681f7,0x7b0b00ec65ae4bdd,0xd4f372a65a575b18,0xaa3380437b75889,])),
        field_new!(BN382Fr,BigInteger([0x521e150067cb5c34,0xddd0d7000436a545,0x14a8ce8bb8c383f0,0x69569fc5352914be,0xdeaf9132524d6b7c,0x264396fbecf9b1b,])),
        field_new!(BN382Fr,BigInteger([0x827853bab7316f02,0xe03670d1c54321cc,0x8308a184607983e8,0x42c94475385ba780,0xae14e507056295c2,0x16a26fa4e7e62fd1,])),
        field_new!(BN382Fr,BigInteger([0x11477aa5d9556bf4,0x8cd38c9f17782c,0x67224e10043089e,0x7b9e186e002a5d0a,0xbd0d06a4e30ab454,0x19070c7b55fcca60,])),
        field_new!(BN382Fr,BigInteger([0xb8a3fe342ae97f71,0xd3377f9d85582d66,0xc5bbee9e346f3273,0xac772f92c6665426,0x88f6df3d8a8d5188,0x1ac57b7c03d42216,])),
        field_new!(BN382Fr,BigInteger([0x7e132e39e670ca8a,0x39dfc3adc7832470,0x5328abf85799c431,0x7b9466f04a9da855,0x4508d8fac01f97a5,0xb782926d71e68f1,])),
        field_new!(BN382Fr,BigInteger([0x97ccdb5a76fc0aa5,0xd6e16c8dc5f7e206,0x298ee6ab3c71d944,0xe55c955eb38f6c97,0x757bd1d9f746ef50,0x15fbcee358092dc1,])),
        field_new!(BN382Fr,BigInteger([0x6c970df067c60f23,0x6bb6e0cc4b910162,0xbdc1759443633876,0xd076bdae238232fe,0xdcf4f9300f23985e,0x135b5481f8337e9b,])),
        field_new!(BN382Fr,BigInteger([0x785f30aa2ebfde43,0xa9fdfd04c9b75e45,0x3e5e3a0b1e9b0788,0x434d0a8cdd1a5641,0x66425fe572a203f0,0xbf96a3b42165c73,])),
        field_new!(BN382Fr,BigInteger([0x9594db702429dcaa,0x91b8246d933ebd6b,0x8e876a1368e1cf97,0xa58925ee1da6aaec,0x9b7f96d89b2a839f,0x18efadb64440d441,])),
        field_new!(BN382Fr,BigInteger([0x46b7f122949ba9ec,0xc97adc943a3c2ba5,0x617d66835c68741d,0x4c346f4c88c08fa9,0xc9a5dcbe8c604ea8,0x19556bfebba49232,])),
        field_new!(BN382Fr,BigInteger([0x502b786484da94d6,0x70af0f996050c4cf,0x7bc4eb282e92efde,0x3cc13c9fbac2461b,0x76aae8b46515cf81,0x5c08f41e3b03f7a,])),
        field_new!(BN382Fr,BigInteger([0x378d56657a97e2f3,0xddaab891ec53abdc,0xd9b855b3245334b7,0x31264f18f3427d0,0x591a8e1df6c6a4b2,0x13d120a29e3925ef,])),
        field_new!(BN382Fr,BigInteger([0xbecd44432b5f67d1,0xbe0580b15a9da777,0xa779556318e82596,0x2f5f23655b3b75f8,0x3bb479a02e847e10,0xe7ddc705473f20c,])),
        field_new!(BN382Fr,BigInteger([0x6b6e5c0337750e36,0x4b40e5666b9aef6c,0xbf8068c108601ec9,0xb5d92512d2705122,0x7559c4862202b7e4,0x2032a50c2573e6ab,])),
        field_new!(BN382Fr,BigInteger([0xef07946de19d89ec,0xf95925650e8fcb60,0x79f749f54ae1cfbe,0xc8eef18b542e9fd9,0xabeb0b79937ff307,0xc5f28a31dc9d608,])),
        field_new!(BN382Fr,BigInteger([0x1f75ce22dcc06e6e,0x437f87988235efb0,0x9086a7d80524a8d0,0x1dcde226b5818e83,0x9cf4235b8e09ec3a,0xe05c1eb1b19ab1,])),
        field_new!(BN382Fr,BigInteger([0x3c7900051e7388ff,0xed97ec6862b48066,0x94f25f4b0cf7b3eb,0x7287aca0d13a6e82,0xd36f5004effbb985,0x4ec65397a065dea,])),
        field_new!(BN382Fr,BigInteger([0x9e1c766108af505d,0x30c84353674de042,0xc3f1928fdd934cb4,0xc1f38b33f07a84f5,0x8cc237edf14011de,0x8eaba8e51dd779c,])),
        field_new!(BN382Fr,BigInteger([0x48359e687edb8f84,0x8655630a4a68aaab,0x261a90d533b44928,0xc190d058e6c9439a,0x61ac3aafb82ba635,0x1494c0a698e52de5,])),
        field_new!(BN382Fr,BigInteger([0x168d484cb1778d66,0xdcd8c74199b11136,0x17d92329166b4948,0x312770e62ae54976,0x266e16d60a810e5f,0x4496f776caecc65,])),
        field_new!(BN382Fr,BigInteger([0x50a676ea4416eb2e,0xb9627b6dade2e3aa,0xf9e57d095e42f39d,0xb2bcd062c55c2d67,0xe2779837ffcb6e7d,0x1f4839cf7d86f8eb,])),
        field_new!(BN382Fr,BigInteger([0xb12e1716f71ed91b,0x27d8de1c2a8c828e,0xed04b02d5c65a11a,0x36e916c152f6a379,0x44969f87c20a1ece,0x4408d84ceedb145,])),
        field_new!(BN382Fr,BigInteger([0x3154f9da4c52b4a9,0xaa63ca916ce64811,0x2d1ecb52db89a7f0,0x58e997f7dedb0575,0x79e4f19654b47296,0x1d231393a9bdf2f0,])),
        field_new!(BN382Fr,BigInteger([0x4d3fdc53d4999b51,0xd5b9da0c018cc5c0,0x5aac0fee19cb3fd4,0xd57a1fd78266889,0x11bb9ab06b1eb60e,0x4c61d8160747c10,])),
        field_new!(BN382Fr,BigInteger([0x6cf6339972418e98,0x5a8ffb1ed8677882,0x70fa9f55ea7f59eb,0xff82065ddffa952d,0xb64e7b51c8d1c03c,0x12f36ea40e9e5559,])),
        field_new!(BN382Fr,BigInteger([0x53b9ccda6e84a65d,0xe5b7620858f8433c,0x5500b6758ca14ecc,0x2ddea05ee984a57f,0x51edadd520007288,0x12a161d5438c36fa,])),
        field_new!(BN382Fr,BigInteger([0x32516c0c9d2daa27,0xc683c85ae5831a9d,0x7a44cac4c6e04bbb,0x86cc68ca96cb89fa,0xc381e214cc0f1b42,0x23b115b019e27c5e,])),
        field_new!(BN382Fr,BigInteger([0x850e0e6cc19070cc,0x859db81fd43d7e26,0xc1e21f0df3ad5d17,0x3ae161051f2e90dc,0xe056d00f6b00e52a,0x28943f255dcd267,])),
        field_new!(BN382Fr,BigInteger([0x884c8a013c5a2a1a,0xb069415fabf2d0ff,0xa8b420e2c171f47c,0x856ca33a62572e52,0xc0ebde2406ed0987,0xb0ecf3aa6ad07af,])),
        field_new!(BN382Fr,BigInteger([0x8c91e15eb81fbbcf,0x51b38fccd0b6b068,0xf79c6a034f95fe53,0x9626cc95f96659c7,0xcbcccfe8fc30c289,0x19fb71c7406e9a35,])),
        field_new!(BN382Fr,BigInteger([0x7607534731acda95,0x4c511fddb22342ce,0x447ee08d9bb19c72,0xc4822aebfcbc2285,0x24c7063fbc50ef5f,0x111d562483ae1b71,])),
        field_new!(BN382Fr,BigInteger([0xce20bffa022cee7e,0x421f5dfca8b1a5f9,0x1da40c9a61ab178b,0xcc134d7f9db89d45,0xae3253acd9b18c10,0x15ef6c06f33fb6c0,])),
        field_new!(BN382Fr,BigInteger([0x2bc2f7581707e7d8,0xe9a0613d9bc1bd33,0xe24c78647b7f3bbe,0x2839b022c82b9cf8,0xed2921264b022413,0xb381f2aaab65f4d,])),
        field_new!(BN382Fr,BigInteger([0x5e6fee613014710c,0xf34e50300d58d054,0xb00bfa2f5a8bc9f2,0x89ea7a4f518a3edc,0x6b5cc8869511a61,0xfaf777914cb272e,])),
        field_new!(BN382Fr,BigInteger([0x66af9169e9f2de88,0xfdea808705a2514,0x825e10e467fb80dd,0x39c7cb2eb3eac255,0x2e9e945b2024d288,0x19fda157944fbf36,])),
        field_new!(BN382Fr,BigInteger([0x6eefb698748896c4,0xa06c916f6f1c91bf,0x24ff20753d5cf7f4,0x52de1724feaf5af4,0xf25e208ae5af63ca,0x102689f02caa0826,])),
        field_new!(BN382Fr,BigInteger([0x34b7964e39e834cc,0x3e775735d0955f9,0x88e77f88d8ebeb57,0x825b94779cad295,0x46c9b7191d5e4d74,0x19bfe4306a81e64a,])),
        field_new!(BN382Fr,BigInteger([0xa35df64b24f289d2,0x66f092b3aedfc3f7,0x13f874ca29beced6,0x22ea2e7a43d9f226,0x7414416c37789e87,0x3350acacfd72967,])),
        field_new!(BN382Fr,BigInteger([0xd2bf00b533ce6c06,0xb3de8680f43a28c7,0x730e5a196c5fc194,0x8c154245fb46c624,0x82e3241d164de917,0x1902e37228d9d38f,])),
        field_new!(BN382Fr,BigInteger([0xb819eec020508b5c,0xcce6660568f80104,0x692e54d5856c0684,0x5a1080560a8ebbf2,0x56f5ecfbf91dcbb7,0x173a900322be09e4,])),
        field_new!(BN382Fr,BigInteger([0x95969670c277ddb9,0xc826790873bba829,0xfdf70609fa8230b7,0xa169524c68697c76,0x2786e0c33daa49cf,0x29c1b08c55baa58,])),
        field_new!(BN382Fr,BigInteger([0x187ae236b49eaf35,0xa9fe12f04dc3cd94,0x6f8ff94bdf4e131b,0x99228622c82b5e58,0x397a158c03b324a3,0x4e7712aed7462f1,])),
        field_new!(BN382Fr,BigInteger([0x597c7274df3d7d88,0xbb2a2190c7bb2f43,0xc664baf43bb79e84,0x687ee06e701c86fc,0x1e24d31f3dea47fc,0x2075c27b6a16bd0,])),
        field_new!(BN382Fr,BigInteger([0x99d63b17bbdf6ab2,0xb59d593e36a172,0x5ee25a9d8a1b80b4,0xfe38bd87369e3a98,0x47eb9c4c39e18c2f,0x150581e6c9362089,])),
        field_new!(BN382Fr,BigInteger([0x4f63aade947fae5f,0x2c2b5531556b5edf,0x60d8239b8fdf387a,0x2909f8c49bee14da,0xaffac27e2d83dd81,0x193bd69debe9c522,])),
        field_new!(BN382Fr,BigInteger([0xbf5239674121e83e,0xaebe0c92d79df372,0x7578c05576f91f84,0x49ffc0ab4e48fbeb,0x54c23ed221fd9853,0x11d63ec956e107e9,])),
        field_new!(BN382Fr,BigInteger([0xf459c6ac32b8652e,0x528db5f18f6afc99,0x1a502939c4f2fd5d,0x49600c3308ea6a63,0xbf0415f6ba180853,0x1fcdfde2b660527e,])),
        field_new!(BN382Fr,BigInteger([0xe2e903d9d4c808a0,0x7a4defedc70780b4,0xc8d6b3a356d34fbf,0x4544fe079617c918,0x4d0589b6193869e9,0x120c6530412201aa,])),
        field_new!(BN382Fr,BigInteger([0x5f826fc253b59528,0x28449323d7c050ec,0x62aa7b6294a2f139,0xe42cde6fcefbf3dd,0xe6339d9ba1965313,0x1a72b1b95874ddf9,])),
        field_new!(BN382Fr,BigInteger([0xd17eeae9951f047,0xf0dc29eb01d1118a,0x669f981021b78ace,0x8a89559daeea7f91,0x30a09810b5a22c76,0xdf7f160cf9436a4,])),
        field_new!(BN382Fr,BigInteger([0x8be1bdbb1d48b64e,0xc37cfc891cdf1410,0x5d1ddc24edf7692b,0xc15a2ce1f334e6c8,0x3575b82b8470f86e,0x69117702034296a,])),
        field_new!(BN382Fr,BigInteger([0xd625d3dd403286e3,0xd52e788ef0f57130,0x330158b788aec4d8,0x9d2626ec8ea6f809,0xcb27c9558047ac2f,0x2227509862ecc1a0,])),
        field_new!(BN382Fr,BigInteger([0x57cc408927eb6722,0xf8e6c6e2fdc1d5f6,0x6655c3d44b5c16fa,0x518e71c7c9866f1a,0x2fc4aa2db79d1e76,0xef174135a6ea6da,])),
        field_new!(BN382Fr,BigInteger([0x865f134c6a813514,0x7a635641c2514936,0x32eef0d70a72c1db,0x191b7985fbbf4797,0x3f7d8b950abaa75f,0xd66089a58be5673,])),
        field_new!(BN382Fr,BigInteger([0xbb0bff3a43659235,0x81e01781d17d77e2,0x9042478a34860ade,0x9a0a4f52db822381,0x411fc69234f0831,0x18670b6257d14e5f,])),
        field_new!(BN382Fr,BigInteger([0xed1825b47c0970a8,0x6c30c692af42c2dc,0x7170a21067e6ebae,0xa88fce0e1de88878,0xeded4124fd263e5d,0x10cc27dba715fbce,])),
        field_new!(BN382Fr,BigInteger([0xc507cd5ca20ac47e,0x8760b2d002c24bf4,0x7a1a3ee341d2bd31,0xbde7a4dc298733f0,0x59384f9ba681de1a,0x1e61c79fdcbbc92,])),
        field_new!(BN382Fr,BigInteger([0x50ff27fef4648a49,0xf4ffbcb41a25f01a,0x11475e1c50ca75a3,0xc748083328fde991,0xa51978c881dd1657,0x1a8c4560c688e4f7,])),
        field_new!(BN382Fr,BigInteger([0x5669d2e3a299c74b,0x4dc3bcf4ca360bc1,0x79ac21ed9756f463,0xd03312e6a6b66cde,0x7dca20b390eb1db8,0x1011ccb163b1de7d,])),
        field_new!(BN382Fr,BigInteger([0xf1f28a273dc0a4c4,0xdd43c35dcef01c34,0xb2bea8ffd6b04709,0xc5558d2ba68fd50d,0xe904e61565cb64cd,0x113ef43883a21768,])),
        field_new!(BN382Fr,BigInteger([0xb708e32f29816d24,0x23775eff7e90a018,0xe24a63c0e2757005,0x408fe0842baac598,0x4a99ec3cd437fde1,0x17eb1dd58b2b71cd,])),
        field_new!(BN382Fr,BigInteger([0x24190c79caae1c26,0xcd672499c42e8960,0xc1c8b951fc99dece,0xd636eaec9b0139bf,0xfcb633cc250fa9b7,0x1d3001e683da15c8,])),
    ];

    // The MDS matrix constants
    const MDS_CST: &'static [BN382Fr] = &[
        // Constants in Montgomery representation
        field_new!(BN382Fr,BigInteger([0x6ac1a9ca2bfaf672,0x8741e5775336eecd,0xc3542eb56e2ecdbd,0xc060b453f5769f1d,0xa0bfbaaf8550d2f0,0x82244d24068fb84,])),
        field_new!(BN382Fr,BigInteger([0x72f8f2e204bf70bb,0xdfaca0814998d678,0x5bc5bc7dc7efbf60,0x60c7447005c6238c,0x228675fb4e689682,0x1b23a18d15b6e344,])),
        field_new!(BN382Fr,BigInteger([0xef774390a82f9829,0x9794a1188d8dae52,0x8784315795923532,0xc572c69f9cb6de5a,0x59a5a62e6c8ff7fe,0x1fcde0449a9d773b,])),
        field_new!(BN382Fr,BigInteger([0x60259bca5f29a567,0x642332164b5a1c6,0x8c5fc348a776f303,0x4d3fdbbc5c457c5b,0x8d7b0b765f9aab96,0x15754b8d77c2bac,])),
        field_new!(BN382Fr,BigInteger([0xb073f85139114a15,0xc73710f0b2754d34,0x5fec554b012529cd,0xd127ce2c88fe8e59,0x348d6fac251c205d,0x3d62705403fb5c7,])),
        field_new!(BN382Fr,BigInteger([0x8fe5ed1437107ae5,0x3573f33f9cdd0fa1,0xc4f893a2a0ce03a7,0xe96399d2176c06de,0x48e6d3f03abbbcdf,0x22fc5a0e6c275361,])),
        field_new!(BN382Fr,BigInteger([0xf8e3d65ad93901ba,0xbf80d68b79087348,0x986a203c13df0dfd,0x28e6fee273ab8089,0xa0d247b5118c7053,0x13c1fc781c3bc96a,])),
        field_new!(BN382Fr,BigInteger([0xb384b1e3e7890676,0xbf03c31fbdf881ca,0x202d2c8fdd23af75,0xeec6a4e71db93069,0xcd7b6a126c7c5241,0xc0670d904227bbb,])),
        field_new!(BN382Fr,BigInteger([0xb5c9511701fe7e60,0x1d994508bb246d45,0xd516dd8ebf30a39,0xd96940aa566a16bc,0xc613094840067ecb,0xfe933fbef246789,])),
    ];
}

pub type BN382FrQuinticSbox = PoseidonQuinticSBox<BN382Fr, BN382FrPoseidonParameters>;
pub type BN382FrPoseidonHash = PoseidonHash<BN382Fr, BN382FrPoseidonParameters, BN382FrQuinticSbox>;
pub type BN382FrBatchPoseidonHash = PoseidonBatchHash<BN382Fr, BN382FrPoseidonParameters, BN382FrQuinticSbox>;