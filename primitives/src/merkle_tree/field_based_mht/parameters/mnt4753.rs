use algebra::{biginteger::BigInteger768, field_new, fields::mnt4753::Fr as MNT4753Fr};

use crate::{
    crh::poseidon::parameters::mnt4753::MNT4PoseidonHash,
    FieldBasedMerkleTreePrecomputedZeroConstants,
};

// PoseidonHash("This represents an empty Merkle Root for a MNT4753PoseidonHash based Merkle Tree.") padded with 0s
pub const MNT4753_PHANTOM_MERKLE_ROOT: MNT4753Fr = field_new!(
    MNT4753Fr,
    BigInteger768([
        13776568879588824265,
        7211554190542477013,
        6228527372657692958,
        5440247819114626778,
        13614791109063536162,
        14611005264246379394,
        10104591396740536371,
        18157835991916950533,
        3122065761218094219,
        17045787444773751417,
        16906993886158454915,
        357538635362377
    ])
);

pub const MNT4753_MHT_POSEIDON_PARAMETERS: FieldBasedMerkleTreePrecomputedZeroConstants<
    'static,
    MNT4PoseidonHash,
> = FieldBasedMerkleTreePrecomputedZeroConstants {
    nodes: &[
        field_new!(
            MNT4753Fr,
            BigInteger768([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                8006651735201630156,
                9690860117920174136,
                17224466678789631133,
                6780594604568324163,
                10846822411885063383,
                7705408890208139333,
                17852453186369903215,
                4603099682590023221,
                6867488836877866745,
                9012707624260102571,
                2160379244411329684,
                405517700872843
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                9009078911095728295,
                16880778409027731807,
                13121109548980524388,
                8671583285772432396,
                1276712593148266536,
                3846166368668027075,
                987365742422813655,
                4133721649779220685,
                18214701760975815806,
                2560296921114197075,
                6735843989315866968,
                258198083137644
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                17950050146492127951,
                16327866259413817165,
                5325612456818009723,
                13032332967517994116,
                11606259928698780021,
                18423757838658996228,
                4947340578531384732,
                11439818895821885783,
                3806664898755278830,
                7632322505775809872,
                2138578042937164240,
                256174925062235
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                3440575764136291984,
                4646597685838725417,
                14120282487422853466,
                51118828334671919,
                5193412418438997247,
                4943684452011438354,
                17459644778321457702,
                3482809443021974704,
                14790384667283994535,
                4282610666874864568,
                11523700099217562075,
                438967134548262
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                7272168453534284373,
                10958105035899260074,
                15576269046001681679,
                14787328550056102708,
                16335226507289463986,
                14720733464497687810,
                7919383887301123260,
                11066567550789535136,
                15975211607681070022,
                10296269259113856382,
                10920143346057771676,
                795252093138
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                826904150116067538,
                10237112221043249725,
                6024061998080125997,
                7753170609339516104,
                2550092909420279384,
                13448074323075115706,
                17602829318749851898,
                8101804824736693879,
                8863089057636595414,
                3661185237686557926,
                6880021529183572516,
                224308704083285
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                14509017355779969101,
                7602547500616040275,
                6086256388237624346,
                4549079082801452129,
                7761772750489326265,
                618337719571335897,
                4128122185318597813,
                9440684808288899728,
                8297543190946064001,
                12538498250612997391,
                7746398219879848372,
                339163394071224
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                14897606205276046121,
                18196472582659531638,
                9919697950629599129,
                17140679205180594759,
                16248442797882106339,
                13146452530658826299,
                16400107791967239768,
                6342701669832629563,
                16711494074981700621,
                6046242811920717474,
                5069759035007581693,
                426056598423805
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                13832717954384852105,
                4777087501933178325,
                10106031147259565671,
                15211034711597743161,
                547067972737459710,
                5316919614969511031,
                13415111780447572134,
                16379829099190731105,
                16908825399490173118,
                16761352258165638563,
                2651363678930579874,
                293001363772891
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                3088196936201215579,
                411195204763091569,
                957689884939256150,
                5344744660544593413,
                9154072722752723086,
                963708121815637048,
                4118424780073651547,
                9918483088405587381,
                6505410768726408322,
                15956201118139961263,
                10672344634186514148,
                425957272776980
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                6890685290309250100,
                10917145531760739102,
                14719211770396917614,
                6836210014783622731,
                9469737138486471242,
                11704140669979867438,
                8610882305834650242,
                4253753287292976407,
                13528843874983492250,
                11051662406992354237,
                16903935879627839586,
                115222354052225
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                8759311244806062395,
                16509615049142117685,
                3506411235897307862,
                7767703220974419464,
                14475472100904919078,
                17766403247755250385,
                13229316555250281859,
                14946820516798057054,
                7340741730994031015,
                15810923291459218960,
                10362079008992189265,
                386980203947789
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                366542987704479593,
                7491087030901403403,
                1748599198260349709,
                6309943162499683466,
                361398753107610192,
                11360939894264079925,
                7626657954954560711,
                17577555707395667460,
                10633632359697441686,
                15817452800923744911,
                403589153351487455,
                54683048474572
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                13154894757714414076,
                3942231991847132064,
                6690438292706701404,
                5187136559389623522,
                11468763560636066712,
                15777209099117347908,
                15557153678423763992,
                9189466820391742192,
                15839277679467339510,
                3459989245352632517,
                11345523455559550518,
                256660346462578
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                8533897467025638584,
                853672783164557803,
                16830135038022363854,
                475486368040139068,
                3260361352581377157,
                4122106333684655466,
                17773998518179370950,
                13641587981503405312,
                3795487074609093445,
                16023611769834333073,
                5337729099241714681,
                493836840226030
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                6552160755121619290,
                2226525113934313527,
                6954790633464422916,
                16957346923365632653,
                13469259751022876076,
                11864187307963093011,
                13238904914713261525,
                15403183584681544051,
                14154916867329423447,
                7986970947670157443,
                18280476418258825294,
                228704311229295
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                13596214878413645653,
                10028406174504822680,
                7845267569665511043,
                3693282426430836518,
                1514235139990352786,
                857984465806563760,
                9585974967955267639,
                18000847279993024473,
                12297125587738349588,
                117029454954467358,
                2338341037152989597,
                303099571637622
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                11048222126519557396,
                2520152213074532505,
                15628570610647977335,
                12805621240223884962,
                11698211466308656146,
                12202519382704857837,
                13072516069182388655,
                13296922864870589056,
                2950220356565398516,
                2151648312638372850,
                7727404783418313044,
                63356747261574
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                1386779273207008297,
                2955015462311940601,
                874818772586304640,
                7123568282054192624,
                14728825476677172503,
                11277308017749846363,
                13887413010534581858,
                1862300501765005774,
                17419843084546291821,
                11829961595472129903,
                16681611922536747530,
                136474265169304
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                10713747124286135864,
                9086161828076021229,
                5555100427996659561,
                1470306338995684623,
                15916644495839627673,
                411527644852328187,
                9429826889012021043,
                14705458484555255968,
                5934062770407641818,
                7683687020052766872,
                15967386600965421401,
                324259340549965
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                2072741438367970421,
                4869279828213690800,
                1875566743164330033,
                590116011439552749,
                5221991567702673154,
                807769010792921136,
                13645737349377176564,
                12513410160470767056,
                13009173784400112441,
                10235087766408319185,
                16937559936578365283,
                263276030266166
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                4189523660368586602,
                6278642172692533845,
                13184214539129358565,
                7147054310905220845,
                4472437898681435196,
                16982789820718370902,
                18121036795751182908,
                18095734241466597416,
                14291779326773236488,
                16926516653577162178,
                17191881770261242965,
                315621916526122
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                8695210000102462032,
                15281091069731234812,
                18034746722218064816,
                3857775695946977987,
                17928559596415409273,
                4066106753497997199,
                4333954571268259110,
                11641807671925441984,
                3155765604983362588,
                7167631261242370462,
                7888315017560439451,
                187213809801377
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                16042571177330299509,
                3430575175704009919,
                13843356378333679723,
                13119015426574444189,
                14427312293676046772,
                7776655594928021097,
                16209496875272471676,
                15025327164498019501,
                629442338631307904,
                1186666011763811140,
                17991343667413250244,
                489750359376125
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                4666757560794445700,
                17895882071873175795,
                14883047586674553252,
                13644409150349351825,
                16830910159664700254,
                14605622783619330462,
                664513908433616482,
                4446784349118490453,
                12446027985342168617,
                3680282527167199670,
                8892860287022047794,
                230448275925393
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                4401327514159998030,
                5039519046495110279,
                8432520625830373109,
                12177216553438111872,
                6215116659635726957,
                1868175308362502793,
                13431583243355157928,
                2598252129090361201,
                15245982355931786796,
                15849910380517498867,
                2533181393696041767,
                394426895967592
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                946220579998252050,
                14535231056231293743,
                18100148845274371163,
                15982549014249841099,
                11616446266506416320,
                2374800414550269618,
                7125887514565359469,
                11177213721427221030,
                6980592791519673351,
                1092813708430335244,
                5226570270038420548,
                275555306376678
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                9909191784808659980,
                7822980706219406110,
                1354544939544130003,
                15056941642501955912,
                14072391732394087652,
                10344801111318233482,
                7352420520801904226,
                9765345188288962489,
                13806780619758456507,
                15541928495496498891,
                13587552134359280965,
                369054404734421
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                734954740240586689,
                3913461705888992416,
                3538814402350625490,
                2015435145345959795,
                17858599047997784687,
                15946369341068671401,
                17605111926286485052,
                15705924544688110409,
                6763684539455285602,
                5871927759490994034,
                11690260275509231658,
                464384432133552
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                13554528009218964275,
                2182733947422982795,
                12171945937773678001,
                6979657033986228132,
                18278526111914765457,
                12988434810330026679,
                7311038473130562404,
                9892640641628910348,
                9509839010239315562,
                17481513471349160818,
                946267090613631893,
                26937341181169
            ])
        ),
        field_new!(
            MNT4753Fr,
            BigInteger768([
                1214525150360138110,
                16730010020447477237,
                2974388837665379820,
                239714683347011625,
                1344568049668497831,
                14614250391340271530,
                8877516492314574160,
                7020608802630085427,
                10105119508116907748,
                15166529063145820970,
                14035625450675726455,
                186843123237636
            ])
        ),
    ],
    merkle_arity: 2,
};

#[cfg(test)]
mod test {

    use super::{MNT4753_MHT_POSEIDON_PARAMETERS, MNT4753_PHANTOM_MERKLE_ROOT};
    use crate::{
        crh::MNT4PoseidonHash,
        merkle_tree::field_based_mht::parameters::{
            generate_mht_empty_nodes, generate_phantom_merkle_root_from_magic_string,
        },
        FieldBasedMerkleTreePrecomputedZeroConstants,
    };
    use algebra::{fields::mnt4753::Fr, Field};

    #[ignore]
    #[test]
    fn test_generate_mnt4753_phantom_merkle_root() {
        let expected_root = generate_phantom_merkle_root_from_magic_string::<Fr, MNT4PoseidonHash>(
            "This represents an empty Merkle Root for a MNT4753PoseidonHash based Merkle Tree.",
        );
        assert_eq!(expected_root, MNT4753_PHANTOM_MERKLE_ROOT);
    }

    #[ignore]
    #[test]
    fn test_generate_binary_mnt4753_mht_empty_nodes() {
        let merkle_arity = 2;
        let max_height = 32;

        let empty_nodes =
            generate_mht_empty_nodes::<Fr, MNT4PoseidonHash>(merkle_arity, max_height, Fr::zero());
        assert_eq!(empty_nodes.len(), max_height);

        let params = FieldBasedMerkleTreePrecomputedZeroConstants::<MNT4PoseidonHash> {
            nodes: empty_nodes.as_slice(),
            merkle_arity,
        };
        assert_eq!(params, MNT4753_MHT_POSEIDON_PARAMETERS)
    }
}
