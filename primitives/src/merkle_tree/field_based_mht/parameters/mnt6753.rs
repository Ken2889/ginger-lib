use algebra::{
    field_new, biginteger::BigInteger768,
    fields::mnt6753::Fr as MNT6753Fr
};

use crate::{
    crh::poseidon::MNT6PoseidonHash,
    FieldBasedMerkleTreePrecomputedEmptyConstants,
};

pub const MNT6753_MHT_POSEIDON_PARAMETERS: FieldBasedMerkleTreePrecomputedEmptyConstants<'static, MNT6PoseidonHash> =
    FieldBasedMerkleTreePrecomputedEmptyConstants {
        nodes: &[
            field_new!(MNT6753Fr,BigInteger768([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])),
            field_new!(MNT6753Fr,BigInteger768([17637649811893425297, 9356568928171551347, 15442933386895351042, 16037249952112432370, 13788858697879839278, 11025667786216957645, 7102709371094193238, 12422915737218740758, 10531053957796416782, 9696092897380549051, 1339040383975805668, 64128018321799])),
            field_new!(MNT6753Fr,BigInteger768([4472923475352101931, 14125459602252897885, 13088438548806363052, 16269053428991819111, 3116242482118239773, 8191706716067520569, 4230313181893216955, 5167780582185616020, 15631071562248952054, 11846663030841039828, 642062297174172342, 296312004800026])),
            field_new!(MNT6753Fr,BigInteger768([17560533737151908951, 7063542403418931348, 9946122940491405418, 7701715352861997786, 9566898456569095206, 5256256878378084730, 9233983441268881659, 6942880360212085679, 6283174021297026980, 8102155274089156953, 2439467320428321035, 332916539951005])),
            field_new!(MNT6753Fr,BigInteger768([5858795400903007273, 7438824890337000111, 11488323460733706521, 2430825815000466084, 1725829885235881856, 15876812446098322793, 17156214869442521015, 5137679012965207550, 9116445458721095545, 4712054789035514492, 14030095712657958516, 179133400783271])),
            field_new!(MNT6753Fr,BigInteger768([9196483772299324859, 2927602375838435979, 16763111848481482763, 17882384337132970051, 17207183906514250255, 9530001320382362332, 3830621480341297746, 4866359965257025230, 16727937285691906509, 7542198491188832218, 8110695628458743283, 465520569394182])),
            field_new!(MNT6753Fr,BigInteger768([10747845174812323570, 2352057383464167932, 1141492571882677871, 1470351414409109323, 10420683829849635095, 15838896170163265003, 15955496784306175007, 4512671111438446024, 14027406595267595230, 4821799888258843127, 8552400658778235926, 90196730269457])),
            field_new!(MNT6753Fr,BigInteger768([5256253866873843525, 272593912443857551, 28470486217631823, 5159435739716868363, 6008486422443066719, 13667749945326593098, 12159573967831293532, 13247815893026277720, 5156136969387447701, 18025485311606231696, 3021473936786719040, 369755762512790])),
            field_new!(MNT6753Fr,BigInteger768([12344211293249999590, 12957596404284010059, 13910609108784582371, 17948699145681135586, 15785513802737509917, 9521697374075267890, 6365430956477394167, 10489625328383467046, 3109920408419137721, 4776466127615241425, 13808572562066969960, 309948976116781])),
            field_new!(MNT6753Fr,BigInteger768([6119070406732032896, 9410219222515712831, 5619723902868157253, 1973644971311309067, 6350780697601099563, 9024750504788049395, 15043082738210571628, 5620029319140107743, 3847387393513625150, 14928494257596235235, 2953722154564751554, 351659788771135])),
            field_new!(MNT6753Fr,BigInteger768([6049475571987158620, 14682333365358852589, 18135530363728134391, 14238712786862549175, 18420038755059004258, 7100569247008813954, 15681379881268007011, 3148544300132614406, 7346490772185170040, 2440588656045554503, 16485398900108052412, 60014821790753])),
            field_new!(MNT6753Fr,BigInteger768([12856661607330728400, 7016632322912905163, 3480013918990612535, 4344326050178292196, 16734656594695639398, 619569984615794816, 508464437174924696, 17238871601243639011, 9357837317046245838, 8883981285570502927, 7265239135733430929, 39139143918093])),
            field_new!(MNT6753Fr,BigInteger768([14817103890877107626, 6987260744665995883, 14570226874221084604, 11556329245783721885, 7466968604079736709, 9776987887571675901, 16458942593670591818, 9816159862029094791, 3921792482916243118, 6716123312977174659, 1710272864040696433, 421734633970436])),
            field_new!(MNT6753Fr,BigInteger768([4282397222691614301, 9879141210547300880, 12086373471014813377, 12666137842608178202, 12136963581046123545, 13264356597674291141, 13279969693572861251, 10611706899587547649, 5822212096659034083, 14127644322758565237, 14315577465274012830, 39177977839243])),
            field_new!(MNT6753Fr,BigInteger768([5728462243094819006, 17630581552464220954, 11320732721357334166, 1900213285723218149, 16241842790685525577, 15426354003830150652, 13204149184110252705, 12782089451147648433, 1732724535640987276, 10481021796229132770, 10419395107867006910, 344012985558625])),
            field_new!(MNT6753Fr,BigInteger768([344683888409415049, 17104079267154355794, 16575788368412272898, 8623293262069993159, 7982910632910187999, 7467718100746598937, 13092614656658983286, 16652493132760118102, 721157856720696161, 13335533611612451260, 781487980213691662, 442787986655123])),
            field_new!(MNT6753Fr,BigInteger768([6074433373638373965, 12098141975132028903, 1772727838370092714, 17302232439660752033, 13973402180971253892, 10747553266078344056, 4629001220352976062, 3362177028682656276, 4093103855723114167, 11999448184397189566, 4836796932935328252, 386630740659090])),
            field_new!(MNT6753Fr,BigInteger768([13014586413437199011, 14604625218698575416, 5071797836894621793, 17933033024926760524, 17079269583255311986, 6087229422530194396, 13294680830864986388, 401049880672557278, 12491328108961811657, 262021736727899607, 4727246708058880707, 110415138534356])),
            field_new!(MNT6753Fr,BigInteger768([1810339956058039811, 5220319720510094406, 13881603660491110179, 13222612110129007479, 6312365029261375458, 4488597311969070097, 3786930340526411451, 3100227749896650684, 17888997887837665338, 11120050721883473292, 17333024085167386788, 122622432905739])),
            field_new!(MNT6753Fr,BigInteger768([12015855797949312766, 15089252312128931938, 4487075872730733012, 11064976590409484842, 7345635811734382058, 6654267483537341812, 7338965532001215980, 8910608120598620104, 11760124634612512865, 16634036057775533219, 3154848179763801, 252988057458120])),
            field_new!(MNT6753Fr,BigInteger768([12844051781387933694, 14867417428795205800, 9706792882858210784, 2837497735373956323, 8708230781562375881, 16216709488172319510, 16685678840904390572, 17518208216783484556, 7106074686008369725, 18119542548943855133, 14132259050522202957, 74750391842824])),
            field_new!(MNT6753Fr,BigInteger768([2095049432688090524, 14022991336226067587, 13064251048943312063, 4930626082426515917, 7398876182738915571, 12675065241304118357, 11599240147379022093, 12104736345308339081, 7326994241467324793, 9543773052250172798, 2775763972445393468, 458168979271920])),
            field_new!(MNT6753Fr,BigInteger768([1946334007581914066, 17651035588256778549, 16514069863291089961, 6837961831333698346, 14290465216201654988, 11695022680475175792, 5272328103994695478, 6615418303775738534, 7306040626339560814, 1068008787604355877, 4115635962454045834, 495898874262831])),
            field_new!(MNT6753Fr,BigInteger768([14402861386561446620, 14792084567357226272, 6866700736595022709, 4113741901118049627, 16974812291891495925, 2591187165974885152, 9652009272067146832, 17945392524410072521, 16355201864774011574, 17722464991226331207, 6711417801116586799, 64077825502541])),
            field_new!(MNT6753Fr,BigInteger768([14064439024053015058, 8311654208515298479, 9104801255536293439, 3435835109271397379, 2712106172220266833, 16109486991502526028, 5651721887369042452, 14572741680048077241, 17167805857692983973, 10790465472671670937, 17136899827689865975, 235713138184448])),
            field_new!(MNT6753Fr,BigInteger768([10921122272069803471, 12577796758815504414, 17894410592699986884, 15650444086007959556, 948214525341676896, 4413473555476543334, 400409551525995658, 9569271116300630353, 14300418054165299370, 2405861297007405656, 8593207143586674229, 317679646497041])),
            field_new!(MNT6753Fr,BigInteger768([5010217285040896027, 6118190716370278919, 5568761447497243608, 7232401845348398675, 11018189049174018358, 9063262008998899553, 15414255187942422510, 15366085234988945047, 749508538410508494, 4179612678808007669, 9379657808494207396, 332004587403462])),
            field_new!(MNT6753Fr,BigInteger768([15596855953553551339, 14558516921801695117, 1716340212069481454, 16931771333182645310, 664561412384369638, 2277135588311724679, 17019393950247019203, 7528389714662451145, 4710861527742606713, 9268887905114908216, 4277691410811219790, 358017827571860])),
            field_new!(MNT6753Fr,BigInteger768([1345110017514752937, 11172153568636292065, 11079027760107165009, 766116359110021478, 16056140398387994894, 3290268012245266281, 4800923857475440103, 2198169219803152265, 7420936784792270326, 772819559725172974, 235282743392278103, 208876952517211])),
            field_new!(MNT6753Fr,BigInteger768([13471797275036477227, 13061727920320491911, 6819174308936409884, 8716139006117964600, 1962085276963290769, 6096628119158067780, 8167753635222191055, 14542801129845756191, 12572804873626916137, 9323731354266459335, 2575323808597388829, 11574582105067])),
            field_new!(MNT6753Fr,BigInteger768([4099487087924561648, 17735253112812409865, 1472196735946662562, 14589900298475437019, 13077017353725781269, 4656951940440280130, 2006510094889487317, 16199931703350800082, 14440178232943249115, 1407142698233581642, 13367748001204569270, 368868378632133])),
            field_new!(MNT6753Fr,BigInteger768([8074651267210831167, 8119908304743691932, 10050269642681585298, 17235916655576462100, 13335057030995613925, 10953418346798654943, 3695463758673253539, 5941835118077151115, 3992757082309531504, 9920313873598345988, 13151267180037628287, 207067907840698])),
            field_new!(MNT6753Fr,BigInteger768([894664452991370310, 16640116934783334734, 14808118850566711269, 6854546902707263589, 4286409562415851882, 6376630963274680056, 1706592727108815514, 2827938002676295743, 4157439222499882505, 8938576560015078325, 17999318348661348728, 34731319506718])),
            field_new!(MNT6753Fr,BigInteger768([11652860094199701250, 3478742230776828196, 10882615542005694703, 3349819079712688914, 8867992918381147826, 18409048493474927536, 11246279017112615234, 9748413453493631722, 17953656205798507701, 15187396101076825886, 11399324590810188311, 260131766860778])),
            field_new!(MNT6753Fr,BigInteger768([1249906864722423399, 12380849303036860652, 9152918792602847508, 8633501350856661146, 9693350457758570990, 14247290248527674449, 17646894536337687694, 4172434561479646685, 14342150478683294750, 7577792009144541865, 4695577900183865210, 317076072551130])),
            field_new!(MNT6753Fr,BigInteger768([8243914980137266903, 12333230796586460241, 14444364149875431527, 10803094216152777629, 4245055689606596787, 11044932568629364169, 11143770400531777907, 9358590092664905825, 4464390783738523435, 10767199047452580923, 15229918729430798984, 462864070917908])),
            field_new!(MNT6753Fr,BigInteger768([1332194145515023222, 5989346566927373592, 2377432556512621922, 7197981111191741919, 8933561838464171794, 14784476823475522561, 8478394278159923626, 5550504370540145528, 9532923115841735693, 14268124095180929026, 13757307827788564501, 122834449169298])),
            field_new!(MNT6753Fr,BigInteger768([14315080839281141763, 12316729172954982736, 12240902985496785994, 15572988659996267515, 2853659555022734346, 6458457554023043088, 18242519349120488704, 9074731373769712100, 16887310820873581593, 10961259943832775631, 7703684579928629068, 172779365404209])),
            field_new!(MNT6753Fr,BigInteger768([404644793350804679, 10645061623026087383, 7037216068474108354, 6875015450266344877, 9691319874633432046, 8981392801744671263, 7935787978429651629, 15636241802405345506, 1798934145016865467, 15862544822185043035, 1853057481023778743, 48582979057739])),
            field_new!(MNT6753Fr,BigInteger768([13841377248024908588, 6443916402067134263, 4121795598949110874, 17604038008411622297, 13539797093572147657, 8129794625753716120, 1778292717222571517, 1274414933390228330, 12302491198307697454, 12915166626799987755, 10282112543429553668, 337540712877314])),
            field_new!(MNT6753Fr,BigInteger768([2623819668573158668, 18068100053054478991, 11510571701283286325, 5846159179552586599, 7116703367486880097, 14386197053801562981, 15156005615023383543, 9383873929378927496, 14930130200844661115, 17345013830483094608, 11202472323720105939, 67169217781307])),
            field_new!(MNT6753Fr,BigInteger768([4403869937029740070, 12780380221027360032, 8411002685782179801, 9673734652350638919, 1271006590149990751, 14713224810005625570, 11720231750293065950, 5216848339135916669, 2768835827765483017, 9531440940757609710, 6191833244911324787, 187122239473111])),
        ],
        merkle_arity: 2,
        max_height: 41,
    };

#[cfg(test)]
mod test {
    use algebra::{
        fields::mnt6753::Fr as MNT6753Fr,
        Field,
    };
    use crate::{
        crh::{
            FieldBasedHash, MNT6PoseidonHash
        },
    };
    use super::MNT6753_MHT_POSEIDON_PARAMETERS;

    #[ignore]
    #[test]
    fn generate_binary_mnt6753_mht_nodes() {
        let mut empty_node = MNT6753_MHT_POSEIDON_PARAMETERS.nodes[0].clone();
        assert_eq!(empty_node, MNT6753Fr::zero());
        let mut digest = MNT6PoseidonHash::init(None);
        for node in MNT6753_MHT_POSEIDON_PARAMETERS.nodes {
            assert_eq!(node, &empty_node);
            empty_node = digest.update(empty_node).update(empty_node).finalize();
            digest.reset(None);
        }
    }
}
