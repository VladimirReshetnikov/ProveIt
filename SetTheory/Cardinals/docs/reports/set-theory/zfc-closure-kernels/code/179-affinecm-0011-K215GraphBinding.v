From Coq Require Import Lists.List Bool Arith NArith.
From K230 Require Import RM RMEquiv.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import PathCodec NormalizedBisim DrainCore CoreContraction K215DrainData SourceGraphBridge.
Import ListNotations.

Definition locations_source : K215DrainData.tree positive :=
(Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 0%N 8%positive
 Empty) 2%N 18%positive
 Empty) 7%N 46%positive
 (Branch (Branch Empty 9%N 33%positive
 Empty) 11%N 561%positive
 Empty)) 13%N 689%positive
 (Branch (Branch (Branch Empty 17%N 41%positive
 Empty) 20%N 21%positive
 Empty) 23%N 19%positive
 (Branch (Branch Empty 24%N 139%positive
 Empty) 25%N 1099%positive
 Empty))) 26%N 66123%positive
 (Branch (Branch (Branch (Branch Empty 29%N 148043%positive
 Empty) 32%N 574027%positive
 Empty) 36%N 705099%positive
 (Branch (Branch Empty 38%N 5685835%positive
 Empty) 42%N 377419%positive
 Empty)) 45%N 74315%positive
 (Branch (Branch (Branch Empty 49%N 90699%positive
 Empty) 52%N 70219%positive
 Empty) 55%N 152139%positive
 (Branch Empty 58%N 578123%positive
 Empty)))) 62%N 709195%positive
 (Branch (Branch (Branch (Branch (Branch Empty 64%N 5689931%positive
 Empty) 68%N 381515%positive
 Empty) 71%N 78411%positive
 (Branch (Branch Empty 75%N 94795%positive
 Empty) 78%N 68171%positive
 Empty)) 80%N 1149515%positive
 (Branch (Branch (Branch Empty 82%N 1411659%positive
 Empty) 86%N 84555%positive
 Empty) 89%N 141899%positive
 (Branch Empty 93%N 174667%positive
 Empty))) 95%N 1419851%positive
 (Branch (Branch (Branch (Branch Empty 99%N 92747%positive
 Empty) 107%N 67147%positive
 Empty) 110%N 149067%positive
 (Branch (Branch Empty 113%N 575051%positive
 Empty) 117%N 706123%positive
 Empty)) 119%N 5686859%positive
 (Branch (Branch (Branch Empty 123%N 378443%positive
 Empty) 126%N 75339%positive
 Empty) 130%N 91723%positive
 (Branch Empty 133%N 71243%positive
 Empty))))) 136%N 153163%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 139%N 579147%positive
 Empty) 143%N 710219%positive
 Empty) 145%N 5690955%positive
 (Branch (Branch Empty 149%N 382539%positive
 Empty) 152%N 79435%positive
 Empty)) 156%N 95819%positive
 (Branch (Branch (Branch Empty 159%N 265803%positive
 Empty) 161%N 4591179%positive
 Empty) 163%N 5639755%positive
 (Branch (Branch Empty 167%N 331339%positive
 Empty) 170%N 167499%positive
 Empty))) 173%N 544331%positive
 (Branch (Branch (Branch (Branch Empty 175%N 9195083%positive
 Empty) 177%N 11292235%positive
 Empty) 181%N 675403%positive
 (Branch (Branch Empty 184%N 1134155%positive
 Empty) 188%N 1396299%positive
 Empty)) 190%N 11357771%positive
 (Branch (Branch (Branch Empty 194%N 740939%positive
 Empty) 200%N 2149963%positive
 Empty) 202%N 36752971%positive
 (Branch Empty 204%N 45141579%positive
 Empty)))) 208%N 2674251%positive
 (Branch (Branch (Branch (Branch (Branch Empty 211%N 2412107%positive
 Empty) 214%N 9227851%positive
 Empty) 217%N 19713611%positive
 (Branch (Branch Empty 220%N 74239563%positive
 Empty) 224%N 91016779%positive
 Empty)) 226%N 728550987%positive
 (Branch (Branch (Branch Empty 230%N 49073739%positive
 Empty) 233%N 10276427%positive
 Empty) 237%N 12373579%positive
 (Branch Empty 240%N 2281035%positive
 Empty))) 242%N 36884043%positive
 (Branch (Branch (Branch (Branch Empty 244%N 45272651%positive
 Empty) 248%N 2805323%positive
 Empty) 251%N 4640331%positive
 (Branch (Branch Empty 255%N 5688907%positive
 Empty) 257%N 45534795%positive
 Empty)) 261%N 3067467%positive
 (Branch (Branch (Branch Empty 267%N 2215499%positive
 Empty) 270%N 4836939%positive
 Empty) 273%N 18468427%positive
 (Branch Empty 277%N 22662731%positive
 Empty)))))) 279%N 182046283%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 283%N 12176971%positive
 Empty) 286%N 2477643%positive
 Empty) 290%N 3001931%positive
 (Branch (Branch Empty 293%N 2346571%positive
 Empty) 296%N 4968011%positive
 Empty)) 299%N 18599499%positive
 (Branch (Branch (Branch Empty 303%N 22793803%positive
 Empty) 305%N 182177355%positive
 Empty) 309%N 12308043%positive
 (Branch (Branch Empty 312%N 2608715%positive
 Empty) 316%N 3133003%positive
 Empty))) 319%N 1060427%positive
 (Branch (Branch (Branch (Branch Empty 321%N 18361931%positive
 Empty) 323%N 22556235%positive
 Empty) 327%N 1322571%positive
 (Branch (Branch Empty 330%N 2240075%positive
 Empty) 334%N 2764363%positive
 Empty)) 336%N 22687307%positive
 (Branch (Branch (Branch Empty 340%N 1453643%positive
 Empty) 346%N 2174539%positive
 Empty) 349%N 4795979%positive
 (Branch Empty 352%N 18427467%positive
 Empty)))) 356%N 22621771%positive
 (Branch (Branch (Branch (Branch (Branch Empty 358%N 182005323%positive
 Empty) 362%N 12136011%positive
 Empty) 365%N 2436683%positive
 (Branch (Branch Empty 369%N 2960971%positive
 Empty) 372%N 2305611%positive
 Empty)) 375%N 4927051%positive
 (Branch (Branch (Branch Empty 378%N 18558539%positive
 Empty) 382%N 22752843%positive
 Empty) 384%N 182136395%positive
 (Branch Empty 388%N 12267083%positive
 Empty))) 391%N 2567755%positive
 (Branch (Branch (Branch (Branch Empty 395%N 3092043%positive
 Empty) 398%N 4238923%positive
 Empty) 400%N 73444939%positive
 (Branch (Branch Empty 402%N 90222155%positive
 Empty) 406%N 5287499%positive
 Empty)) 409%N 8957515%positive
 (Branch (Branch (Branch Empty 413%N 11054667%positive
 Empty) 415%N 90746443%positive
 Empty) 419%N 5811787%positive
 (Branch Empty 425%N 4501067%positive
 Empty))))) 427%N 73707083%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 429%N 90484299%positive
 Empty) 433%N 5549643%positive
 Empty) 436%N 9219659%positive
 (Branch (Branch Empty 440%N 11316811%positive
 Empty) 442%N 91008587%positive
 Empty)) 446%N 6073931%positive
 (Branch (Branch (Branch Empty 452%N 8564299%positive
 Empty) 454%N 146976331%positive
 Empty) 456%N 180530763%positive
 (Branch Empty 460%N 10661451%positive
 Empty))) 463%N 18001483%positive
 (Branch (Branch (Branch (Branch Empty 467%N 22195787%positive
 Empty) 469%N 181579339%positive
 Empty) 473%N 11710027%positive
 (Branch (Branch Empty 479%N 67808843%positive
 Empty) 482%N 151694923%positive
 Empty)) 485%N 587902539%positive
 (Branch (Branch (Branch Empty 489%N 722120267%positive
 Empty) 491%N 5822393931%positive
 Empty) 495%N 386575947%positive
 (Branch Empty 498%N 76197451%positive
 Empty)))) 502%N 92974667%positive
 (Branch (Branch (Branch (Branch (Branch Empty 505%N 72003147%positive
 Empty) 508%N 155889227%positive
 Empty) 511%N 592096843%positive
 (Branch (Branch Empty 515%N 726314571%positive
 Empty) 517%N 5826588235%positive
 Empty)) 521%N 390770251%positive
 (Branch (Branch (Branch Empty 524%N 80391755%positive
 Empty) 528%N 97168971%positive
 Empty) 531%N 69905995%positive
 (Branch Empty 533%N 1177202251%positive
 Empty))) 535%N 1445637707%positive
 (Branch (Branch (Branch (Branch Empty 539%N 86683211%positive
 Empty) 542%N 145403467%positive
 Empty) 546%N 178957899%positive
 (Branch (Branch Empty 548%N 1454026315%positive
 Empty) 552%N 95071819%positive
 Empty)) 561%N 138063435%positive
 (Branch (Branch (Branch Empty 564%N 305835595%positive
 Empty) 567%N 1178250827%positive
 Empty) 571%N 1446686283%positive
 (Branch Empty 573%N 11647233611%positive
 Empty))))))) 577%N 775597643%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 580%N 154840651%positive
 Empty) 584%N 188395083%positive
 Empty) 587%N 146452043%positive
 (Branch (Branch Empty 590%N 314224203%positive
 Empty) 593%N 1186639435%positive
 Empty)) 597%N 1455074891%positive
 (Branch (Branch (Branch Empty 599%N 11655622219%positive
 Empty) 603%N 783986251%positive
 Empty) 606%N 163229259%positive
 (Branch (Branch Empty 610%N 196783691%positive
 Empty) 613%N 142257739%positive
 Empty))) 615%N 2356850251%positive
 (Branch (Branch (Branch (Branch Empty 617%N 2893721163%positive
 Empty) 621%N 175812171%positive
 Empty) 624%N 293252683%positive
 (Branch (Branch Empty 628%N 360361547%positive
 Empty) 630%N 2910498379%positive
 Empty)) 634%N 192589387%positive
 (Branch (Branch (Branch Empty 643%N 1082568267%positive
 Empty) 646%N 2424745547%positive
 Empty) 649%N 9404067403%positive
 (Branch Empty 653%N 11551551051%positive
 Empty)))) 655%N 93155929675%positive
 (Branch (Branch (Branch (Branch (Branch Empty 659%N 6182841931%positive
 Empty) 662%N 1216785995%positive
 Empty) 666%N 1485221451%positive
 (Branch (Branch Empty 669%N 1149677131%positive
 Empty) 672%N 2491854411%positive
 Empty)) 675%N 9471176267%positive
 (Branch (Branch (Branch Empty 679%N 11618659915%positive
 Empty) 681%N 93223038539%positive
 Empty) 685%N 6249950795%positive
 (Branch Empty 688%N 1283894859%positive
 Empty))) 692%N 1552330315%positive
 (Branch (Branch (Branch (Branch Empty 695%N 1116122699%positive
 Empty) 697%N 18832862795%positive
 Empty) 699%N 23127830091%positive
 (Branch (Branch Empty 703%N 1384558155%positive
 Empty) 706%N 2324082251%positive
 Empty)) 710%N 2860953163%positive
 (Branch (Branch (Branch Empty 712%N 23262047819%positive
 Empty) 716%N 1518775883%positive
 Empty) 723%N 2173087307%positive
 (Branch Empty 726%N 4857441867%positive
 Empty))))) 729%N 18816085579%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 733%N 23111052875%positive
 Empty) 735%N 186319810123%positive
 Empty) 739%N 12373634635%positive
 (Branch (Branch Empty 742%N 2441522763%positive
 Empty) 746%N 2978393675%positive
 Empty)) 749%N 2307305035%positive
 (Branch (Branch (Branch Empty 752%N 4991659595%positive
 Empty) 755%N 18950303307%positive
 Empty) 759%N 23245270603%positive
 (Branch Empty 761%N 186454027851%positive
 Empty))) 765%N 12507852363%positive
 (Branch (Branch (Branch (Branch Empty 768%N 2575740491%positive
 Empty) 772%N 3112611403%positive
 Empty) 775%N 2240196171%positive
 (Branch (Branch Empty 777%N 37673676363%positive
 Empty) 779%N 46263610955%positive
 Empty)) 783%N 2777067083%positive
 (Branch (Branch (Branch Empty 786%N 4656115275%positive
 Empty) 790%N 5729857099%positive
 Empty) 792%N 46532046411%positive
 (Branch Empty 796%N 3045502539%positive
 Empty)))) 805%N 273067595%positive
 (Branch (Branch (Branch (Branch (Branch Empty 807%N 4702252619%positive
 Empty) 809%N 5775994443%positive
 Empty) 813%N 340176459%positive
 (Branch (Branch Empty 816%N 575057483%positive
 Empty) 820%N 709275211%positive
 Empty)) 822%N 5809548875%positive
 (Branch (Branch (Branch Empty 826%N 373730891%positive
 Empty) 834%N 1086762571%positive
 Empty) 836%N 18803502667%positive
 (Branch Empty 838%N 23098469963%positive
 Empty))) 842%N 1355198027%positive
 (Branch (Branch (Branch (Branch Empty 845%N 2294722123%positive
 Empty) 849%N 2831593035%positive
 Empty) 851%N 23232687691%positive
 (Branch (Branch Empty 855%N 1489415755%positive
 Empty) 861%N 1153871435%positive
 Empty)) 863%N 18870611531%positive
 (Branch (Branch (Branch Empty 865%N 23165578827%positive
 Empty) 869%N 1422306891%positive
 Empty) 872%N 2361830987%positive
 (Branch Empty 876%N 2898701899%positive
 Empty)))))) 878%N 23299796555%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 882%N 1556524619%positive
 Empty) 888%N 583446091%positive
 Empty) 891%N 1254534731%positive
 (Branch (Branch Empty 894%N 4744195659%positive
 Empty) 898%N 5817937483%positive
 Empty)) 900%N 46620126795%positive
 (Branch (Branch (Branch Empty 904%N 3133582923%positive
 Empty) 907%N 650554955%positive
 Empty) 911%N 784772683%positive
 (Branch (Branch Empty 914%N 2177281611%positive
 Empty) 917%N 4861636171%positive
 Empty))) 920%N 18820279883%positive
 (Branch (Branch (Branch (Branch Empty 924%N 23115247179%positive
 Empty) 926%N 186324004427%positive
 Empty) 930%N 12377828939%positive
 (Branch (Branch Empty 933%N 2445717067%positive
 Empty) 937%N 2982587979%positive
 Empty)) 940%N 2311499339%positive
 (Branch (Branch (Branch Empty 943%N 4995853899%positive
 Empty) 946%N 18954497611%positive
 Empty) 950%N 23249464907%positive
 (Branch Empty 952%N 186458222155%positive
 Empty)))) 956%N 12512046667%positive
 (Branch (Branch (Branch (Branch (Branch Empty 959%N 2579934795%positive
 Empty) 963%N 3116805707%positive
 Empty) 966%N 2244390475%positive
 (Branch (Branch Empty 968%N 37677870667%positive
 Empty) 970%N 46267805259%positive
 Empty)) 974%N 2781261387%positive
 (Branch (Branch (Branch Empty 977%N 4660309579%positive
 Empty) 981%N 5734051403%positive
 Empty) 983%N 46536240715%positive
 (Branch Empty 987%N 3049696843%positive
 Empty))) 995%N 2210836043%positive
 (Branch (Branch (Branch (Branch Empty 998%N 4895190603%positive
 Empty) 1001%N 18853834315%positive
 Empty) 1005%N 23148801611%positive
 (Branch (Branch Empty 1007%N 186357558859%positive
 Empty) 1011%N 12411383371%positive
 Empty)) 1015%N 8787504715%positive
 (Branch (Branch (Branch Empty 1017%N 150521425483%positive
 Empty) 1019%N 184881163851%positive
 Empty) 1023%N 10934988363%positive
 (Branch Empty 1026%N 18451181131%positive
 Empty))))) 1030%N 22746148427%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1032%N 185954905675%positive
 Empty) 1036%N 12008730187%positive
 Empty) 1042%N 17914310219%positive
 (Branch (Branch Empty 1044%N 301382151755%positive
 Empty) 1046%N 370101628491%positive
 Empty)) 1050%N 22209277515%positive
 (Branch (Branch (Branch Empty 1053%N 37241663051%positive
 Empty) 1057%N 45831597643%positive
 Empty) 1059%N 372249112139%positive
 (Branch Empty 1063%N 24356761163%positive
 Empty))) 1071%N 9055940171%positive
 (Branch (Branch (Branch (Branch Empty 1074%N 19793358411%positive
 Empty) 1077%N 75627933259%positive
 Empty) 1081%N 92807802443%positive
 (Branch (Branch Empty 1083%N 745642831435%positive
 Empty) 1087%N 49858129483%positive
 Empty)) 1091%N 9592811083%positive
 (Branch (Branch (Branch Empty 1093%N 151326731851%positive
 Empty) 1095%N 185686470219%positive
 Empty) 1099%N 11740294731%positive
 (Branch Empty 1102%N 19256487499%positive
 Empty)))) 1106%N 23551454795%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1108%N 186760212043%positive
 Empty) 1112%N 12814036555%positive
 Empty) 1118%N 1204203083%positive
 (Branch (Branch Empty 1121%N 2546380363%positive
 Empty) 1124%N 9525702219%positive
 Empty)) 1128%N 11673185867%positive
 (Branch (Branch (Branch Empty 1130%N 93277564491%positive
 Empty) 1134%N 6304476747%positive
 Empty) 1137%N 1338420811%positive
 (Branch Empty 1141%N 1606856267%positive
 Empty))) 1144%N 270970443%positive
 (Branch (Branch (Branch (Branch Empty 1146%N 4700155467%positive
 Empty) 1148%N 5773897291%positive
 Empty) 1152%N 338079307%positive
 (Branch (Branch Empty 1155%N 572960331%positive
 Empty) 1159%N 707178059%positive
 Empty)) 1161%N 5807451723%positive
 (Branch (Branch (Branch Empty 1165%N 371633739%positive
 Empty) 1171%N 2166795851%positive
 Empty) 1174%N 4851150411%positive
 (Branch Empty 1177%N 18809794123%positive
 Empty)))))))) 1181%N 23104761419%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1183%N 186313518667%positive
 Empty) 1187%N 12367343179%positive
 Empty) 1190%N 2435231307%positive
 (Branch (Branch Empty 1194%N 2972102219%positive
 Empty) 1197%N 2301013579%positive
 Empty)) 1200%N 4985368139%positive
 (Branch (Branch (Branch Empty 1203%N 18944011851%positive
 Empty) 1207%N 23238979147%positive
 Empty) 1209%N 186447736395%positive
 (Branch (Branch Empty 1213%N 12501560907%positive
 Empty) 1216%N 2569449035%positive
 Empty))) 1220%N 3106319947%positive
 (Branch (Branch (Branch (Branch Empty 1223%N 2233904715%positive
 Empty) 1225%N 37667384907%positive
 Empty) 1227%N 46257319499%positive
 (Branch (Branch Empty 1231%N 2770775627%positive
 Empty) 1234%N 4649823819%positive
 Empty)) 1238%N 5723565643%positive
 (Branch (Branch (Branch Empty 1240%N 46525754955%positive
 Empty) 1244%N 3039211083%positive
 Empty) 1253%N 4414942795%positive
 (Branch Empty 1256%N 9783651915%positive
 Empty)))) 1259%N 37700939339%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1263%N 46290873931%positive
 Empty) 1265%N 372708388427%positive
 Empty) 1269%N 24816037451%positive
 (Branch (Branch Empty 1272%N 4951813707%positive
 Empty) 1276%N 6025555531%positive
 Empty)) 1279%N 4683378251%positive
 (Branch (Branch (Branch Empty 1282%N 10052087371%positive
 Empty) 1285%N 37969374795%positive
 Empty) 1289%N 46559309387%positive
 (Branch Empty 1291%N 372976823883%positive
 Empty))) 1295%N 25084472907%positive
 (Branch (Branch (Branch (Branch Empty 1298%N 5220249163%positive
 Empty) 1302%N 6293990987%positive
 Empty) 1305%N 4549160523%positive
 (Branch (Branch Empty 1307%N 75416120907%positive
 Empty) 1309%N 92595990091%positive
 Empty)) 1313%N 5622902347%positive
 (Branch (Branch (Branch Empty 1316%N 9380998731%positive
 Empty) 1320%N 11528482379%positive
 Empty) 1322%N 93132861003%positive
 (Branch Empty 1326%N 6159773259%positive
 Empty))))) 1333%N 1084665419%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1336%N 2426842699%positive
 Empty) 1339%N 9406164555%positive
 Empty) 1343%N 11553648203%positive
 (Branch (Branch Empty 1345%N 93158026827%positive
 Empty) 1349%N 6184939083%positive
 Empty)) 1352%N 1218883147%positive
 (Branch (Branch (Branch Empty 1356%N 1487318603%positive
 Empty) 1359%N 1151774283%positive
 Empty) 1362%N 2493951563%positive
 (Branch (Branch Empty 1365%N 9473273419%positive
 Empty) 1369%N 11620757067%positive
 Empty))) 1371%N 93225135691%positive
 (Branch (Branch (Branch (Branch Empty 1375%N 6252047947%positive
 Empty) 1378%N 1285992011%positive
 Empty) 1382%N 1554427467%positive
 (Branch (Branch Empty 1385%N 1118219851%positive
 Empty) 1387%N 18834959947%positive
 Empty)) 1389%N 23129927243%positive
 (Branch (Branch (Branch Empty 1393%N 1386655307%positive
 Empty) 1396%N 2326179403%positive
 Empty) 1400%N 2863050315%positive
 (Branch Empty 1402%N 23264144971%positive
 Empty)))) 1406%N 1520873035%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1413%N 2175184459%positive
 Empty) 1415%N 37608664651%positive
 Empty) 1417%N 46198599243%positive
 (Branch (Branch Empty 1421%N 2712055371%positive
 Empty) 1424%N 4591103563%positive
 Empty)) 1428%N 5664845387%positive
 (Branch (Branch (Branch Empty 1430%N 46467034699%positive
 Empty) 1434%N 2980490827%positive
 Empty) 1440%N 2309402187%positive
 (Branch Empty 1442%N 37742882379%positive
 Empty))) 1444%N 46332816971%positive
 (Branch (Branch (Branch (Branch Empty 1448%N 2846273099%positive
 Empty) 1451%N 4725321291%positive
 Empty) 1455%N 5799063115%positive
 (Branch (Branch Empty 1457%N 46601252427%positive
 Empty) 1461%N 3114708555%positive
 Empty)) 1467%N 1168551499%positive
 (Branch (Branch (Branch Empty 1470%N 2510728779%positive
 Empty) 1473%N 9490050635%positive
 Empty) 1477%N 11637534283%positive
 (Branch Empty 1479%N 93241912907%positive
 Empty)))))) 1483%N 6268825163%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1486%N 1302769227%positive
 Empty) 1490%N 1571204683%positive
 Empty) 1493%N 1134997067%positive
 (Branch (Branch Empty 1496%N 2477174347%positive
 Empty) 1499%N 9456496203%positive
 Empty)) 1503%N 11603979851%positive
 (Branch (Branch (Branch Empty 1505%N 93208358475%positive
 Empty) 1509%N 6235270731%positive
 Empty) 1512%N 1269214795%positive
 (Branch (Branch Empty 1516%N 1537650251%positive
 Empty) 1519%N 1202105931%positive
 Empty))) 1522%N 2544283211%positive
 (Branch (Branch (Branch (Branch Empty 1525%N 9523605067%positive
 Empty) 1529%N 11671088715%positive
 Empty) 1531%N 93275467339%positive
 (Branch (Branch Empty 1535%N 6302379595%positive
 Empty) 1538%N 1336323659%positive
 Empty)) 1542%N 1604759115%positive
 (Branch (Branch (Branch Empty 1545%N 543600203%positive
 Empty) 1547%N 9401970251%positive
 Empty) 1549%N 11549453899%positive
 (Branch Empty 1553%N 677817931%positive
 Empty)))) 1556%N 1147579979%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1560%N 1416015435%positive
 Empty) 1562%N 11616562763%positive
 Empty) 1566%N 744926795%positive
 (Branch (Branch Empty 1574%N 291941963%positive
 Empty) 1576%N 4721126987%positive
 Empty)) 1578%N 5794868811%positive
 (Branch (Branch (Branch Empty 1582%N 359050827%positive
 Empty) 1585%N 593931851%positive
 Empty) 1589%N 728149579%positive
 (Branch Empty 1591%N 5828423243%positive
 Empty))) 1595%N 392605259%positive
 (Branch (Branch (Branch (Branch Empty 1603%N 34643291723%positive
 Empty) 1606%N 77592964683%positive
 Empty) 1609%N 300931264075%positive
 (Branch (Branch Empty 1613%N 369650740811%positive
 Empty) 1615%N 2980990856779%positive
 Empty)) 1619%N 197852048971%positive
 (Branch (Branch (Branch Empty 1622%N 38938259019%positive
 Empty) 1626%N 47528193611%positive
 Empty) 1629%N 277308943947%positive
 (Branch Empty 1632%N 620906327627%positive
 Empty))))) 1635%N 2407612722763%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1639%N 2957368536651%positive
 Empty) 1641%N 23848089464395%positive
 Empty) 1645%N 1582979001931%positive
 (Branch (Branch Empty 1648%N 311668682315%positive
 Empty) 1652%N 380388159051%positive
 Empty)) 1655%N 294488813131%positive
 (Branch (Branch (Branch Empty 1658%N 638086196811%positive
 Empty) 1661%N 2424792591947%positive
 Empty) 1665%N 2974548405835%positive
 (Branch Empty 1667%N 23865269333579%positive
 Empty))) 1671%N 1600158871115%positive
 (Branch (Branch (Branch (Branch Empty 1674%N 328848551499%positive
 Empty) 1678%N 397568028235%positive
 Empty) 1681%N 285898878539%positive
 (Branch (Branch Empty 1683%N 4821384343115%positive
 Empty) 1685%N 5920895970891%positive
 Empty)) 1689%N 354618355275%positive
 (Branch (Branch (Branch Empty 1692%N 595136523851%positive
 Empty) 1696%N 732575477323%positive
 Empty) 1698%N 5955255709259%positive
 (Branch Empty 1702%N 388978093643%positive
 Empty)))) 1710%N 556481818187%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1712%N 9627452747339%positive
 Empty) 1714%N 11826476002891%positive
 Empty) 1718%N 693920771659%positive
 (Branch (Branch Empty 1721%N 1174957108811%positive
 Empty) 1725%N 1449835015755%positive
 Empty)) 1727%N 11895195479627%positive
 (Branch (Branch (Branch Empty 1731%N 762640248395%positive
 Empty) 1739%N 298783780427%positive
 Empty) 1741%N 4834269245003%positive
 (Branch Empty 1743%N 5933780872779%positive
 Empty))) 1747%N 367503257163%positive
 (Branch (Branch (Branch (Branch Empty 1750%N 608021425739%positive
 Empty) 1754%N 745460379211%positive
 Empty) 1756%N 5968140611147%positive
 (Branch (Branch Empty 1760%N 401862995531%positive
 Empty) 1766%N 1114827566667%positive
 Empty)) 1769%N 2489217101387%positive
 (Branch (Branch (Branch Empty 1772%N 9636042681931%positive
 Empty) 1776%N 11835065937483%positive
 Empty) 1778%N 95397949648459%positive
 (Branch Empty 1782%N 6337507798603%positive
 Empty))))))) 1785%N 1252266520139%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1789%N 1527144427083%positive
 Empty) 1792%N 1183547043403%positive
 Empty) 1795%N 2557936578123%positive
 (Branch (Branch Empty 1798%N 9704762158667%positive
 Empty) 1802%N 11903785414219%positive
 Empty)) 1804%N 95466669125195%positive
 (Branch (Branch (Branch Empty 1808%N 6406227275339%positive
 Empty) 1811%N 1320985996875%positive
 Empty) 1815%N 1595863903819%positive
 (Branch (Branch Empty 1818%N 1149187305035%positive
 Empty) 1820%N 19291129163339%positive
 Empty))) 1822%N 23689175674443%positive
 (Branch (Branch (Branch (Branch Empty 1826%N 1424065211979%positive
 Empty) 1829%N 2386137886283%positive
 Empty) 1833%N 2935893700171%positive
 (Branch (Branch Empty 1835%N 23826614627915%positive
 Empty) 1839%N 1561504165451%positive
 Empty)) 1848%N 138796248651%positive
 (Branch (Branch (Branch Empty 1851%N 310594940491%positive
 Empty) 1854%N 1203948138059%positive
 Empty) 1858%N 1478826045003%positive
 (Branch Empty 1860%N 11924186508875%positive
 Empty)))) 1864%N 791631277643%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1867%N 155976117835%positive
 Empty) 1871%N 190335856203%positive
 Empty) 1874%N 147386183243%positive
 (Branch (Branch Empty 1877%N 319184875083%positive
 Empty) 1880%N 1212538072651%positive
 Empty)) 1884%N 1487415979595%positive
 (Branch (Branch (Branch Empty 1886%N 11932776443467%positive
 Empty) 1890%N 800221212235%positive
 Empty) 1893%N 164566052427%positive
 (Branch Empty 1897%N 198925790795%positive
 Empty))) 1900%N 143091215947%positive
 (Branch (Branch (Branch (Branch Empty 1902%N 2410833948235%positive
 Empty) 1904%N 2960589762123%positive
 Empty) 1908%N 177450954315%positive
 (Branch (Branch Empty 1911%N 297710038603%positive
 Empty) 1915%N 366429515339%positive
 Empty)) 1917%N 2977769631307%positive
 (Branch (Branch (Branch Empty 1921%N 194630823499%positive
 Empty) 1928%N 140943732299%positive
 Empty) 1931%N 312742424139%positive
 (Branch Empty 1934%N 1206095621707%positive
 Empty))))) 1938%N 1480973528651%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1940%N 11926333992523%positive
 Empty) 1944%N 793778761291%positive
 Empty) 1947%N 158123601483%positive
 (Branch (Branch Empty 1951%N 192483339851%positive
 Empty) 1954%N 149533666891%positive
 Empty)) 1957%N 321332358731%positive
 (Branch (Branch (Branch Empty 1960%N 1214685556299%positive
 Empty) 1964%N 1489563463243%positive
 Empty) 1966%N 11934923927115%positive
 (Branch Empty 1970%N 802368695883%positive
 Empty))) 1973%N 166713536075%positive
 (Branch (Branch (Branch (Branch Empty 1977%N 201073274443%positive
 Empty) 1980%N 145238699595%positive
 Empty) 1982%N 2412981431883%positive
 (Branch (Branch Empty 1984%N 2962737245771%positive
 Empty) 1988%N 179598437963%positive
 Empty)) 1991%N 299857522251%positive
 (Branch (Branch (Branch Empty 1995%N 368576998987%positive
 Empty) 1997%N 2979917114955%positive
 Empty) 2001%N 196778307147%positive
 (Branch Empty 2008%N 69539901003%positive
 Empty)))) 2010%N 1203411267147%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2012%N 1478289174091%positive
 Empty) 2016%N 86719770187%positive
 Empty) 2019%N 146849312331%positive
 (Branch (Branch Empty 2023%N 181209050699%positive
 Empty) 2025%N 1486879108683%positive
 Empty)) 2029%N 95309704779%positive
 (Branch (Branch (Branch Empty 2035%N 73834868299%positive
 Empty) 2037%N 1207706234443%positive
 Empty) 2039%N 1482584141387%positive
 (Branch Empty 2043%N 91014737483%positive
 Empty))) 2046%N 151144279627%positive
 (Branch (Branch (Branch (Branch Empty 2050%N 185504017995%positive
 Empty) 2052%N 1491174075979%positive
 Empty) 2056%N 99604672075%positive
 (Branch (Branch Empty 2062%N 37327646283%positive
 Empty) 2065%N 80277319243%positive
 Empty)) 2068%N 303615618635%positive
 (Branch (Branch (Branch Empty 2072%N 372335095371%positive
 Empty) 2074%N 2983675211339%positive
 Empty) 2078%N 200536403531%positive
 (Branch Empty 2081%N 41622613579%positive
 Empty)))))) 2085%N 50212548171%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2088%N 36253904459%positive
 Empty) 2091%N 79203577419%positive
 Empty) 2094%N 302541876811%positive
 (Branch (Branch Empty 2098%N 371261353547%positive
 Empty) 2100%N 2982601469515%positive
 Empty)) 2104%N 199462661707%positive
 (Branch (Branch (Branch Empty 2107%N 40548871755%positive
 Empty) 2111%N 49138806347%positive
 Empty) 2114%N 38401388107%positive
 (Branch (Branch Empty 2117%N 81351061067%positive
 Empty) 2120%N 304689360459%positive
 Empty))) 2124%N 373408837195%positive
 (Branch (Branch (Branch (Branch Empty 2126%N 2984748953163%positive
 Empty) 2130%N 201610145355%positive
 Empty) 2133%N 42696355403%positive
 (Branch (Branch Empty 2137%N 51286289995%positive
 Empty) 2140%N 8739270219%positive
 Empty)) 2142%N 150473190987%positive
 (Branch (Branch (Branch Empty 2144%N 184832929355%positive
 Empty) 2148%N 10886753867%positive
 Empty) 2151%N 18402946635%positive
 (Branch Empty 2155%N 22697913931%positive
 Empty)))) 2157%N 185906671179%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2161%N 11960495691%positive
 Empty) 2167%N 17866075723%positive
 Empty) 2169%N 301333917259%positive
 (Branch (Branch Empty 2171%N 370053393995%positive
 Empty) 2175%N 22161043019%positive
 Empty)) 2178%N 37193428555%positive
 (Branch (Branch (Branch Empty 2182%N 45783363147%positive
 Empty) 2184%N 372200877643%positive
 Empty) 2188%N 24308526667%positive
 (Branch Empty 2196%N 34777509451%positive
 Empty))) 2199%N 77727182411%positive
 (Branch (Branch (Branch (Branch Empty 2202%N 301065481803%positive
 Empty) 2206%N 369784958539%positive
 Empty) 2208%N 2981125074507%positive
 (Branch (Branch Empty 2212%N 197986266699%positive
 Empty) 2215%N 39072476747%positive
 Empty)) 2219%N 47662411339%positive
 (Branch (Branch (Branch Empty 2222%N 36924993099%positive
 Empty) 2225%N 79874666059%positive
 Empty) 2228%N 303212965451%positive
 (Branch Empty 2232%N 371932442187%positive
 Empty))))) 2234%N 2983272558155%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2238%N 200133750347%positive
 Empty) 2241%N 41219960395%positive
 Empty) 2245%N 49809894987%positive
 (Branch (Branch Empty 2248%N 35851251275%positive
 Empty) 2250%N 602786934347%positive
 Empty)) 2252%N 740225887819%positive
 (Branch (Branch (Branch Empty 2256%N 44441185867%positive
 Empty) 2259%N 74505956939%positive
 Empty) 2263%N 91685826123%positive
 (Branch Empty 2265%N 744520855115%positive
 Empty))) 2269%N 48736153163%positive
 (Branch (Branch (Branch (Branch Empty 2277%N 69674118731%positive
 Empty) 2280%N 155573464651%positive
 Empty) 2283%N 602250063435%positive
 (Branch (Branch Empty 2287%N 739689016907%positive
 Empty) 2289%N 5962369248843%positive
 Empty)) 2293%N 396091633227%positive
 (Branch (Branch (Branch Empty 2296%N 78264053323%positive
 Empty) 2300%N 95443922507%positive
 Empty) 2303%N 73969086027%positive
 (Branch Empty 2306%N 159868431947%positive
 Empty)))) 2309%N 606545030731%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2313%N 743983984203%positive
 Empty) 2315%N 5966664216139%positive
 Empty) 2319%N 400386600523%positive
 (Branch (Branch Empty 2322%N 82559020619%positive
 Empty) 2326%N 99738889803%positive
 Empty)) 2329%N 71821602379%positive
 (Branch (Branch (Branch Empty 2331%N 1205692968523%positive
 Empty) 2333%N 1480570875467%positive
 Empty) 2337%N 89001471563%positive
 (Branch Empty 2340%N 149131013707%positive
 Empty))) 2344%N 183490752075%positive
 (Branch (Branch (Branch (Branch Empty 2346%N 1489160810059%positive
 Empty) 2350%N 97591406155%positive
 Empty) 2358%N 139467337291%positive
 (Branch (Branch Empty 2360%N 2407210069579%positive
 Empty) 2362%N 2956965883467%positive
 Empty)) 2366%N 173827075659%positive
 (Branch (Branch (Branch Empty 2369%N 294086159947%positive
 Empty) 2373%N 362805636683%positive
 Empty) 2375%N 2974145752651%positive
 (Branch Empty 2379%N 191006944843%positive
 Empty))))))))) 2385%N 148057271883%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2387%N 2415800004171%positive
 Empty) 2389%N 2965555818059%positive
 Empty) 2393%N 182417010251%positive
 (Branch (Branch Empty 2396%N 302676094539%positive
 Empty) 2400%N 371395571275%positive
 Empty)) 2402%N 2982735687243%positive
 (Branch (Branch (Branch Empty 2406%N 199596879435%positive
 Empty) 2412%N 75042827851%positive
 Empty) 2415%N 160942173771%positive
 (Branch (Branch Empty 2418%N 607618772555%positive
 Empty) 2422%N 745057726027%positive
 Empty))) 2424%N 5967737957963%positive
 (Branch (Branch (Branch (Branch Empty 2428%N 401460342347%positive
 Empty) 2431%N 83632762443%positive
 Empty) 2435%N 100812631627%positive
 (Branch (Branch Empty 2438%N 279053774411%positive
 Empty) 2441%N 622651158091%positive
 Empty)) 2444%N 2409357553227%positive
 (Branch (Branch (Branch Empty 2448%N 2959113367115%positive
 Empty) 2450%N 23849834294859%positive
 Empty) 2454%N 1584723832395%positive
 (Branch Empty 2457%N 313413512779%positive
 Empty)))) 2461%N 382132989515%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2464%N 296233643595%positive
 Empty) 2467%N 639831027275%positive
 Empty) 2470%N 2426537422411%positive
 (Branch (Branch Empty 2474%N 2976293236299%positive
 Empty) 2476%N 23867014164043%positive
 Empty)) 2480%N 1601903701579%positive
 (Branch (Branch (Branch Empty 2483%N 330593381963%positive
 Empty) 2487%N 399312858699%positive
 Empty) 2490%N 287643709003%positive
 (Branch Empty 2492%N 4823129173579%positive
 Empty))) 2494%N 5922640801355%positive
 (Branch (Branch (Branch (Branch Empty 2498%N 356363185739%positive
 Empty) 2501%N 596881354315%positive
 Empty) 2505%N 734320307787%positive
 (Branch (Branch Empty 2507%N 5957000539723%positive
 Empty) 2511%N 390722924107%positive
 Empty)) 2520%N 2229710411%positive
 (Branch (Branch (Branch Empty 2523%N 4914064971%positive
 Empty) 2526%N 18872708683%positive
 Empty) 2530%N 23167675979%positive
 (Branch Empty 2532%N 186376433227%positive
 Empty))))) 2536%N 12430257739%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2540%N 8806379083%positive
 Empty) 2542%N 150540299851%positive
 Empty) 2544%N 184900038219%positive
 (Branch (Branch Empty 2548%N 10953862731%positive
 Empty) 2551%N 18470055499%positive
 Empty)) 2555%N 22765022795%positive
 (Branch (Branch (Branch Empty 2557%N 185973780043%positive
 Empty) 2561%N 12027604555%positive
 Empty) 2567%N 17933184587%positive
 (Branch (Branch Empty 2569%N 301401026123%positive
 Empty) 2571%N 370120502859%positive
 Empty))) 2575%N 22228151883%positive
 (Branch (Branch (Branch (Branch Empty 2578%N 37260537419%positive
 Empty) 2582%N 45850472011%positive
 Empty) 2584%N 372267986507%positive
 (Branch (Branch Empty 2588%N 24375635531%positive
 Empty) 2596%N 9074814539%positive
 Empty)) 2599%N 19812232779%positive
 (Branch (Branch (Branch Empty 2602%N 75646807627%positive
 Empty) 2606%N 92826676811%positive
 Empty) 2608%N 745661705803%positive
 (Branch Empty 2612%N 49877003851%positive
 Empty)))) 2616%N 9611685451%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2618%N 151345606219%positive
 Empty) 2620%N 185705344587%positive
 Empty) 2624%N 11759169099%positive
 (Branch (Branch Empty 2627%N 19275361867%positive
 Empty) 2631%N 23570329163%positive
 Empty)) 2633%N 186779086411%positive
 (Branch (Branch (Branch Empty 2637%N 12832910923%positive
 Empty) 2643%N 4343639627%positive
 Empty) 2646%N 9712348747%positive
 (Branch Empty 2649%N 37629636171%positive
 Empty))) 2653%N 46219570763%positive
 (Branch (Branch (Branch (Branch Empty 2655%N 372637085259%positive
 Empty) 2659%N 24744734283%positive
 Empty) 2662%N 4880510539%positive
 (Branch (Branch Empty 2666%N 5954252363%positive
 Empty) 2669%N 4612075083%positive
 Empty)) 2672%N 9980784203%positive
 (Branch (Branch (Branch Empty 2675%N 37898071627%positive
 Empty) 2679%N 46488006219%positive
 Empty) 2681%N 372905520715%positive
 (Branch Empty 2685%N 25013169739%positive
 Empty)))))) 2688%N 5148945995%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2692%N 6222687819%positive
 Empty) 2695%N 4477857355%positive
 Empty) 2697%N 75344817739%positive
 (Branch (Branch Empty 2699%N 92524686923%positive
 Empty) 2703%N 5551599179%positive
 Empty)) 2706%N 9309695563%positive
 (Branch (Branch (Branch Empty 2710%N 11457179211%positive
 Empty) 2712%N 93061557835%positive
 Empty) 2716%N 6088470091%positive
 (Branch (Branch Empty 2723%N 8705715787%positive
 Empty) 2726%N 19443134027%positive
 Empty))) 2729%N 75277708875%positive
 (Branch (Branch (Branch (Branch Empty 2733%N 92457578059%positive
 Empty) 2735%N 745292607051%positive
 Empty) 2739%N 49507905099%positive
 (Branch (Branch Empty 2742%N 9779457611%positive
 Empty) 2746%N 11926941259%positive
 Empty)) 2749%N 69372128843%positive
 (Branch (Branch (Branch Empty 2752%N 155271474763%positive
 Empty) 2755%N 601948073547%positive
 Empty) 2759%N 739387027019%positive
 (Branch Empty 2761%N 5962067258955%positive
 Empty)))) 2765%N 395789643339%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2768%N 77962063435%positive
 Empty) 2772%N 95141932619%positive
 Empty) 2775%N 73667096139%positive
 (Branch (Branch Empty 2778%N 159566442059%positive
 Empty) 2781%N 606243040843%positive
 Empty)) 2785%N 743681994315%positive
 (Branch (Branch (Branch Empty 2787%N 5966362226251%positive
 Empty) 2791%N 400084610635%positive
 Empty) 2794%N 82257030731%positive
 (Branch Empty 2798%N 99436899915%positive
 Empty))) 2801%N 71519612491%positive
 (Branch (Branch (Branch (Branch Empty 2803%N 1205390978635%positive
 Empty) 2805%N 1480268885579%positive
 Empty) 2809%N 88699481675%positive
 (Branch (Branch Empty 2812%N 148829023819%positive
 Empty) 2816%N 183188762187%positive
 Empty)) 2818%N 1488858820171%positive
 (Branch (Branch (Branch Empty 2822%N 97289416267%positive
 Empty) 2829%N 70445870667%positive
 Empty) 2831%N 1204317236811%positive
 (Branch Empty 2833%N 1479195143755%positive
 Empty))))) 2837%N 87625739851%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2840%N 147755281995%positive
 Empty) 2844%N 182115020363%positive
 Empty) 2846%N 1487785078347%positive
 (Branch (Branch Empty 2850%N 96215674443%positive
 Empty) 2858%N 38233615947%positive
 Empty)) 2860%N 605169299019%positive
 (Branch (Branch (Branch Empty 2862%N 742608252491%positive
 Empty) 2866%N 46823550539%positive
 Empty) 2869%N 76888321611%positive
 (Branch Empty 2873%N 94068190795%positive
 Empty))) 2875%N 746903219787%positive
 (Branch (Branch (Branch (Branch Empty 2879%N 51118517835%positive
 Empty) 2885%N 17564085835%positive
 Empty) 2888%N 39038922315%positive
 (Branch (Branch Empty 2891%N 150708072011%positive
 Empty) 2895%N 185067810379%positive
 Empty)) 2897%N 1490737868363%positive
 (Branch (Branch (Branch Empty 2901%N 99168464459%positive
 Empty) 2904%N 19711569483%positive
 Empty) 2908%N 24006536779%positive
 (Branch Empty 2911%N 18637827659%positive
 Empty)))) 2914%N 40112664139%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2917%N 151781813835%positive
 Empty) 2921%N 186141552203%positive
 Empty) 2923%N 1491811610187%positive
 (Branch (Branch Empty 2927%N 100242206283%positive
 Empty) 2930%N 20785311307%positive
 Empty)) 2934%N 25080278603%positive
 (Branch (Branch (Branch Empty 2937%N 35280825931%positive
 Empty) 2940%N 78230498891%positive
 Empty) 2943%N 301568798283%positive
 (Branch Empty 2947%N 370288275019%positive
 Empty))) 2949%N 2981628390987%positive
 (Branch (Branch (Branch (Branch Empty 2953%N 198489583179%positive
 Empty) 2956%N 39575793227%positive
 Empty) 2960%N 48165727819%positive
 (Branch (Branch Empty 2963%N 37428309579%positive
 Empty) 2966%N 80377982539%positive
 Empty)) 2969%N 303716281931%positive
 (Branch (Branch (Branch Empty 2973%N 372435758667%positive
 Empty) 2975%N 2983775874635%positive
 Empty) 2979%N 200637066827%positive
 (Branch Empty 2982%N 41723276875%positive
 Empty))))))) 2986%N 50313211467%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2989%N 36354567755%positive
 Empty) 2991%N 603290250827%positive
 Empty) 2993%N 740729204299%positive
 (Branch (Branch Empty 2997%N 44944502347%positive
 Empty) 3000%N 75009273419%positive
 Empty)) 3004%N 92189142603%positive
 (Branch (Branch (Branch Empty 3006%N 745024171595%positive
 Empty) 3010%N 49239469643%positive
 Empty) 3017%N 17429868107%positive
 (Branch (Branch Empty 3020%N 38904704587%positive
 Empty) 3023%N 150573854283%positive
 Empty))) 3027%N 184933592651%positive
 (Branch (Branch (Branch (Branch Empty 3029%N 1490603650635%positive
 Empty) 3033%N 99034246731%positive
 Empty) 3036%N 19577351755%positive
 (Branch (Branch Empty 3040%N 23872319051%positive
 Empty) 3043%N 18503609931%positive
 Empty)) 3046%N 39978446411%positive
 (Branch (Branch (Branch Empty 3049%N 151647596107%positive
 Empty) 3053%N 186007334475%positive
 Empty) 3055%N 1491677392459%positive
 (Branch Empty 3059%N 100107988555%positive
 Empty)))) 3062%N 20651093579%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3066%N 24946060875%positive
 Empty) 3069%N 35146608203%positive
 Empty) 3072%N 78096281163%positive
 (Branch (Branch Empty 3075%N 301434580555%positive
 Empty) 3079%N 370154057291%positive
 Empty)) 3081%N 2981494173259%positive
 (Branch (Branch (Branch Empty 3085%N 198355365451%positive
 Empty) 3088%N 39441575499%positive
 Empty) 3092%N 48031510091%positive
 (Branch Empty 3095%N 37294091851%positive
 Empty))) 3098%N 80243764811%positive
 (Branch (Branch (Branch (Branch Empty 3101%N 303582064203%positive
 Empty) 3105%N 372301540939%positive
 Empty) 3107%N 2983641656907%positive
 (Branch (Branch Empty 3111%N 200502849099%positive
 Empty) 3114%N 41589059147%positive
 Empty)) 3118%N 50178993739%positive
 (Branch (Branch (Branch Empty 3121%N 139299565131%positive
 Empty) 3124%N 311098256971%positive
 Empty) 3127%N 1204451454539%positive
 (Branch Empty 3131%N 1479329361483%positive
 Empty))))) 3133%N 11924689825355%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3137%N 792134594123%positive
 Empty) 3140%N 156479434315%positive
 Empty) 3144%N 190839172683%positive
 (Branch (Branch Empty 3147%N 147889499723%positive
 Empty) 3150%N 319688191563%positive
 Empty)) 3153%N 1213041389131%positive
 (Branch (Branch (Branch Empty 3157%N 1487919296075%positive
 Empty) 3159%N 11933279759947%positive
 Empty) 3163%N 800724528715%positive
 (Branch Empty 3166%N 165069368907%positive
 Empty))) 3170%N 199429107275%positive
 (Branch (Branch (Branch (Branch Empty 3173%N 143594532427%positive
 Empty) 3175%N 2411337264715%positive
 Empty) 3177%N 2961093078603%positive
 (Branch (Branch Empty 3181%N 177954270795%positive
 Empty) 3184%N 298213355083%positive
 Empty)) 3188%N 366932831819%positive
 (Branch (Branch (Branch Empty 3190%N 2978272947787%positive
 Empty) 3194%N 195134139979%positive
 Empty) 3201%N 141447048779%positive
 (Branch Empty 3204%N 313245740619%positive
 Empty)))) 3207%N 1206598938187%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3211%N 1481476845131%positive
 Empty) 3213%N 11926837309003%positive
 Empty) 3217%N 794282077771%positive
 (Branch (Branch Empty 3220%N 158626917963%positive
 Empty) 3224%N 192986656331%positive
 Empty)) 3227%N 150036983371%positive
 (Branch (Branch (Branch Empty 3230%N 321835675211%positive
 Empty) 3233%N 1215188872779%positive
 Empty) 3237%N 1490066779723%positive
 (Branch Empty 3239%N 11935427243595%positive
 Empty))) 3243%N 802872012363%positive
 (Branch (Branch (Branch (Branch Empty 3246%N 167216852555%positive
 Empty) 3250%N 201576590923%positive
 Empty) 3253%N 145742016075%positive
 (Branch (Branch Empty 3255%N 2413484748363%positive
 Empty) 3257%N 2963240562251%positive
 Empty)) 3261%N 180101754443%positive
 (Branch (Branch (Branch Empty 3264%N 300360838731%positive
 Empty) 3268%N 369080315467%positive
 Empty) 3270%N 2980420431435%positive
 (Branch Empty 3274%N 197281623627%positive
 Empty)))))) 3281%N 34878172747%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3283%N 601813855819%positive
 Empty) 3285%N 739252809291%positive
 Empty) 3289%N 43468107339%positive
 (Branch (Branch Empty 3292%N 73532878411%positive
 Empty) 3296%N 90712747595%positive
 Empty)) 3298%N 743547776587%positive
 (Branch (Branch (Branch Empty 3302%N 47763074635%positive
 Empty) 3308%N 71385394763%positive
 Empty) 3310%N 1205256760907%positive
 (Branch (Branch Empty 3312%N 1480134667851%positive
 Empty) 3316%N 88565263947%positive
 Empty))) 3319%N 148694806091%positive
 (Branch (Branch (Branch (Branch Empty 3323%N 183054544459%positive
 Empty) 3325%N 1488724602443%positive
 Empty) 3329%N 97155198539%positive
 (Branch (Branch Empty 3337%N 139031129675%positive
 Empty) 3340%N 310829821515%positive
 Empty)) 3343%N 1204183019083%positive
 (Branch (Branch (Branch Empty 3347%N 1479060926027%positive
 Empty) 3349%N 11924421389899%positive
 Empty) 3353%N 791866158667%positive
 (Branch Empty 3356%N 156210998859%positive
 Empty)))) 3360%N 190570737227%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3363%N 147621064267%positive
 Empty) 3366%N 319419756107%positive
 Empty) 3369%N 1212772953675%positive
 (Branch (Branch Empty 3373%N 1487650860619%positive
 Empty) 3375%N 11933011324491%positive
 Empty)) 3379%N 800456093259%positive
 (Branch (Branch (Branch Empty 3382%N 164800933451%positive
 Empty) 3386%N 199160671819%positive
 Empty) 3389%N 143326096971%positive
 (Branch Empty 3392%N 315124788811%positive
 Empty))) 3395%N 1208477986379%positive
 (Branch (Branch (Branch (Branch Empty 3399%N 1483355893323%positive
 Empty) 3401%N 11928716357195%positive
 Empty) 3405%N 796161125963%positive
 (Branch (Branch Empty 3408%N 160505966155%positive
 Empty) 3412%N 194865704523%positive
 Empty)) 3415%N 151916031563%positive
 (Branch (Branch (Branch Empty 3418%N 323714723403%positive
 Empty) 3421%N 1217067920971%positive
 Empty) 3425%N 1491945827915%positive
 (Branch Empty 3427%N 11937306291787%positive
 Empty))))) 3431%N 804751060555%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3434%N 169095900747%positive
 Empty) 3438%N 203455639115%positive
 Empty) 3441%N 141178613323%positive
 (Branch (Branch Empty 3444%N 312977305163%positive
 Empty) 3447%N 1206330502731%positive
 Empty)) 3451%N 1481208409675%positive
 (Branch (Branch (Branch Empty 3453%N 11926568873547%positive
 Empty) 3457%N 794013642315%positive
 Empty) 3460%N 158358482507%positive
 (Branch Empty 3464%N 192718220875%positive
 Empty))) 3467%N 149768547915%positive
 (Branch (Branch (Branch (Branch Empty 3470%N 321567239755%positive
 Empty) 3473%N 1214920437323%positive
 Empty) 3477%N 1489798344267%positive
 (Branch (Branch Empty 3479%N 11935158808139%positive
 Empty) 3483%N 802603576907%positive
 Empty)) 3486%N 166948417099%positive
 (Branch (Branch (Branch Empty 3490%N 201308155467%positive
 Empty) 3493%N 145473580619%positive
 Empty) 3495%N 2413216312907%positive
 (Branch Empty 3497%N 2962972126795%positive
 Empty)))) 3501%N 179833318987%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3504%N 300092403275%positive
 Empty) 3508%N 368811880011%positive
 Empty) 3510%N 2980151995979%positive
 (Branch (Branch Empty 3514%N 197013188171%positive
 Empty) 3521%N 35415043659%positive
 Empty)) 3524%N 78364716619%positive
 (Branch (Branch (Branch Empty 3527%N 301703016011%positive
 Empty) 3531%N 370422492747%positive
 Empty) 3533%N 2981762608715%positive
 (Branch Empty 3537%N 198623800907%positive
 Empty))) 3541%N 37562527307%positive
 (Branch (Branch (Branch (Branch Empty 3543%N 604498210379%positive
 Empty) 3545%N 741937163851%positive
 Empty) 3549%N 46152461899%positive
 (Branch (Branch Empty 3552%N 76217232971%positive
 Empty) 3556%N 93397102155%positive
 Empty)) 3558%N 746232131147%positive
 (Branch (Branch (Branch Empty 3562%N 50447429195%positive
 Empty) 3568%N 70848523851%positive
 Empty) 3570%N 1204719889995%positive
 (Branch Empty 3572%N 1479597796939%positive
 Empty)))))))) 3576%N 88028393035%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3579%N 148157935179%positive
 Empty) 3583%N 182517673547%positive
 Empty) 3585%N 1488187731531%positive
 (Branch (Branch Empty 3589%N 96618327627%positive
 Empty) 3595%N 143862967883%positive
 Empty)) 3597%N 2411605700171%positive
 (Branch (Branch (Branch Empty 3599%N 2961361514059%positive
 Empty) 3603%N 178222706251%positive
 Empty) 3606%N 298481790539%positive
 (Branch (Branch Empty 3610%N 367201267275%positive
 Empty) 3612%N 2978541383243%positive
 Empty))) 3616%N 195402575435%positive
 (Branch (Branch (Branch (Branch Empty 3624%N 72996007499%positive
 Empty) 3627%N 158895353419%positive
 Empty) 3630%N 605571952203%positive
 (Branch (Branch Empty 3634%N 743010905675%positive
 Empty) 3636%N 5965691137611%positive
 Empty)) 3640%N 399413521995%positive
 (Branch (Branch (Branch Empty 3644%N 77290974795%positive
 Empty) 3646%N 1211162340939%positive
 Empty) 3648%N 1486040247883%positive
 (Branch Empty 3652%N 94470843979%positive
 Empty)))) 3655%N 154600386123%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3659%N 188960124491%positive
 Empty) 3661%N 1494630182475%positive
 Empty) 3665%N 103060778571%positive
 (Branch (Branch Empty 3671%N 1105636939%positive
 Empty) 3673%N 18822377035%positive
 Empty)) 3675%N 23117344331%positive
 (Branch (Branch (Branch Empty 3679%N 1374072395%positive
 Empty) 3682%N 2313596491%positive
 Empty) 3686%N 2850467403%positive
 (Branch Empty 3688%N 23251562059%positive
 Empty))) 3692%N 1508290123%positive
 (Branch (Branch (Branch (Branch Empty 3698%N 2246487627%positive
 Empty) 3700%N 37679967819%positive
 Empty) 3702%N 46269902411%positive
 (Branch (Branch Empty 3706%N 2783358539%positive
 Empty) 3709%N 4662406731%positive
 Empty)) 3713%N 5736148555%positive
 (Branch (Branch (Branch Empty 3715%N 46538337867%positive
 Empty) 3719%N 3051793995%positive
 Empty) 3727%N 2212933195%positive
 (Branch Empty 3729%N 37646413387%positive
 Empty))))) 3731%N 46236347979%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3735%N 2749804107%positive
 Empty) 3738%N 4628852299%positive
 Empty) 3742%N 5702594123%positive
 (Branch (Branch Empty 3744%N 46504783435%positive
 Empty) 3748%N 3018239563%positive
 Empty)) 3754%N 4494634571%positive
 (Branch (Branch (Branch Empty 3756%N 75361594955%positive
 Empty) 3758%N 92541464139%positive
 Empty) 3762%N 5568376395%positive
 (Branch Empty 3765%N 9326472779%positive
 Empty))) 3769%N 11473956427%positive
 (Branch (Branch (Branch (Branch Empty 3771%N 93078335051%positive
 Empty) 3775%N 6105247307%positive
 Empty) 3783%N 8722493003%positive
 (Branch (Branch Empty 3786%N 19459911243%positive
 Empty) 3789%N 75294486091%positive
 Empty)) 3793%N 92474355275%positive
 (Branch (Branch (Branch Empty 3795%N 745309384267%positive
 Empty) 3799%N 49524682315%positive
 Empty) 3803%N 9259363915%positive
 (Branch Empty 3805%N 150993284683%positive
 Empty)))) 3807%N 185353023051%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3811%N 11406847563%positive
 Empty) 3814%N 18923040331%positive
 Empty) 3818%N 23218007627%positive
 (Branch (Branch Empty 3820%N 186426764875%positive
 Empty) 3824%N 12480589387%positive
 Empty)) 3830%N 17580863051%positive
 (Branch (Branch (Branch Empty 3832%N 301048704587%positive
 Empty) 3834%N 369768181323%positive
 Empty) 3838%N 21875830347%positive
 (Branch Empty 3841%N 36908215883%positive
 Empty))) 3845%N 45498150475%positive
 (Branch (Branch (Branch (Branch Empty 3847%N 371915664971%positive
 Empty) 3851%N 24023313995%positive
 Empty) 3857%N 35834474059%positive
 (Branch (Branch Empty 3859%N 602770157131%positive
 Empty) 3861%N 740209110603%positive
 Empty)) 3865%N 44424408651%positive
 (Branch (Branch (Branch Empty 3868%N 74489179723%positive
 Empty) 3872%N 91669048907%positive
 Empty) 3874%N 744504077899%positive
 (Branch Empty 3878%N 48719375947%positive
 Empty)))))) 3886%N 18117733963%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3889%N 39592570443%positive
 Empty) 3892%N 151261720139%positive
 Empty) 3896%N 185621458507%positive
 (Branch (Branch Empty 3898%N 1491291516491%positive
 Empty) 3902%N 99722112587%positive
 Empty)) 3906%N 19191475787%positive
 (Branch (Branch (Branch Empty 3908%N 302659317323%positive
 Empty) 3910%N 371378794059%positive
 Empty) 3914%N 23486443083%positive
 (Branch (Branch Empty 3917%N 38518828619%positive
 Empty) 3921%N 47108763211%positive
 Empty))) 3923%N 373526277707%positive
 (Branch (Branch (Branch (Branch Empty 3927%N 25633926731%positive
 Empty) 3933%N 17446645323%positive
 Empty) 3935%N 300914486859%positive
 (Branch (Branch Empty 3937%N 369633963595%positive
 Empty) 3941%N 21741612619%positive
 Empty)) 3944%N 36773998155%positive
 (Branch (Branch (Branch Empty 3948%N 45363932747%positive
 Empty) 3950%N 371781447243%positive
 Empty) 3954%N 23889096267%positive
 (Branch Empty 3960%N 35700256331%positive
 Empty)))) 3962%N 602635939403%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3964%N 740074892875%positive
 Empty) 3968%N 44290190923%positive
 Empty) 3971%N 74354961995%positive
 (Branch (Branch Empty 3975%N 91534831179%positive
 Empty) 3977%N 744369860171%positive
 Empty)) 3981%N 48585158219%positive
 (Branch (Branch (Branch Empty 3989%N 69523123787%positive
 Empty) 3992%N 155422469707%positive
 Empty) 3995%N 602099068491%positive
 (Branch Empty 3999%N 739538021963%positive
 Empty))) 4001%N 5962218253899%positive
 (Branch (Branch (Branch (Branch Empty 4005%N 395940638283%positive
 Empty) 4008%N 78113058379%positive
 Empty) 4012%N 95292927563%positive
 (Branch (Branch Empty 4015%N 73818091083%positive
 Empty) 4018%N 159717437003%positive
 Empty)) 4021%N 606394035787%positive
 (Branch (Branch (Branch Empty 4025%N 743832989259%positive
 Empty) 4027%N 5966513221195%positive
 Empty) 4031%N 400235605579%positive
 (Branch Empty 4034%N 82408025675%positive
 Empty))))) 4038%N 99587894859%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4041%N 71670607435%positive
 Empty) 4044%N 157569953355%positive
 Empty) 4047%N 604246552139%positive
 (Branch (Branch Empty 4051%N 741685505611%positive
 Empty) 4053%N 5964365737547%positive
 Empty)) 4057%N 398088121931%positive
 (Branch (Branch (Branch Empty 4060%N 80260542027%positive
 Empty) 4064%N 97440411211%positive
 Empty) 4067%N 75965574731%positive
 (Branch Empty 4070%N 161864920651%positive
 Empty))) 4073%N 608541519435%positive
 (Branch (Branch (Branch (Branch Empty 4077%N 745980472907%positive
 Empty) 4079%N 5968660704843%positive
 Empty) 4083%N 402383089227%positive
 (Branch (Branch Empty 4086%N 84555509323%positive
 Empty) 4090%N 101735378507%positive
 Empty)) 4093%N 70596865611%positive
 (Branch (Branch (Branch Empty 4096%N 156496211531%positive
 Empty) 4099%N 603172810315%positive
 Empty) 4103%N 740611763787%positive
 (Branch Empty 4105%N 5963291995723%positive
 Empty)))) 4109%N 397014380107%positive
 (Branch (Branch (Branch (Branch (Branch Empty 4112%N 79186800203%positive
 Empty) 4116%N 96366669387%positive
 Empty) 4119%N 74891832907%positive
 (Branch (Branch Empty 4122%N 160791178827%positive
 Empty) 4125%N 607467777611%positive
 Empty)) 4129%N 744906731083%positive
 (Branch (Branch (Branch Empty 4131%N 5967586963019%positive
 Empty) 4135%N 401309347403%positive
 Empty) 4138%N 83481767499%positive
 (Branch Empty 4142%N 100661636683%positive
 Empty))) 4145%N 72744349259%positive
 (Branch (Branch (Branch (Branch Empty 4147%N 1206615715403%positive
 Empty) 4149%N 1481493622347%positive
 Empty) 4153%N 89924218443%positive
 (Branch (Branch Empty 4156%N 150053760587%positive
 Empty) 4160%N 184413498955%positive
 Empty)) 4162%N 1490083556939%positive
 (Branch (Branch (Branch Empty 4166%N 98514153035%positive
 Empty) 4173%N 17715080779%positive
 Empty) 4176%N 39189917259%positive
 (Branch Empty 4179%N 150859066955%positive
 Empty))))))) 4183%N 185218805323%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 4185%N 1490888863307%positive
 Empty) 4189%N 99319459403%positive
 Empty) 4193%N 18788822603%positive
 (Branch (Branch Empty 4195%N 302256664139%positive
 Empty) 4197%N 370976140875%positive
 Empty)) 4201%N 23083789899%positive
 (Branch (Branch (Branch Empty 4204%N 38116175435%positive
 Empty) 4208%N 46706110027%positive
 Empty) 4210%N 373123624523%positive
 (Branch (Branch Empty 4214%N 25231273547%positive
 Empty) 4220%N 35431820875%positive
 Empty))) 4222%N 602367503947%positive
 (Branch (Branch (Branch (Branch Empty 4224%N 739806457419%positive
 Empty) 4228%N 44021755467%positive
 Empty) 4231%N 74086526539%positive
 (Branch (Branch Empty 4235%N 91266395723%positive
 Empty) 4237%N 744101424715%positive
 Empty)) 4241%N 48316722763%positive
 (Branch (Branch (Branch Empty 4247%N 71939042891%positive
 Empty) 4249%N 1205810409035%positive
 Empty) 4251%N 1480688315979%positive
 (Branch Empty 4255%N 89118912075%positive
 Empty)))) 4258%N 149248454219%positive
 (Branch (Branch (Branch (Branch (Branch Empty 4262%N 183608192587%positive
 Empty) 4264%N 1489278250571%positive
 Empty) 4268%N 97708846667%positive
 (Branch (Branch Empty 4276%N 36505562699%positive
 Empty) 4279%N 79455235659%positive
 Empty)) 4282%N 302793535051%positive
 (Branch (Branch (Branch Empty 4286%N 371513011787%positive
 Empty) 4288%N 2982853127755%positive
 Empty) 4292%N 199714319947%positive
 (Branch Empty 4296%N 38653046347%positive
 Empty))) 4298%N 605588729419%positive
 (Branch (Branch (Branch (Branch Empty 4300%N 743027682891%positive
 Empty) 4304%N 47242980939%positive
 Empty) 4307%N 77307752011%positive
 (Branch (Branch Empty 4311%N 94487621195%positive
 Empty) 4313%N 747322650187%positive
 Empty)) 4317%N 51537948235%positive
 (Branch (Branch (Branch Empty 4323%N 68595275%positive
 Empty) 4325%N 1175891531%positive
 Empty) 4327%N 1444326987%positive
 (Branch Empty 4331%N 85372491%positive
 Empty))))) 4334%N 144092747%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4338%N 177647179%positive
 Empty) 4340%N 1452715595%positive
 Empty) 4344%N 93761099%positive
 (Branch (Branch Empty 4350%N 139898443%positive
 Empty) 4352%N 2354490955%positive
 Empty)) 4354%N 2891361867%positive
 (Branch (Branch (Branch Empty 4358%N 173452875%positive
 Empty) 4361%N 290893387%positive
 Empty) 4365%N 358002251%positive
 (Branch Empty 4367%N 2908139083%positive
 Empty))) 4371%N 190230091%positive
 (Branch (Branch (Branch (Branch Empty 4379%N 70692427%positive
 Empty) 4382%N 154578507%positive
 Empty) 4385%N 590786123%positive
 (Branch (Branch Empty 4389%N 725003851%positive
 Empty) 4391%N 5825277515%positive
 Empty)) 4395%N 389459531%positive
 (Branch (Branch (Branch Empty 4399%N 74886731%positive
 Empty) 4401%N 1182182987%positive
 Empty) 4403%N 1450618443%positive
 (Branch Empty 4407%N 91663947%positive
 Empty)))) 4410%N 150384203%positive
 (Branch (Branch (Branch (Branch (Branch Empty 4414%N 183938635%positive
 Empty) 4416%N 1459007051%positive
 Empty) 4420%N 100052555%positive
 (Branch (Branch Empty 4426%N 34516555%positive
 Empty) 4428%N 588164683%positive
 Empty)) 4430%N 722382411%positive
 (Branch (Branch (Branch Empty 4434%N 42905163%positive
 Empty) 4437%N 72265291%positive
 Empty) 4441%N 89042507%positive
 (Branch Empty 4443%N 726576715%positive
 Empty))) 4447%N 47099467%positive
 (Branch (Branch (Branch (Branch Empty 4453%N 70168139%positive
 Empty) 4455%N 1177464395%positive
 Empty) 4457%N 1445899851%positive
 (Branch (Branch Empty 4461%N 86945355%positive
 Empty) 4464%N 145665611%positive
 Empty)) 4468%N 179220043%positive
 (Branch (Branch (Branch Empty 4470%N 1454288459%positive
 Empty) 4474%N 95333963%positive
 Empty) 4482%N 69119563%positive
 (Branch Empty 4484%N 1176415819%positive
 Empty)))))) 4486%N 1444851275%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 4490%N 85896779%positive
 Empty) 4493%N 144617035%positive
 Empty) 4497%N 178171467%positive
 (Branch (Branch Empty 4499%N 1453239883%positive
 Empty) 4503%N 94285387%positive
 Empty)) 4509%N 140422731%positive
 (Branch (Branch (Branch Empty 4512%N 308194891%positive
 Empty) 4515%N 1180610123%positive
 Empty) 4519%N 1449045579%positive
 (Branch (Branch Empty 4521%N 11649592907%positive
 Empty) 4525%N 777956939%positive
 Empty))) 4529%N 148811339%positive
 (Branch (Branch (Branch (Branch Empty 4531%N 2363403851%positive
 Empty) 4533%N 2900274763%positive
 Empty) 4537%N 182365771%positive
 (Branch (Branch Empty 4540%N 299806283%positive
 Empty) 4544%N 366915147%positive
 Empty)) 4546%N 2917051979%positive
 (Branch (Branch (Branch Empty 4550%N 199142987%positive
 Empty) 4556%N 12496459%positive
 Empty) 4560%N 2207307%positive
 (Branch Empty 4561%N 9547339%positive
 Empty)))) 4564%N 1683019%positive
 (Branch (Branch (Branch (Branch (Branch Empty 4565%N 2469451%positive
 Empty) 4567%N 5090891%positive
 Empty) 4570%N 765515%positive
 (Branch (Branch Empty 4572%N 159307%positive
 Empty) 4575%N 192075%positive
 Empty)) 4578%N 269899%positive
 (Branch (Branch (Branch Empty 4579%N 1187403%positive
 Empty) 4582%N 204363%positive
 Empty) 4583%N 302667%positive
 (Branch Empty 4585%N 630347%positive
 Empty))) 4588%N 89675%positive
 (Branch (Branch (Branch (Branch Empty 4591%N 33099%positive
 Empty) 4593%N 573771%positive
 Empty) 4595%N 704843%positive
 (Branch (Branch Empty 4599%N 41291%positive
 Empty) 4602%N 37195%positive
 Empty)) 4605%N 143691%positive
 (Branch (Branch (Branch Empty 4608%N 307531%positive
 Empty) 4611%N 1159499%positive
 Empty) 4615%N 1421643%positive
 (Branch Empty 4617%N 11383115%positive
 Empty))))) 4621%N 766283%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4624%N 160075%positive
 Empty) 4628%N 192843%positive
 Empty) 4631%N 35147%positive
 (Branch (Branch Empty 4633%N 575819%positive
 Empty) 4635%N 706891%positive
 Empty)) 4639%N 43339%positive
 (Branch (Branch (Branch Empty 4642%N 72011%positive
 Empty) 4646%N 88395%positive
 Empty) 4648%N 710987%positive
 (Branch Empty 4652%N 47435%positive
 Empty))) 4658%N 5451%positive
 (Branch (Branch (Branch (Branch Empty 4661%N 17227%positive
 Empty) 4662%N 74571%positive
 Empty) 4665%N 13131%positive
 (Branch (Branch Empty 4666%N 19275%positive
 Empty) 4668%N 39755%positive
 Empty)) 4671%N 18251%positive
 (Branch (Branch (Branch Empty 4674%N 38731%positive
 Empty) 4677%N 145227%positive
 Empty) 4681%N 177995%positive
 (Branch Empty 4683%N 1423179%positive
 Empty)))) 4687%N 96075%positive
 (Branch (Branch (Branch (Branch (Branch Empty 4690%N 20299%positive
 Empty) 4694%N 24395%positive
 Empty) 4698%N 555%positive
 (Branch (Branch Empty 4701%N 1195%positive
 Empty) 4704%N 4523%positive
 Empty)) 4708%N 5547%positive
 (Branch (Branch (Branch Empty 4710%N 44459%positive
 Empty) 4714%N 2987%positive
 Empty) 4717%N 619%positive
 (Branch Empty 4721%N 747%positive
 Empty))) 4726%N 527%positive
 (Branch (Branch (Branch (Branch Empty 4727%N 2319%positive
 Empty) 4730%N 399%positive
 Empty) 4731%N 591%positive
 (Branch (Branch Empty 4733%N 1231%positive
 Empty) 4736%N 111%positive
 Empty)) 4737%N 287%positive
 (Branch (Branch (Branch Empty 4739%N 4511%positive
 Empty) 4741%N 5535%positive
 Empty) 4745%N 351%positive
 (Branch Empty 4748%N 191%positive
 Empty)))))))))).

Definition loc_source (v : N) : list bool :=
  match K215DrainData.lookup locations_source v with
  | Some c => decode_path c
  | None => []
  end.

Definition locations_reference : K215DrainData.tree positive :=
(Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 0%N 8%positive
 Empty) 2%N 18%positive
 Empty) 7%N 46%positive
 (Branch (Branch Empty 9%N 33%positive
 Empty) 11%N 593%positive
 Empty)) 13%N 721%positive
 (Branch (Branch (Branch Empty 17%N 41%positive
 Empty) 20%N 21%positive
 Empty) 23%N 19%positive
 (Branch (Branch Empty 24%N 139%positive
 Empty) 25%N 1099%positive
 Empty))) 26%N 33355%positive
 (Branch (Branch (Branch (Branch Empty 29%N 74315%positive
 Empty) 32%N 287307%positive
 Empty) 36%N 352843%positive
 (Branch (Branch Empty 38%N 2843211%positive
 Empty) 42%N 189003%positive
 Empty)) 45%N 37451%positive
 (Branch (Branch (Branch Empty 49%N 45643%positive
 Empty) 52%N 68171%positive
 Empty) 55%N 150091%positive
 (Branch Empty 58%N 576075%positive
 Empty)))) 62%N 707147%positive
 (Branch (Branch (Branch (Branch (Branch Empty 64%N 5687883%positive
 Empty) 68%N 379467%positive
 Empty) 71%N 76363%positive
 (Branch (Branch Empty 75%N 92747%positive
 Empty) 78%N 268875%positive
 Empty)) 80%N 4856395%positive
 (Branch (Branch (Branch Empty 82%N 5904971%positive
 Empty) 86%N 334411%positive
 Empty) 89%N 563787%positive
 (Branch Empty 93%N 694859%positive
 Empty))) 95%N 5675595%positive
 (Branch (Branch (Branch (Branch Empty 99%N 367179%positive
 Empty) 107%N 277067%positive
 Empty) 110%N 604747%positive
 (Branch (Branch Empty 113%N 2308683%positive
 Empty) 117%N 2832971%positive
 Empty)) 119%N 22755915%positive
 (Branch (Branch (Branch Empty 123%N 1522251%positive
 Empty) 126%N 309835%positive
 Empty) 130%N 375371%positive
 (Branch Empty 133%N 555595%positive
 Empty))))) 136%N 1210955%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 139%N 4618827%positive
 Empty) 143%N 5667403%positive
 Empty) 145%N 45513291%positive
 (Branch (Branch Empty 149%N 3045963%positive
 Empty) 152%N 621131%positive
 Empty)) 156%N 752203%positive
 (Branch (Branch (Branch Empty 159%N 1112651%positive
 Empty) 161%N 19462731%positive
 Empty) 163%N 23657035%positive
 (Branch (Branch Empty 167%N 1374795%positive
 Empty) 170%N 719435%positive
 Empty))) 173%N 2226763%positive
 (Branch (Branch (Branch (Branch Empty 175%N 38926923%positive
 Empty) 177%N 47315531%positive
 Empty) 181%N 2751051%positive
 (Branch (Branch Empty 184%N 4586059%positive
 Empty) 188%N 5634635%positive
 Empty)) 190%N 45480523%positive
 (Branch (Branch (Branch Empty 194%N 3013195%positive
 Empty) 200%N 4454987%positive
 Empty) 202%N 77855307%positive
 (Branch Empty 204%N 94632523%positive
 Empty)))) 208%N 5503563%positive
 (Branch (Branch (Branch (Branch (Branch Empty 211%N 2882123%positive
 Empty) 214%N 8911435%positive
 Empty) 217%N 19397195%positive
 (Branch (Branch Empty 220%N 73923147%positive
 Empty) 224%N 90700363%positive
 Empty)) 226%N 728234571%positive
 (Branch (Branch (Branch Empty 230%N 48757323%positive
 Empty) 233%N 9960011%positive
 Empty) 237%N 12057163%positive
 (Branch Empty 240%N 17824331%positive
 Empty))) 242%N 311425611%positive
 (Branch (Branch (Branch (Branch Empty 244%N 378534475%positive
 Empty) 248%N 22018635%positive
 Empty) 251%N 36698699%positive
 (Branch (Branch Empty 255%N 45087307%positive
 Empty) 257%N 363854411%positive
 Empty)) 261%N 24115787%positive
 (Branch (Branch (Branch Empty 267%N 35650123%positive
 Empty) 270%N 77593163%positive
 Empty) 273%N 295696971%positive
 (Branch Empty 277%N 362805835%positive
 Empty)))))) 279%N 2912942667%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 283%N 195033675%positive
 Empty) 286%N 39844427%positive
 Empty) 290%N 48233035%positive
 (Branch (Branch Empty 293%N 71301707%positive
 Empty) 296%N 155187787%positive
 Empty)) 299%N 591395403%positive
 (Branch (Branch (Branch Empty 303%N 725613131%positive
 Empty) 305%N 5825886795%positive
 Empty) 309%N 390068811%positive
 (Branch (Branch Empty 312%N 79690315%positive
 Empty) 316%N 96467531%positive
 Empty))) 319%N 142604875%positive
 (Branch (Branch (Branch (Branch Empty 321%N 2491415115%positive
 Empty) 323%N 3028286027%positive
 Empty) 327%N 176159307%positive
 (Branch (Branch Empty 330%N 293599819%positive
 Empty) 334%N 360708683%positive
 Empty)) 336%N 2910845515%positive
 (Branch (Branch (Branch Empty 340%N 192936523%positive
 Empty) 346%N 285211211%positive
 Empty) 349%N 620755531%positive
 (Branch Empty 352%N 2365585995%positive
 Empty)))) 356%N 2902456907%positive
 (Branch (Branch (Branch (Branch (Branch Empty 358%N 23303551563%positive
 Empty) 362%N 1560279627%positive
 Empty) 365%N 318765643%positive
 (Branch (Branch Empty 369%N 385874507%positive
 Empty) 372%N 570423883%positive
 Empty)) 375%N 1241512523%positive
 (Branch (Branch (Branch Empty 378%N 4731173451%positive
 Empty) 382%N 5804915275%positive
 Empty) 384%N 46607104587%positive
 (Branch Empty 388%N 3120560715%positive
 Empty))) 391%N 637532747%positive
 (Branch (Branch (Branch (Branch Empty 395%N 771750475%positive
 Empty) 398%N 1140849227%positive
 Empty) 400%N 19931331147%positive
 (Branch (Branch Empty 402%N 24226298443%positive
 Empty) 406%N 1409284683%positive
 Empty)) 409%N 2348808779%positive
 (Branch (Branch (Branch Empty 413%N 2885679691%positive
 Empty) 415%N 23286774347%positive
 Empty) 419%N 1543502411%positive
 (Branch Empty 425%N 2281699915%positive
 Empty))))) 427%N 39862663755%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 429%N 48452598347%positive
 Empty) 433%N 2818570827%positive
 Empty) 436%N 4697619019%positive
 (Branch (Branch Empty 440%N 5771360843%positive
 Empty) 442%N 46573550155%positive
 Empty)) 446%N 3087006283%positive
 (Branch (Branch (Branch Empty 452%N 4563401291%positive
 Empty) 454%N 79725328971%positive
 Empty) 456%N 96905198155%positive
 (Branch Empty 460%N 5637143115%positive
 Empty))) 463%N 9395239499%positive
 (Branch (Branch (Branch (Branch Empty 467%N 11542723147%positive
 Empty) 469%N 93147101771%positive
 Empty) 473%N 6174014027%positive
 (Branch (Branch Empty 479%N 9126804043%positive
 Empty) 482%N 19864222283%positive
 Empty)) 485%N 75698797131%positive
 (Branch (Branch (Branch Empty 489%N 92878666315%positive
 Empty) 491%N 745713695307%positive
 Empty) 495%N 49928993355%positive
 (Branch Empty 498%N 10200545867%positive
 Empty)))) 502%N 12348029515%positive
 (Branch (Branch (Branch (Branch (Branch Empty 505%N 18253609547%positive
 Empty) 508%N 39728446027%positive
 Empty) 511%N 151397595723%positive
 (Branch (Branch Empty 515%N 185757334091%positive
 Empty) 517%N 1491427392075%positive
 Empty)) 521%N 99857988171%positive
 (Branch (Branch (Branch Empty 524%N 20401093195%positive
 Empty) 528%N 24696060491%positive
 Empty) 531%N 70866958923%positive
 (Branch Empty 533%N 1273457801803%positive
 Empty))) 535%N 1548335708747%positive
 (Branch (Branch (Branch (Branch Empty 539%N 88046828107%positive
 Empty) 542%N 148176370251%positive
 Empty) 546%N 182536108619%positive
 (Branch (Branch Empty 548%N 1488206166603%positive
 Empty) 552%N 96636762699%positive
 Empty)) 561%N 73014442571%positive
 (Branch (Branch (Branch Empty 564%N 158913788491%positive
 Empty) 567%N 605590387275%positive
 Empty) 571%N 743029340747%positive
 (Branch Empty 573%N 5965709572683%positive
 Empty))))))) 577%N 399431957067%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 580%N 81604377163%positive
 Empty) 584%N 98784246347%positive
 Empty) 587%N 146028886603%positive
 (Branch (Branch Empty 590%N 317827578443%positive
 Empty) 593%N 1211180776011%positive
 Empty)) 597%N 1486058682955%positive
 (Branch (Branch (Branch Empty 599%N 11931419146827%positive
 Empty) 603%N 798863915595%positive
 Empty) 606%N 163208755787%positive
 (Branch (Branch Empty 610%N 197568494155%positive
 Empty) 613%N 566935681611%positive
 Empty))) 615%N 10187662424651%positive
 (Branch (Branch (Branch (Branch Empty 617%N 12386685680203%positive
 Empty) 621%N 704374635083%positive
 Empty) 624%N 1185410972235%positive
 (Branch (Branch Empty 628%N 1460288879179%positive
 Empty) 630%N 11905649343051%positive
 Empty)) 634%N 773094111819%positive
 (Branch (Branch (Branch Empty 643%N 584115550795%positive
 Empty) 646%N 1271310318155%positive
 Empty) 649%N 4844723108427%positive
 (Branch Empty 653%N 5944234736203%positive
 Empty)))) 655%N 47725676591691%positive
 (Branch (Branch (Branch (Branch (Branch Empty 659%N 3195455666763%positive
 Empty) 662%N 652835027531%positive
 Empty) 666%N 790273981003%positive
 (Branch (Branch Empty 669%N 1168231103051%positive
 Empty) 672%N 2542620637771%positive
 Empty)) 675%N 9689446218315%positive
 (Branch (Branch (Branch Empty 679%N 11888469473867%positive
 Empty) 681%N 95451353184843%positive
 Empty) 685%N 6390911334987%positive
 (Branch Empty 688%N 1305670056523%positive
 Empty))) 692%N 1580547963467%positive
 (Branch (Branch (Branch (Branch Empty 695%N 4535485463115%positive
 Empty) 697%N 81501299407435%positive
 Empty) 699%N 99093485451851%positive
 (Branch (Branch Empty 703%N 5634997090891%positive
 Empty) 706%N 9483287788107%positive
 Empty)) 710%N 11682311043659%positive
 (Branch (Branch (Branch Empty 712%N 95245194754635%positive
 Empty) 716%N 6184752904779%positive
 Empty) 723%N 4672924416587%positive
 (Branch Empty 726%N 10170482555467%positive
 Empty))))) 729%N 38757784877643%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 733%N 47553877899851%positive
 Empty) 735%N 381805412743755%positive
 Empty) 739%N 25563645344331%positive
 (Branch (Branch Empty 742%N 5222680230475%positive
 Empty) 746%N 6322191858251%positive
 Empty)) 749%N 9345848834635%positive
 (Branch (Branch (Branch Empty 752%N 20340965112395%positive
 Empty) 755%N 77515569756747%positive
 Empty) 759%N 95107755801163%positive
 (Branch Empty 761%N 763610825488971%positive
 Empty))) 765%N 51127290690123%positive
 (Branch (Branch (Branch (Branch Empty 768%N 10445360462411%positive
 Empty) 772%N 12644383717963%positive
 Empty) 775%N 36283883715147%positive
 (Branch (Branch Empty 777%N 652010395269707%positive
 Empty) 779%N 792747883625035%positive
 Empty)) 783%N 45079976737355%positive
 (Branch (Branch (Branch Empty 786%N 75866302315083%positive
 Empty) 790%N 93458488359499%positive
 Empty) 792%N 761961558047307%positive
 (Branch Empty 796%N 49478023248459%positive
 Empty)))) 805%N 72567767431755%positive
 (Branch (Branch (Branch (Branch (Branch Empty 807%N 1304020790540875%positive
 Empty) 809%N 1585495767251531%positive
 Empty) 813%N 90159953476171%positive
 (Branch (Branch Empty 816%N 151732604631627%positive
 Empty) 820%N 186916976720459%positive
 Empty)) 822%N 1523923116096075%positive
 (Branch (Branch (Branch Empty 826%N 98956046498379%positive
 Empty) 834%N 74766790687307%positive
 Empty) 836%N 1306219813796427%positive
 (Branch Empty 838%N 1587694790507083%positive
 Empty))) 842%N 92358976731723%positive
 (Branch (Branch (Branch (Branch Empty 845%N 153931627887179%positive
 Empty) 849%N 189115999976011%positive
 Empty) 851%N 1526122139351627%positive
 (Branch (Branch Empty 855%N 101155069753931%positive
 Empty) 861%N 149533581376075%positive
 Empty)) 863%N 2612439627594315%positive
 (Branch (Branch (Branch Empty 865%N 3175389581015627%positive
 Empty) 869%N 184717953464907%positive
 Empty) 872%N 307863255775819%positive
 (Branch Empty 876%N 378231999953483%positive
 Empty)))))) 878%N 3052244278704715%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 882%N 202310139509323%positive
 Empty) 888%N 299067162753611%positive
 Empty) 891%N 650910883641931%positive
 (Branch (Branch Empty 894%N 2480498232261195%positive
 Empty) 898%N 3043448185682507%positive
 Empty)) 900%N 24435546415692363%positive
 (Branch (Branch (Branch Empty 904%N 1636073302129227%positive
 Empty) 907%N 334251534842443%positive
 Empty) 911%N 404620279020107%positive
 (Branch (Branch Empty 914%N 598134325508683%positive
 Empty) 917%N 1301821767285323%positive
 Empty))) 920%N 4960996464523851%positive
 (Branch (Branch (Branch (Branch Empty 924%N 6086896371366475%positive
 Empty) 926%N 48871092831386187%positive
 Empty) 930%N 3272146604259915%positive
 (Branch (Branch Empty 933%N 668503069686347%positive
 Empty) 937%N 809240558041675%positive
 Empty)) 940%N 1196268651018827%positive
 (Branch (Branch (Branch Empty 943%N 2603643534572107%positive
 Empty) 946%N 9921992929049163%positive
 Empty) 950%N 12173792742734411%positive
 (Branch Empty 952%N 97742185662773835%positive
 Empty)))) 956%N 6544293208521291%positive
 (Branch (Branch (Branch (Branch (Branch Empty 959%N 1337006139374155%positive
 Empty) 963%N 1618481116084811%positive
 Empty) 966%N 4644337115724363%positive
 (Branch (Branch Empty 968%N 83457330594708043%positive
 Empty) 970%N 101471729104190027%positive
 Empty)) 974%N 5770237022566987%positive
 (Branch (Branch (Branch Empty 977%N 9710886696516171%positive
 Empty) 981%N 11962686510201419%positive
 Empty) 983%N 97531079430240843%positive
 (Branch Empty 987%N 6333186975988299%positive
 Empty))) 995%N 18295873486191179%positive
 (Branch (Branch (Branch (Branch Empty 998%N 40813871623043659%positive
 Empty) 1001%N 157907461934676555%positive
 Empty) 1005%N 193936258953640523%positive
 (Branch (Branch Empty 1007%N 1563030545674271307%positive
 Empty) 1011%N 103864266406230603%positive
 Empty)) 1015%N 19421773393033803%positive
 (Branch (Branch (Branch Empty 1017%N 334673747308968523%positive
 Empty) 1019%N 406731341346896459%positive
 Empty) 1023%N 23925373020404299%positive
 (Branch Empty 1026%N 39687971716201035%positive
 Empty))))) 1030%N 48695170970942027%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1032%N 390968742651099723%positive
 Empty) 1036%N 26177172834089547%positive
 Empty) 1042%N 36873221949094475%positive
 (Branch (Branch Empty 1044%N 667377169780963915%positive
 Empty) 1046%N 811492357856819787%positive
 Empty)) 1050%N 45880421203835467%positive
 (Branch (Branch (Branch Empty 1053%N 77405618595428939%positive
 Empty) 1057%N 95420017104910923%positive
 Empty) 1059%N 779967160465226315%positive
 (Branch Empty 1063%N 50384020831205963%positive
 Empty))) 1071%N 37999121855937099%positive
 (Branch (Branch (Branch (Branch Empty 1074%N 83035118129642059%positive
 Empty) 1077%N 317222298752907851%positive
 Empty) 1081%N 389279892790835787%positive
 (Branch (Branch Empty 1083%N 3127468466232097355%positive
 Empty) 1087%N 209135907696015947%positive
 Empty)) 1091%N 40250921669622347%positive
 (Branch (Branch (Branch Empty 1093%N 670754869501491787%positive
 Empty) 1095%N 814870057577347659%positive
 Empty) 1099%N 49258120924363339%positive
 (Branch Empty 1102%N 80783318315956811%positive
 Empty)))) 1106%N 98797716825438795%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1108%N 783344860185754187%positive
 Empty) 1112%N 53761720551733835%positive
 Empty) 1118%N 9570149208160843%positive
 (Branch (Branch Empty 1121%N 20829148276587083%positive
 Empty) 1124%N 79375943432403531%positive
 Empty)) 1128%N 97390341941885515%positive
 (Branch (Branch (Branch Empty 1130%N 781937485302200907%positive
 Empty) 1134%N 52354345668180555%positive
 Empty) 1137%N 10696049115003467%positive
 (Branch Empty 1141%N 12947848928688715%positive
 Empty))) 1144%N 19140298416323147%positive
 (Branch (Branch (Branch (Branch Empty 1146%N 334392272332257867%positive
 Empty) 1148%N 406449866370185803%positive
 Empty) 1152%N 23643898043693643%positive
 (Branch (Branch Empty 1155%N 39406496739490379%positive
 Empty) 1159%N 48413695994231371%positive
 Empty)) 1161%N 390687267674389067%positive
 (Branch (Branch (Branch Empty 1165%N 25895697857378891%positive
 Empty) 1171%N 38280596832647755%positive
 Empty) 1174%N 83316593106352715%positive
 (Branch Empty 1177%N 317503773729618507%positive
 Empty)))))))) 1181%N 389561367767546443%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1183%N 3127749941208808011%positive
 Empty) 1187%N 209417382672726603%positive
 Empty) 1190%N 42784196460018251%positive
 (Branch (Branch Empty 1194%N 51791395714759243%positive
 Empty) 1197%N 76561193665296971%positive
 Empty)) 1200%N 166633186212706891%positive
 (Branch (Branch (Branch Empty 1203%N 635007547459238475%positive
 Empty) 1207%N 779122735535094347%positive
 Empty) 1209%N 6255499882417617483%positive
 (Branch (Branch Empty 1213%N 418834765345454667%positive
 Empty) 1216%N 85568392920037963%positive
 Empty))) 1220%N 103582791429519947%positive
 (Branch (Branch (Branch (Branch Empty 1223%N 297237575406451275%positive
 Empty) 1225%N 5341269158061406795%positive
 Empty) 1227%N 6494190662668253771%positive
 (Branch (Branch Empty 1231%N 369295169444379211%positive
 Empty) 1234%N 621496748577126987%positive
 Empty)) 1238%N 765611936652982859%positive
 (Branch (Branch (Branch Empty 1240%N 6241989083535505995%positive
 Empty) 1244%N 405323966463343179%positive
 Empty) 1253%N 306244774661192267%positive
 (Branch Empty 1256%N 666532744850831947%positive
 Empty)))) 1259%N 2540030189836958283%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1263%N 3116490942140381771%positive
 Empty) 1265%N 25021999529670474315%positive
 Empty) 1269%N 1675339061381823051%positive
 (Branch (Branch Empty 1272%N 342273571680156235%positive
 Empty) 1276%N 414331165718084171%positive
 Empty)) 1279%N 612489549322385995%positive
 (Branch (Branch (Branch Empty 1282%N 1333065489701665355%positive
 Empty) 1285%N 5080060379673918027%positive
 Empty) 1289%N 6232981884280765003%positive
 (Branch Empty 1291%N 50043999059340950091%positive
 Empty))) 1295%N 3350678122763647563%positive
 (Branch (Branch (Branch (Branch Empty 1298%N 684547143360313931%positive
 Empty) 1302%N 828662331436169803%positive
 Empty) 1305%N 2377900603251620427%positive
 (Branch (Branch Empty 1307%N 42730153264491264587%positive
 Empty) 1309%N 51953525301346040395%positive
 Empty)) 1313%N 2954361355555043915%positive
 (Branch (Branch (Branch Empty 1316%N 4971973988617026123%positive
 Empty) 1320%N 6124895493223873099%positive
 Empty) 1322%N 49935912668284058187%positive
 (Branch Empty 1326%N 3242591731706755659%positive
 Empty))))) 1333%N 2449958197289548363%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1336%N 5332261958806665803%positive
 Empty) 1339%N 20320241518695676491%positive
 Empty) 1343%N 24931927537123064395%positive
 (Branch (Branch Empty 1345%N 200175996237363804747%positive
 Empty) 1349%N 13402712491054594635%positive
 Empty)) 1352%N 2738188573441260107%positive
 (Branch (Branch (Branch Empty 1356%N 3314649325744683595%positive
 Empty) 1359%N 4899916394579098187%positive
 Empty) 1362%N 10664523917613333067%positive
 (Branch (Branch Empty 1365%N 40640483037391354443%positive
 Empty) 1369%N 49863855074246130251%positive
 Empty))) 1371%N 400351992474727610955%positive
 (Branch (Branch (Branch (Branch Empty 1375%N 26805424982109190731%positive
 Empty) 1378%N 5476377146882521675%positive
 Empty) 1382%N 6629298651489368651%positive
 (Branch (Branch Empty 1385%N 19023204826012973643%positive
 Empty) 1387%N 341841226115930126923%positive
 Empty)) 1389%N 415628202410768333387%positive
 (Branch (Branch (Branch Empty 1393%N 23634890844440361547%positive
 Empty) 1396%N 39775791908936219211%positive
 Empty) 1400%N 48999163945790995019%positive
 (Branch Empty 1402%N 399487301346272475723%positive
 Empty)))) 1406%N 25940733853654055499%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1413%N 19599665578316397131%positive
 Empty) 1415%N 342417686868233550411%positive
 Empty) 1417%N 416204663163071756875%positive
 (Branch (Branch Empty 1421%N 24211351596743785035%positive
 Empty) 1424%N 40352252661239642699%positive
 Empty)) 1428%N 49575624698094418507%positive
 (Branch (Branch (Branch Empty 1430%N 400063762098575899211%positive
 Empty) 1434%N 26517194605957478987%positive
 Empty) 1440%N 39199331156632795723%positive
 (Branch Empty 1442%N 684835373736467102283%positive
 Empty))) 1444%N 832409326326143515211%positive
 (Branch (Branch (Branch (Branch Empty 1448%N 48422703193487571531%positive
 Empty) 1451%N 80704505322479286859%positive
 Empty) 1455%N 99151249396188838475%positive
 (Branch (Branch Empty 1457%N 800127524197151799883%positive
 Empty) 1461%N 53034389211914959435%positive
 Empty)) 1467%N 78398662313265592907%positive
 (Branch (Branch (Branch Empty 1470%N 170632382681813350987%positive
 Empty) 1473%N 650247728598261693003%positive
 Empty) 1477%N 797821681187938105931%positive
 (Branch Empty 1479%N 6405631879595641797195%positive
 Empty)))))) 1483%N 428886799713747073611%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1486%N 87622034350120368715%positive
 Empty) 1490%N 106068778423829920331%positive
 Empty) 1493%N 156797324626531187275%positive
 (Branch (Branch Empty 1496%N 341264765363626703435%positive
 Empty) 1499%N 1300495457196523387467%positive
 Empty)) 1503%N 1595643362375876213323%positive
 (Branch (Branch (Branch Empty 1505%N 12811263759191283595851%positive
 Empty) 1509%N 857773599427494148683%positive
 Empty) 1512%N 175244068700240738891%positive
 (Branch (Branch Empty 1516%N 212137556847659842123%positive
 Empty) 1519%N 313594649253062376011%positive
 Empty))) 1522%N 682529530727253408331%positive
 (Branch (Branch (Branch (Branch Empty 1525%N 2600990914393046776395%positive
 Empty) 1529%N 3191286724751752428107%positive
 Empty) 1531%N 25622527518382567193163%positive
 (Branch (Branch Empty 1535%N 1715547198854988298827%positive
 Empty) 1538%N 350488137400481479243%positive
 Empty)) 1542%N 424275113695319685707%positive
 (Branch (Branch (Branch Empty 1545%N 1217485108864830405195%positive
 Empty) 1547%N 21877838471419528215115%positive
 Empty) 1549%N 26600204954289173428811%positive
 (Branch Empty 1553%N 1512633014044183231051%positive
 Empty)))) 1556%N 2545650682171918121547%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1560%N 3135946492530623773259%positive
 Empty) 1562%N 25567187286161438538315%positive
 Empty) 1566%N 1660206966633859643979%positive
 (Branch (Branch Empty 1574%N 2434970217729660811851%positive
 Empty) 1576%N 43755676942839056431691%positive
 Empty)) 1578%N 53200409908578346859083%positive
 (Branch (Branch (Branch Empty 1582%N 3025266028088366463563%positive
 Empty) 1585%N 5091301364343836244555%positive
 Empty) 1589%N 6271892985061247547979%positive
 (Branch Empty 1591%N 51134374572322877078091%positive
 Empty))) 1595%N 3320413933267719289419%positive
 (Branch (Branch (Branch (Branch Empty 1603%N 2508757194024499018315%positive
 Empty) 1606%N 5460236245818027276875%positive
 Empty) 1609%N 20807927315144374221387%positive
 (Branch (Branch Empty 1613%N 25530293798014019435083%positive
 Empty) 1615%N 204980220147060537555531%positive
 Empty)) 1619%N 13724377590839906400843%positive
 (Branch (Branch (Branch Empty 1622%N 2803905099203851844171%positive
 Empty) 1626%N 3394200909562557495883%positive
 Empty) 1629%N 5017514388048998038091%positive
 (Branch Empty 1632%N 10920472491636054555211%positive
 Empty))))) 1635%N 41615854630288748444235%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1639%N 51060587596028038871627%positive
 Empty) 1641%N 409960440294121075112523%positive
 Empty) 1645%N 27448755181679812803147%positive
 (Branch (Branch Empty 1648%N 5607810198407703689803%positive
 Empty) 1652%N 6788401819125114993227%positive
 Empty)) 1655%N 10035028776097996077643%positive
 (Branch (Branch (Branch Empty 1658%N 21840944983272109111883%positive
 Empty) 1661%N 83231709260577496889931%positive
 Empty) 1665%N 102121175192056077744715%positive
 (Branch Empty 1667%N 819920880588242150226507%positive
 Empty))) 1671%N 54897510363359625607755%positive
 (Branch (Branch (Branch (Branch Empty 1674%N 11215620396815407381067%positive
 Empty) 1678%N 13576803638250229987915%positive
 Empty) 1681%N 38959523483674573011531%positive
 (Branch (Branch Empty 1683%N 700090831085424902928971%positive
 Empty) 1685%N 851206558537253549767243%positive
 Empty)) 1689%N 48404256449413863438923%positive
 (Branch (Branch (Branch Empty 1692%N 81460821829501379934795%positive
 Empty) 1696%N 100350287760979960789579%positive
 Empty) 1698%N 818149993157166033271371%positive
 (Branch Empty 1702%N 53126622932283508652619%positive
 Empty)))) 1710%N 77919046967349146024523%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1712%N 1400181662170849805859403%positive
 Empty) 1714%N 1702413117074507099535947%positive
 Empty) 1718%N 96808512898827726879307%positive
 (Branch (Branch Empty 1721%N 162921643659002759871051%positive
 Empty) 1725%N 200700575521959921580619%positive
 Empty)) 1727%N 1636299986314332066544203%positive
 (Branch (Branch (Branch Empty 1731%N 106253245864567017306699%positive
 Empty) 1739%N 80280230208783968631371%positive
 Empty) 1741%N 1402542845412284628466251%positive
 (Branch Empty 1743%N 1704774300315941922142795%positive
 Empty))) 1747%N 99169696140262549486155%positive
 (Branch (Branch (Branch (Branch Empty 1750%N 165282826900437582477899%positive
 Empty) 1754%N 203061758763394744187467%positive
 Empty) 1756%N 1638661169555766889151051%positive
 (Branch (Branch Empty 1760%N 108614429106001839913547%positive
 Empty) 1766%N 160560460417567937264203%positive
 Empty)) 1769%N 349455119732353745812043%positive
 (Branch (Branch (Branch Empty 1772%N 1331707348169239950260811%positive
 Empty) 1776%N 1633938803072897243937355%positive
 Empty) 1778%N 13118734089411874403646027%positive
 (Branch Empty 1782%N 878360165813754009745995%positive
 Empty))))))) 1785%N 179449926349046518118987%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 1789%N 217228858212003679828555%positive
 Empty) 1792%N 321120920835135874529867%positive
 Empty) 1795%N 698910239464707491625547%positive
 (Branch (Branch Empty 1798%N 2663414696338479900523083%positive
 Empty) 1802%N 3267877606145794487876171%positive
 Empty)) 1804%N 26237468178823748807293515%positive
 (Branch (Branch (Branch Empty 1808%N 1756720331627508019493451%positive
 Empty) 1811%N 358899852698093036239435%positive
 Empty) 1815%N 434457716424007359658571%positive
 (Branch (Branch Empty 1818%N 1246704751477586336414283%positive
 Empty) 1820%N 22402906594733596893772363%positive
 Empty))) 1822%N 27238609873192113592597067%positive
 (Branch (Branch (Branch (Branch Empty 1826%N 1548936206381243630090827%positive
 Empty) 1829%N 2606746298544044157958731%positive
 Empty) 1833%N 3211209208351358745311819%positive
 (Branch (Branch Empty 1835%N 26180799781029313064729163%positive
 Empty) 1839%N 1700051933833072276929099%positive
 Empty)) 1848%N 1284483683340543498123851%positive
 (Branch (Branch (Branch Empty 1851%N 2795640957858829966506571%positive
 Empty) 1854%N 10653658785353919602096715%positive
 Empty) 1858%N 13071510424583177951509067%positive
 (Branch Empty 1860%N 104949872715294995229178443%positive
 Empty)))) 1864%N 7026881326510032077978187%positive
 (Branch (Branch (Branch (Branch (Branch Empty 1867%N 1435599410792372144962123%positive
 Empty) 1871%N 1737830865696029438638667%positive
 Empty) 1874%N 2568967366681086996249163%positive
 (Branch (Branch Empty 1877%N 5591281915717659933014603%positive
 Empty) 1880%N 21307317570707839204194891%positive
 Empty)) 1884%N 26143020849166355903019595%positive
 (Branch (Branch (Branch Empty 1886%N 209899745430589990458358347%positive
 Empty) 1890%N 14053762653020064155957835%positive
 Empty) 1893%N 2871198821584744289925707%positive
 (Branch Empty 1897%N 3475661731392058877278795%positive
 Empty))) 1900%N 9973638011820690691324491%positive
 (Branch (Branch (Branch (Branch Empty 1902%N 179223252757868775150189131%positive
 Empty) 1904%N 217908878985536908740786763%positive
 Empty) 1908%N 12391489651049949040736843%positive
 (Branch (Branch Empty 1911%N 20853970388352353263680075%positive
 Empty) 1915%N 25689673666810869962504779%positive
 Empty)) 1917%N 209446398248234504517843531%positive
 (Branch (Branch (Branch Empty 1921%N 13600415470664578215443019%positive
 Empty) 1928%N 10275869466724347985001035%positive
 Empty) 1931%N 22365127662870639732062795%positive
 (Branch Empty 1934%N 85229270282831356816783947%positive
 Empty))))) 1938%N 104572083396665423612082763%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 1940%N 839598981722359961833437771%positive
 Empty) 1944%N 56215050612080256623835723%positive
 Empty) 1947%N 11484795286338977159707211%positive
 (Branch (Branch Empty 1951%N 13902646925568235509119563%positive
 Empty) 1954%N 20551738933448695970003531%positive
 Empty)) 1957%N 44730255325741279464127051%positive
 (Branch (Branch (Branch Empty 1960%N 170458540565662713633569355%positive
 Empty) 1964%N 209144166793330847224166987%positive
 Empty) 1966%N 1679197963444719923666877003%positive
 (Branch Empty 1970%N 112430101224160513247672907%positive
 Empty))) 1973%N 22969590572677954319415883%positive
 (Branch (Branch (Branch (Branch Empty 1977%N 27805293851136471018240587%positive
 Empty) 1980%N 79789104094565525530606155%positive
 Empty) 1982%N 1433786022062950201201523275%positive
 (Branch (Branch Empty 1984%N 1743271031884295269926304331%positive
 Empty) 1988%N 99131917208399592325904971%positive
 Empty)) 1991%N 166831763106818826109450827%positive
 (Branch (Branch (Branch Empty 1995%N 205517389334486959700048459%positive
 Empty) 1997%N 1675571185985876036142758475%positive
 Empty) 2001%N 108803323765316625723554379%positive
 (Branch Empty 2008%N 82206955733794783880018507%positive
 Empty)))) 2010%N 1436203873702179459550935627%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2012%N 1745688883523524528275716683%positive
 Empty) 2016%N 101549768847628850675317323%positive
 Empty) 2019%N 169249614746048084458863179%positive
 (Branch (Branch Empty 2023%N 207935240973716218049460811%positive
 Empty) 2025%N 1677989037625105294492170827%positive
 Empty)) 2029%N 111221175404545884072966731%positive
 (Branch (Branch (Branch Empty 2035%N 164413911467589567760038475%positive
 Empty) 2037%N 2872407747404358919101872715%positive
 Empty) 2039%N 3491377767047049056551434827%positive
 (Branch Empty 2043%N 203099537695257701350636107%positive
 Empty))) 2046%N 338499229492096168917727819%positive
 (Branch (Branch (Branch (Branch Empty 2050%N 415870481947432436098923083%positive
 Empty) 2052%N 3355978075250210588984343115%positive
 Empty) 2056%N 222442350809091768145934923%positive
 (Branch (Branch Empty 2062%N 328827822935179135520078411%positive
 Empty) 2065%N 715684085211860471426054731%positive
 Empty)) 2068%N 2727336649050603418137131595%positive
 (Branch (Branch (Branch Empty 2072%N 3346306668693293555586693707%positive
 Empty) 2074%N 26867167415115518778670053963%positive
 Empty) 2078%N 1798881619586568211962788427%positive
 (Branch Empty 2081%N 367513449162847269110676043%positive
 Empty)))))) 2085%N 444884701618183536291871307%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2088%N 657655645870358271040158283%positive
 Empty) 2091%N 1431368170423720942852110923%positive
 Empty) 2094%N 5454673298101206836274264651%positive
 (Branch (Branch Empty 2098%N 6692613337386587111173388875%positive
 Empty) 2100%N 53734334830231037557340109387%positive
 Empty)) 2104%N 3597763239173136423925578315%positive
 (Branch (Branch (Branch Empty 2107%N 735026898325694538221353547%positive
 Empty) 2111%N 889769403236367072583744075%positive
 Empty) 2114%N 1315311291740716542080318027%positive
 (Branch (Branch Empty 2117%N 2862736340847441885704223307%positive
 Empty) 2120%N 10909346596202413672548530763%positive
 Empty))) 2124%N 13385226674773174222346779211%positive
 (Branch (Branch (Branch (Branch Empty 2126%N 107468669660462075114680220235%positive
 Empty) 2130%N 7195526478346272847851158091%positive
 Empty) 2133%N 1470053796651389076442708555%positive
 (Branch (Branch Empty 2137%N 1779538806472734145167489611%positive
 Empty) 2140%N 2630622583481433084160637515%positive
 Empty)) 2142%N 45958523958469742705629985355%positive
 (Branch (Branch (Branch Empty 2144%N 55862044272752784904822979147%positive
 Empty) 2148%N 3249592603124123221610199627%positive
 Empty) 2151%N 5415987671873538702683667019%positive
 (Branch Empty 2155%N 6653927711158918977582791243%positive
 Empty)))) 2157%N 53695649204003369423749511755%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2161%N 3559077612945468290334980683%positive
 Empty) 2167%N 10213005324104387267917773387%positive
 Empty) 2169%N 183524610824057625753795164747%positive
 (Branch (Branch Empty 2171%N 223138692081189794550567139915%positive
 Empty) 2175%N 12688885402675147817716021835%positive
 Empty)) 2178%N 21354465677672809742009891403%positive
 (Branch (Branch (Branch Empty 2182%N 26306225834814330841606388299%positive
 Empty) 2184%N 214473111806192132626273270347%positive
 Empty) 2188%N 13926825441960528092615146059%positive
 (Branch Empty 2196%N 10522490333925732336642554443%positive
 Empty))) 2199%N 22901890726779535085633796683%positive
 (Branch (Branch (Branch (Branch Empty 2202%N 87274772769619309380388256331%positive
 Empty) 2206%N 107081813398185393778774243915%positive
 Empty) 2208%N 859749357283696600917441772107%positive
 (Branch (Branch Empty 2212%N 57564211826770182782809274955%positive
 Empty) 2215%N 11760430373211112611541678667%positive
 Empty)) 2219%N 14236310451781873161339927115%positive
 (Branch (Branch (Branch Empty 2222%N 21044980667851464673285110347%positive
 Empty) 2225%N 45803781453559070171267594827%positive
 Empty) 2228%N 174549545539238618760776514123%positive
 (Branch Empty 2232%N 214163626796370787557548489291%positive
 Empty))))) 2234%N 1719498714567393201834883545675%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2238%N 115128423653540365565618551371%positive
 Empty) 2241%N 23520860746422225223083358795%positive
 Empty) 2245%N 28472620903563746322679855691%positive
 (Branch (Branch Empty 2248%N 81704042592835098143342197323%positive
 Empty) 2250%N 1468196886592461006030361328203%positive
 Empty)) 2252%N 1785109536649518356404537129547%positive
 (Branch (Branch (Branch Empty 2256%N 101511083221401182541728184907%positive
 Empty) 2259%N 170835725421382477936079141451%positive
 Empty) 2263%N 210449806678514646732851116619%positive
 (Branch Empty 2265%N 1715784894449537061010186173003%positive
 Empty))) 2269%N 111414603535684224740921178699%positive
 (Branch (Branch (Branch (Branch Empty 2277%N 84179922671405858693140445771%positive
 Empty) 2280%N 183215125814236280685070383691%positive
 Empty) 2283%N 698198182156954475043106060875%positive
 (Branch (Branch Empty 2287%N 856654507185483150230193961547%positive
 Empty) 2289%N 6877994858269572807339534187083%positive
 Empty)) 2293%N 460513694614161462262474209867%positive
 (Branch (Branch (Branch Empty 2296%N 94083442985688900892333439563%positive
 Empty) 2300%N 113890483614254985290719427147%positive
 Empty) 2303%N 168359845342811717386280893003%positive
 (Branch Empty 2306%N 366430251628472561370140768843%positive
 Empty)))) 2309%N 1396396364313908950086212123211%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2313%N 1713309014370966300460387924555%positive
 Empty) 2315%N 13755989716539145614679068375627%positive
 Empty) 2319%N 921027389228322924524948421195%positive
 (Branch (Branch Empty 2322%N 188166885971377801784666880587%positive
 Empty) 2326%N 227780967228509970581438855755%positive
 Empty)) 2329%N 653632340742680785146737588811%positive
 (Branch (Branch (Branch Empty 2331%N 11745575092739688048242890635851%positive
 Empty) 2333%N 14280876293196146851236297046603%positive
 Empty) 2337%N 812088665771209460333825489483%positive
 (Branch Empty 2340%N 1366685803371059823488633141835%positive
 Empty))) 2344%N 1683598453428117173862808943179%positive
 (Branch (Branch (Branch (Branch Empty 2346%N 13726279155596296488081489394251%positive
 Empty) 2350%N 891316828285473797927369439819%positive
 Empty) 2358%N 673439381371246869545123576395%positive
 (Branch (Branch Empty 2360%N 11765382133368254132641276623435%positive
 Empty) 2362%N 14300683333824712935634683034187%positive
 Empty)) 2366%N 831895706399775544732211477067%positive
 (Branch (Branch (Branch Empty 2369%N 1386492843999625907887019129419%positive
 Empty) 2373%N 1703405494056683258261194930763%positive
 Empty) 2375%N 13746086196224862572479875381835%positive
 (Branch Empty 2379%N 911123868914039882325755427403%positive
 Empty))))))))) 2385%N 1346878762742493739090247154251%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2387%N 23530764266736508265282553248331%positive
 Empty) 2389%N 28601366667649425871269366069835%positive
 Empty) 2393%N 1663791412799551089464422955595%positive
 (Branch (Branch Empty 2396%N 2772985687999251815774038260299%positive
 Empty) 2400%N 3406810988113366516522389862987%positive
 Empty)) 2402%N 27492172392449725144959750765131%positive
 (Branch (Branch (Branch Empty 2406%N 1822247737828079764651510856267%positive
 Empty) 2412%N 2693757525484987478180494309963%positive
 Empty) 2415%N 5862884026055560981922252323403%positive
 (Branch (Branch Empty 2418%N 22342341829022543201379393993291%positive
 Empty) 2422%N 27412944229935460807366206814795%positive
 Empty))) 2424%N 220095835464626329834865094031947%positive
 (Branch (Branch (Branch (Branch Empty 2428%N 14736438227653166792399174761035%positive
 Empty) 2431%N 3010670175542044828554670111307%positive
 Empty) 2435%N 3644495475656159529303021713995%positive
 (Branch (Branch Empty 2438%N 5387515050969974956360988621387%positive
 Empty) 2441%N 11725768052111121963844504648267%positive
 Empty)) 2444%N 44684683658045086402758787988043%positive
 (Branch (Branch (Branch Empty 2448%N 54825888459870921614732413631051%positive
 Empty) 2450%N 440191670929252659669730188065355%positive
 Empty) 2454%N 29472876455306333584798349523531%positive
 (Branch Empty 2457%N 6021340351084089657109340224075%positive
 Empty)))) 2461%N 7288990951312319058606043429451%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2464%N 10775030101939949912721977244235%positive
 Empty) 2467%N 23451536104222243927689009297995%positive
 Empty) 2470%N 89369367316090172805517575977547%positive
 (Branch (Branch Empty 2474%N 109651776919741843229464827263563%positive
 Empty) 2476%N 880383341858505319339460376132171%positive
 Empty)) 2480%N 58945752910612667169596699048523%positive
 (Branch (Branch (Branch Empty 2483%N 12042680702168179314218680449611%positive
 Empty) 2487%N 14577981902624638117212086860363%positive
 Empty) 2490%N 41832469807531570249391205775947%positive
 (Branch Empty 2492%N 751716805935340035087545000786507%positive
 Empty))) 2494%N 913976082764553398479123011074635%positive
 (Branch (Branch (Branch (Branch Empty 2498%N 51973674609357405461364831418955%positive
 Empty) 2501%N 87467891415747828703272521169483%positive
 Empty) 2505%N 107750301019399499127219772455499%positive
 (Branch (Branch Empty 2507%N 878481865958162975237215321324107%positive
 Empty) 2511%N 57044277010270323067351644240459%positive
 Empty)) 2520%N 164794578029669822194571416697419%positive
 (Branch (Branch (Branch Empty 2523%N 367618674066186526434043929557579%positive
 Empty) 2526%N 1422303973456073388479300996430411%positive
 Empty) 2530%N 1746822527114500115262457017006667%positive
 (Branch Empty 2532%N 14078527566134715733022385798904395%positive
 Empty))))) 2536%N 935526142968433298304566965566027%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2540%N 174935782831495657406545042340427%positive
 Empty) 2542%N 3014473127342729516759160222382667%positive
 Empty) 2544%N 3663510234659582970325472263535179%positive
 (Branch (Branch Empty 2548%N 215500602038798998254439544912459%positive
 Empty) 2551%N 357477469264360691222070303914571%positive
 Empty)) 2555%N 438607107678967372917859309058635%positive
 (Branch (Branch (Branch Empty 2557%N 3521533367434021277357841504533067%positive
 Empty) 2561%N 235783011642450668678386796198475%positive
 Empty) 2567%N 332124457259796103192136239807051%positive
 (Branch (Branch Empty 2569%N 6011199146282263821897366599891531%positive
 Empty) 2571%N 7309273360915970729029990682196555%positive
 Empty))) 2575%N 413254095674402784887925244951115%positive
 (Branch (Branch (Branch (Branch Empty 2578%N 697207830125526170823186762955339%positive
 Empty) 2582%N 859467106954739534214764773243467%positive
 Empty) 2584%N 7025319626464847343094729164192331%positive
 (Branch (Branch Empty 2588%N 453818914881706125735819747523147%positive
 Empty) 2596%N 342265662061621938404109865450059%positive
 Empty)) 2599%N 747913854134655346883054891170379%positive
 (Branch (Branch (Branch Empty 2602%N 2857284452914429070973569024916043%positive
 Empty) 2606%N 3506321560231282524539881066068555%positive
 Empty) 2608%N 28169731638271713760059738629864011%positive
 (Branch Empty 2612%N 1883728791939148890624100963187275%positive
 Empty)))) 2616%N 362548071665273608828057116736075%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2618%N 6041622760687741327533287476820555%positive
 Empty) 2620%N 7339696975321448234665911559125579%positive
 Empty) 2624%N 443677710079880290523846121880139%positive
 (Branch (Branch Empty 2627%N 727631444531003676459107639884363%positive
 Empty) 2631%N 889890721360217039850685650172491%positive
 Empty)) 2633%N 7055743240870324848730650041121355%positive
 (Branch (Branch (Branch Empty 2637%N 484242529287183631371740624452171%positive
 Empty) 2643%N 86200240815519599301775817964107%positive
 Empty) 2646%N 187612288833777951421512074394187%positive
 (Branch Empty 2649%N 714954938528721382444140607830603%positive
 Empty))) 2653%N 877214215357934745835718618118731%positive
 (Branch (Branch (Branch (Branch Empty 2655%N 7043066734868042554715683009067595%positive
 Empty) 2659%N 471566023284901337356773592398411%positive
 Empty) 2662%N 96341445617345434513749443607115%positive
 (Branch (Branch Empty 2666%N 116623855220997104937696694893131%positive
 Empty) 2669%N 172400481631039198603551635929675%positive
 Empty)) 2672%N 375224577667555902843024148789835%positive
 (Branch (Branch (Branch Empty 2675%N 1429909877057442764888281215662667%positive
 Empty) 2679%N 1754428430715869491671437236238923%positive
 Empty) 2681%N 14086133469736085109431366018136651%positive
 (Branch Empty 2685%N 943132046569802674713547184798283%positive
 Empty)))))) 2688%N 192682891234690869027498887215691%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2692%N 233247710441994209875393389787723%positive
 Empty) 2695%N 669319516920505123990259292437067%positive
 Empty) 2697%N 12027468894965440561400720012606027%positive
 (Branch (Branch Empty 2699%N 14623617324232854375665968177216075%positive
 Empty) 2703%N 831578793749718487381837302725195%positive
 Empty)) 2706%N 1399486262651965259252360338733643%positive
 (Branch (Branch (Branch Empty 2710%N 1724004816310391986035516359309899%positive
 Empty) 2712%N 14055709855330607603795445141207627%positive
 Empty) 2716%N 912708432164325169077626307869259%positive
 (Branch (Branch Empty 2723%N 689601926524156794414206543723083%positive
 Empty) 2726%N 1500898310670223611372096595163723%positive
 Empty))) 2729%N 5719639508229771059553124862655051%positive
 (Branch (Branch (Branch (Branch Empty 2733%N 7017713722863477966685748944960075%positive
 Empty) 2735%N 56344533878944340437725464072550987%positive
 Empty) 2739%N 3772528186279210698854188739197515%positive
 (Branch (Branch Empty 2742%N 770731564938763476109995548867147%positive
 Empty) 2746%N 932990841767976839501573559155275%positive
 Empty)) 2749%N 1379203853048313588828413087447627%positive
 (Branch (Branch (Branch Empty 2752%N 3001796621340447222744193190328907%positive
 Empty) 2755%N 11439279016459542119106249725311563%positive
 Empty) 2759%N 14035427445726955933371497889921611%positive
 (Branch Empty 2761%N 112689067757888680875450928145103435%positive
 Empty)))) 2765%N 7545056372558421397708377478396491%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2768%N 1541463129877526952219991097735755%positive
 Empty) 2772%N 1865981683535953679003147118312011%positive
 Empty) 2775%N 2758407706096627177656826174896715%positive
 (Branch (Branch Empty 2778%N 6003593242680894445488386380659275%positive
 Empty) 2781%N 22878558032919084238212499450624587%positive
 Empty)) 2785%N 28070854891453911866742995779844683%positive
 (Branch (Branch (Branch Empty 2787%N 225378135515777361750901856290208331%positive
 Empty) 2791%N 15090112745116842795416754956794443%positive
 Empty) 2794%N 3082926259755053904439982195472971%positive
 (Branch Empty 2798%N 3731963367071907358006294236625483%positive
 Empty))) 2801%N 10709112270728081983844148679014987%positive
 (Branch (Branch (Branch (Branch Empty 2803%N 192439502319447048982411520201718347%positive
 Empty) 2805%N 233977877187725670010655490835479115%positive
 Empty) 2809%N 13305260699995495798109396843625035%positive
 (Branch (Branch Empty 2812%N 22391780202431444148037765419760203%positive
 Empty) 2816%N 27584077060966271776568261748980299%positive
 Empty)) 2818%N 224891357685289721660727122259343947%positive
 (Branch (Branch (Branch Empty 2822%N 14603334914629202705242020925930059%positive
 Empty) 2829%N 21418224541456163967688297358031435%positive
 Empty) 2831%N 384879004638894097964823040403438155%positive
 (Branch Empty 2833%N 467955754375451340021310981670959691%positive
 Empty))))) 2837%N 26610521399990991596218793687251531%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 2840%N 44783560404862888296075530839521867%positive
 Empty) 2844%N 55168154121932543553136523497962059%positive
 Empty) 2846%N 449782715370579443321454244518689355%positive
 (Branch (Branch Empty 2850%N 29206669829258405410484041851861579%positive
 Empty) 2858%N 22067261648773017421254609399183947%positive
 Empty)) 2860%N 385528041746210951418389352444590667%positive
 (Branch (Branch (Branch Empty 2862%N 468604791482768193474877293712112203%positive
 Empty) 2866%N 27259558507307845049785105728404043%positive
 Empty) 2869%N 45432597512179741749641842880674379%positive
 (Branch Empty 2873%N 55817191229249397006702835539114571%positive
 Empty))) 2875%N 450431752477896296775020556559841867%positive
 (Branch (Branch (Branch (Branch Empty 2879%N 29855706936575258864050353893014091%positive
 Empty) 2885%N 44134523297546034842509218798369355%positive
 Empty) 2888%N 96057491882894311127814182090570315%positive
 (Branch (Branch Empty 2891%N 366056928526705347811399991210015307%positive
 Empty) 2895%N 449133678263262589867887932477536843%positive
 Empty)) 2897%N 3606050168252437788014429700643355211%positive
 (Branch (Branch (Branch Empty 2901%N 241441803921869484726668079308733003%positive
 Empty) 2904%N 49326820156080862471039715127589451%positive
 Empty) 2908%N 59711413873150517728100707786029643%positive
 (Branch Empty 2911%N 88269046595092069685018437596740171%positive
 Empty)))) 2914%N 192114983765788622255628364181142091%positive
 (Branch (Branch (Branch (Branch (Branch Empty 2917%N 732113857053410695622799982420032075%positive
 Empty) 2921%N 898267356526525179735775864955075147%positive
 Empty) 2923%N 7212100336504875576028859401286711883%positive
 (Branch (Branch Empty 2927%N 482883607843738969453336158617467467%positive
 Empty) 2930%N 98653640312161724942079430255180363%positive
 Empty)) 2934%N 119422827746301035456201415572060747%positive
 (Branch (Branch (Branch Empty 2937%N 176538093190184139370036875193481803%positive
 Empty) 2940%N 384229967531577244511256728362285643%positive
 Empty) 2943%N 1464227714106821391245599964840065611%positive
 (Branch Empty 2947%N 1796534713053050359471551729910151755%positive
 Empty))) 2949%N 14424200673009751152057718802573425227%positive
 (Branch (Branch (Branch (Branch Empty 2953%N 965767215687477938906672317234936395%positive
 Empty) 2956%N 197307280624323449884158860510362187%positive
 Empty) 2960%N 238845655492602070912402831144122955%positive
 (Branch (Branch Empty 2963%N 353076186380368278740073750386965067%positive
 Empty) 2966%N 768459935063154489022513456724572747%positive
 Empty)) 2969%N 2928455428213642782491199929680132683%positive
 (Branch (Branch (Branch Empty 2973%N 3593069426106100718943103459820304971%positive
 Empty) 2975%N 28848401346019502304115437605146851915%positive
 Empty) 2979%N 1931534431374955877813344634469874251%positive
 (Branch Empty 2982%N 394614561248646899768317721020725835%positive
 Empty))))))) 2986%N 477691310985204141824805662288247371%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 2989%N 1370766370653194493932051030914103883%positive
 Empty) 2991%N 24632256296889222269748674585820133963%positive
 Empty) 2993%N 29949168280028885761363902826941512267%positive
 (Branch (Branch Empty 2997%N 1703073369599423462158002795984190027%positive
 Empty) 3000%N 2866147865911224850948833973729491531%positive
 Empty)) 3004%N 3530761863803682787400737503869663819%positive
 (Branch (Branch (Branch Empty 3006%N 28786093783717084372573071649196210763%positive
 Empty) 3010%N 1869226869072537946270978678519233099%positive
 Empty) 3017%N 1412304745521473114960295001547864651%positive
 (Branch (Branch Empty 3020%N 3073839740252617956090053826898295371%positive
 Empty) 3023%N 11713821712854571129964799718720535115%positive
 Empty))) 3027%N 14372277704424402875772413839281224267%positive
 (Branch (Branch (Branch (Branch Empty 3029%N 115393605384078009216461750420587412043%positive
 Empty) 3033%N 7726137725499823511253378537879501387%positive
 Empty) 3036%N 1578458244994587599073270884082907723%positive
 (Branch (Branch Empty 3040%N 1910765243940816567299222649152993867%positive
 Empty) 3043%N 2824609491042946229920590003095730763%positive
 Empty)) 3046%N 6147679480505235912180107653796592203%positive
 (Branch (Branch (Branch Empty 3049%N 23427643425709142259929599437441071691%positive
 Empty) 3053%N 28744555408848805751544827678562449995%positive
 Empty) 3055%N 230787210768156018432923500841174825547%positive
 (Branch Empty 3059%N 15452275450999647022506757075759004235%positive
 Empty)))) 3062%N 3156916489989175198146541768165816907%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3066%N 3821530487881633134598445298305989195%positive
 Empty) 3069%N 5649218982085892459841180006191462987%positive
 Empty) 3072%N 12295358961010471824360215307593185867%positive
 (Branch (Branch Empty 3075%N 46855286851418284519859198874882144843%positive
 Empty) 3079%N 57489110817697611503089655357124901451%positive
 Empty)) 3081%N 461574421536312036865847001682349652555%positive
 (Branch (Branch (Branch Empty 3085%N 30904550901999294045013514151518009931%positive
 Empty) 3088%N 6313832979978350396293083536331635275%positive
 Empty) 3092%N 7643060975763266269196890596611979851%positive
 (Branch Empty 3095%N 11298437964171784919682360012382927435%positive
 Empty))) 3098%N 24590717922020943648720430615186373195%positive
 (Branch (Branch (Branch (Branch Empty 3101%N 93710573702836569039718397749764291147%positive
 Empty) 3105%N 114978221635395223006179310714249804363%positive
 Empty) 3107%N 923148843072624073731694003364699306571%positive
 (Branch (Branch Empty 3111%N 61809101803998588090027028303036021323%positive
 Empty) 3114%N 12627665959956700792586167072663272011%positive
 Empty)) 3118%N 15286121951526532538393781193223961163%positive
 (Branch (Branch (Branch Empty 3121%N 22596875928343569839364720024765856331%positive
 Empty) 3124%N 49181435844041887297440861230372747851%positive
 Empty) 3127%N 187421147405673138079436795499528583755%positive
 (Branch Empty 3131%N 229956443270790446012358621428499610187%positive
 Empty))))) 3133%N 1846297686145248147463388006729398614603%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3137%N 123618203607997176180054056606072044107%positive
 Empty) 3140%N 25255331919913401585172334145326545483%positive
 Empty) 3144%N 30572243903053065076787562386447923787%positive
 (Branch (Branch Empty 3147%N 45193751856687139678729440049531714123%positive
 Empty) 3150%N 98362871688083774594881722460745497163%positive
 Empty)) 3153%N 374842294811346276158873590999057168971%positive
 (Branch (Branch (Branch Empty 3157%N 459912886541580892024717242856999221835%positive
 Empty) 3159%N 3692595372290496294926776013458797230667%positive
 Empty) 3163%N 247236407215994352360108113212144089675%positive
 (Branch Empty 3166%N 50510663839826803170344668290653092427%positive
 Empty))) 3170%N 61144487806106130153575124772895849035%positive
 (Branch (Branch (Branch (Branch Empty 3173%N 175458095443608895223302531957005482571%positive
 Empty) 3175%N 3152928806001820450527830346984977332811%positive
 Empty) 3177%N 3833493539843697377454579561848513755723%positive
 (Branch (Branch Empty 3181%N 217993391308726203156224357885976509003%positive
 Empty) 3184%N 366866926836636780921450748637375101515%positive
 Empty)) 3188%N 451937518566871396787294400495317154379%positive
 (Branch (Branch (Branch Empty 3190%N 3684620004315786799689353171097115163211%positive
 Empty) 3194%N 239261039241284857122685270850462022219%positive
 Empty) 3201%N 180775007426748558714917760198126860875%positive
 (Branch Empty 3204%N 393451486752335098379526889842981993035%positive
 Empty)))) 3207%N 1499369179245385104635494363996228680267%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3211%N 1839651546166323568098868971427996891723%positive
 Empty) 3213%N 14770381489161985179707104053835188927051%positive
 Empty) 3217%N 988945628863977409440432452848576363083%positive
 (Branch (Branch Empty 3220%N 202042655359307212681378673162612374091%positive
 Empty) 3224%N 244577951224424520614300499091583400523%positive
 Empty)) 3227%N 361550014853497117429835520396253723211%positive
 (Branch (Branch (Branch Empty 3230%N 786902973504670196759053779685963987531%positive
 Empty) 3233%N 2998738358490770209270988727992457361995%positive
 Empty) 3237%N 3679303092332647136197737942855993784907%positive
 (Branch Empty 3239%N 29540762978323970359414208107670377855563%positive
 Empty))) 3243%N 1977891257727954818880864905697152727627%positive
 (Branch (Branch (Branch (Branch Empty 3246%N 404085310718614425362757346325224749643%positive
 Empty) 3250%N 489155902448849041228600998183166802507%positive
 Empty) 3253%N 1403664763548871161786420255656043870795%positive
 (Branch (Branch Empty 3255%N 25223430448014563604222642775879818672715%positive
 Empty) 3257%N 30667948318749579019636636494788110056011%positive
 Empty)) 3261%N 1743947130469809625249794863087812082251%positive
 (Branch (Branch (Branch Empty 3264%N 2934935414693094247371605989099000822347%positive
 Empty) 3268%N 3615500148534971174298355203962537245259%positive
 Empty) 3270%N 29476960034526294397514825368776921315915%positive
 (Branch Empty 3274%N 1914088313930278856981482166803696187979%positive
 Empty)))))) 3281%N 1446200059413988469719342081585014897227%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3283%N 25265965743879680912155564601808789699147%positive
 Empty) 3285%N 30710483614614696327569558320717081082443%positive
 Empty) 3289%N 1786482426334926933182716689016783108683%positive
 (Branch (Branch Empty 3292%N 2977470710558211555304527815027971848779%positive
 Empty) 3296%N 3658035444400088482231277029891508271691%positive
 Empty)) 3298%N 29519495330391411705447747194705892342347%positive
 (Branch (Branch (Branch Empty 3302%N 1956623609795396164914403992732667214411%positive
 Empty) 3308%N 5614659054195484647145681022624175487563%positive
 Empty) 3310%N 100893721792058254416890571103519274695243%positive
 (Branch (Branch Empty 3312%N 122671793274998316078546545979152440228427%positive
 Empty) 3316%N 6975788521879238500999179452351248333387%positive
 Empty))) 3319%N 11739741658772376989486423956396003293771%positive
 (Branch (Branch (Branch (Branch Empty 3323%N 14462000594139884697193420815850148985419%positive
 Empty) 3325%N 117907840138105177590059301475107685268043%positive
 Empty) 3329%N 7656353255721115427925928667214784756299%positive
 (Branch (Branch Empty 3337%N 5784800237655953878877368326340059593291%positive
 Empty) 3340%N 12590447576074723148144860474975423822411%positive
 Empty)) 3343%N 47979813735852323348335819647879317813835%positive
 (Branch (Branch (Branch Empty 3347%N 58868849477322354179163807085695900580427%positive
 Empty) 3349%N 472652207653183525750627329722726045710923%positive
 Empty) 3353%N 31646260123647277102093838491154443663947%positive
 (Branch Empty 3356%N 6465364971497830805804117541203596016203%positive
 Empty)))) 3360%N 7826494439181584659657615970930668862027%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3363%N 11569600475311907757754736652680119188043%positive
 Empty) 3366%N 25180895152149446296289720949950847646283%positive
 Empty) 3369%N 95959627471704646696671639295758635629131%positive
 (Branch (Branch Empty 3373%N 117737698954644708358327614171391801162315%positive
 Empty) 3375%N 945304415306367051501254659445452091423307%positive
 Empty)) 3379%N 63292520247294554204187676982308887329355%positive
 (Branch (Branch (Branch Empty 3382%N 12930729942995661611608235082407192033867%positive
 Empty) 3386%N 15652988878363169319315231941861337725515%positive
 Empty) 3389%N 23139200950623815515509473305360238377547%positive
 (Branch Empty 3392%N 50361790304298892592579441899901695294027%positive
 Empty))) 3395%N 191919254943409293393343278591517271259723%positive
 (Branch (Branch (Branch (Branch Empty 3399%N 235475397909289416716655228342783602326091%positive
 Empty) 3401%N 1890608830612734103002509318890904182848075%positive
 Empty) 3405%N 126585040494589108408375353964617774660171%positive
 (Branch (Branch Empty 3408%N 25861459885991323223216470164814384069195%positive
 Empty) 3412%N 31305977756726338638630463883722675452491%positive
 Empty)) 3415%N 46278401901247631031018946610720476756555%positive
 (Branch (Branch (Branch Empty 3418%N 100723580608597785185158883799803390589515%positive
 Empty) 3421%N 383838509886818586786686557183034542520907%positive
 Empty) 3425%N 470950795818578833433310456685567204653643%positive
 (Branch Empty 3427%N 3781217661225468206005018637781808365697611%positive
 Empty))))) 3431%N 253170080989178216816750707929235549321803%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3434%N 51722919771982646446432940329628768139851%positive
 Empty) 3438%N 62611955513452677277260927767445350906443%positive
 Empty) 3441%N 92556803802495262062037893221440953514571%positive
 (Branch (Branch Empty 3444%N 201447161217195570370317767599606781180491%positive
 Empty) 3447%N 767677019773637173573373114366069085043275%positive
 Empty)) 3451%N 941901591637157666866620913371134409308747%positive
 (Branch (Branch (Branch Empty 3453%N 7562435322450936412010037275563616731396683%positive
 Empty) 3457%N 506340161978356433633501415858471098645067%positive
 Empty) 3460%N 103445839543965292892865880659257536281163%positive
 (Branch Empty 3464%N 125223911026905354554521855534890701814347%positive
 Empty))) 3467%N 185113607604990524124075786442881907030603%positive
 (Branch (Branch (Branch (Branch Empty 3470%N 402894322434391140740635535199213562362443%positive
 Empty) 3473%N 1535354039547274347146746228732138170088011%positive
 Empty) 3477%N 1883803183274315333733241826742268818618955%positive
 (Branch (Branch Empty 3479%N 15124870644901872824020074551127233462794827%positive
 Empty) 3483%N 1012680323956712867267002831716942197291595%positive
 Empty)) 3486%N 206891679087930585785731761318515072563787%positive
 (Branch (Branch (Branch Empty 3490%N 250447822053810709109043711069781403630155%positive
 Empty) 3493%N 718676358937022034834647170895894462593611%positive
 Empty) 3495%N 12914396389383456565361993101250467161176651%positive
 (Branch Empty 3497%N 15701989539199784458053957885331512349424203%positive
 Empty)))) 3501%N 892900930800542528127894969900959786859083%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3504%N 1502686932322864254654262266418688421788235%positive
 Empty) 3508%N 1851136076049905241240757864428819070319179%positive
 Empty) 3510%N 15092203537677462731527590588813783714495051%positive
 (Branch (Branch Empty 3514%N 980013216732302774774518869403492448991819%positive
 Empty) 3521%N 1437352717874044069669294341791788925188683%positive
 Empty)) 3524%N 3179598436509249002601772331842442167843403%positive
 (Branch (Branch (Branch Empty 3527%N 12239276173412314653850657880105839029647947%positive
 Empty) 3531%N 15026869323228642546542622664186884217895499%positive
 Empty) 3533%N 120955409016249102468837284459266601371302475%positive
 (Branch Empty 3537%N 8057886448687822814812710703984271247276619%positive
 Empty))) 3541%N 1524465003805804316315918241294321587321419%positive
 (Branch (Branch (Branch (Branch Empty 3543%N 25915905064698673377370610102003466984487499%positive
 Empty) 3545%N 31491091364331329162754539670165557360982603%positive
 Empty) 3549%N 1872914147532845302902413839304452235852363%positive
 (Branch (Branch Empty 3552%N 3092486150577488755955148432339909505710667%positive
 Empty) 3556%N 3789384438031570729128139628360170802772555%positive
 Empty)) 3558%N 30271519361286685709701805077130100091124299%positive
 (Branch (Branch (Branch Empty 3562%N 2047138719396365796195661638309517560117835%positive
 Empty) 3568%N 1480908860839924192992606291543055256255051%positive
 Empty) 3570%N 25872348921732793254047298152252200653421131%positive
 (Branch Empty 3572%N 31447535221365449039431227720414291029916235%positive
 Empty)))))))) 3576%N 1829358004566965179579101889553185904785995%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3579%N 3048930007611608632631836482588643174644299%positive
 Empty) 3583%N 3745828295065690605804827678608904471706187%positive
 Empty) 3585%N 30227963218320805586378493127378833760057931%positive
 (Branch (Branch Empty 3589%N 2003582576430485672872349688558251229051467%positive
 Empty) 3595%N 5749410871496176278677177367167155700759115%positive
 Empty)) 3597%N 103315171115067652522895944810003737289423435%positive
 (Branch (Branch (Branch Empty 3599%N 125615916313598275664431663082652098795403851%positive
 Empty) 3603%N 7143207446404340225023159759207678294882891%positive
 Empty) 3606%N 12021495458582914037234098131349507374316107%positive
 (Branch (Branch Empty 3610%N 14809088608399241929926062915430552562563659%positive
 Empty) 3612%N 120737628301419701852220724710510269715970635%positive
 Empty))) 3616%N 7840105733858422198196150955227939591944779%positive
 (Branch (Branch (Branch (Branch Empty 3624%N 11498821742992352557354354734334311401519691%positive
 Empty) 3627%N 25436787492073992020814178654739537342757451%positive
 Empty) 3630%N 97914209387298517230805263040846712237193803%positive
 (Branch (Branch Empty 3634%N 120214954585829140372340981313495073743174219%positive
 Empty) 3636%N 967643272129992819750698275674132810970430027%positive
 Empty)) 3640%N 64463091589502582518501685631874169978223179%positive
 (Branch (Branch (Branch Empty 3644%N 12195720030446434530527345930354572698581579%positive
 Empty) 3646%N 207327240517589387018964880816027735875910219%positive
 Empty) 3648%N 251928730914650633302036317361324458887871051%positive
 (Branch Empty 3652%N 14983313180262762423219310714435617886829131%positive
 Empty)))) 3655%N 24739889204619910047641187458719276045695563%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3659%N 30315075504252565833025117026881366422190667%positive
 Empty) 3661%N 242172154890293485677614440617040800729004619%positive
 Empty) 3665%N 16377109755170926369565293106476140480952907%positive
 (Branch (Branch Empty 3671%N 11847270886719393543940850332344442050050635%positive
 Empty) 3673%N 206978791373862346032378385218017605227379275%positive
 Empty)) 3675%N 251580281770923592315449821763314328239340107%positive
 (Branch (Branch (Branch Empty 3679%N 14634864036535721436632815116425487238298187%positive
 Empty) 3682%N 24391440060892869061054691860709145397164619%positive
 Empty) 3686%N 29966626360525524846438621428871235773659723%positive
 (Branch Empty 3688%N 241823705746566444691027945019030670080473675%positive
 Empty))) 3692%N 16028660611443885382978797508466009832421963%positive
 (Branch (Branch (Branch (Branch Empty 3698%N 45995286971969410229417418937337245606083147%positive
 Empty) 3700%N 826521368920541220183167558480029898315397707%positive
 Empty) 3702%N 1004927330508786205315453304661216790363241035%positive
 (Branch (Branch Empty 3706%N 57145659571234721800185278073661426359073355%positive
 Empty) 3709%N 96171963668663312297872785050796058994539083%positive
 Empty)) 3713%N 118472708867193935439408503323444420500519499%positive
 (Branch (Branch (Branch Empty 3715%N 965901026411357614817765797684082157727775307%positive
 Empty) 3719%N 62720845870867377585569207641823516735568459%positive
 Empty) 3727%N 47389083546877574175763401329377768200206923%positive
 (Branch Empty 3729%N 827915165495449384129513540872070420909521483%positive
 Empty))))) 3731%N 1006321127083694369261799287053257312957364811%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 3735%N 58539456146142885746531260465701948953197131%positive
 Empty) 3738%N 97565760243571476244218767442836581588662859%positive
 Empty) 3742%N 119866505442102099385754485715484943094643275%positive
 (Branch (Branch Empty 3744%N 967294822986265778764111780076122680321899083%positive
 Empty) 3748%N 64114642445775541531915190033864039329692235%positive
 Empty)) 3754%N 183981147887877640917669675749348982424336971%positive
 (Branch (Branch (Branch Empty 3756%N 3306085475682164880732670233920119593261595211%positive
 Empty) 3758%N 4019709322035144821261813218644867161452968523%positive
 Empty) 3762%N 228582638284938887200741112294645705436297803%positive
 (Branch Empty 3765%N 384687854674653249191491140203184235978160715%positive
 Empty))) 3769%N 473890835468775741757634013293777682002082379%positive
 (Branch (Branch (Branch (Branch Empty 3771%N 3863604105645430459271063190736328630911105611%positive
 Empty) 3775%N 250883383483469510342276830567294066942278219%positive
 Empty) 3783%N 367962295775755281835339351498697964848675403%positive
 (Branch (Branch Empty 3786%N 813977199746367744666053716951665194968283723%positive
 Empty) 3789%N 3133254700393552551385768417307094791590246987%positive
 Empty)) 3793%N 3846878546746532491914911402031842359781620299%positive
 (Branch (Branch (Branch Empty 3795%N 30964584708159770232022344821572249951053806155%positive
 Empty) 3799%N 2062818930864082640592053940219973439303187019%positive
 Empty) 3803%N 390263040974285904976875069771346326354655819%positive
 (Branch Empty 3805%N 6634471696562860384606876186112887548029172299%positive
 Empty)))) 3807%N 8061719389268820265665162155562382684411918923%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3811%N 479466021768408397543017942861939772378577483%positive
 Empty) 3814%N 791676454547837121524517998679016833462303307%positive
 Empty) 3818%N 970082416136082106656803744860203725510146635%positive
 (Branch (Branch Empty 3820%N 7749508956489391541683662099745305623328193099%positive
 Empty) 3824%N 524067512165469643826089379407236495390538315%positive
 Empty)) 3830%N 379112668375020593406107210635022145601665611%positive
 (Branch (Branch (Branch Empty 3832%N 6623321323963595073036108326976563367276182091%positive
 Empty) 3834%N 8050569016669554954094394296426058503658928715%positive
 Empty) 3838%N 468315649169143085972250083725615591625587275%positive
 (Branch Empty 3841%N 780526081948571809953750139542692652709313099%positive
 Empty))) 3845%N 958932043536816795086035885723879544757156427%positive
 (Branch (Branch (Branch (Branch Empty 3847%N 7738358583890126230112894240608981442575202891%positive
 Empty) 3851%N 512917139566204332255321520270912314637548107%positive
 Empty) 3857%N 1471849183103021127341357405994791859394705995%positive
 (Branch (Branch Empty 3859%N 26448683805457319045861361871360956746092771915%positive
 Empty) 3861%N 32157674576281158570094505749158937291623758411%positive
 Empty)) 3865%N 1828661106279511097605928898357165643490392651%positive
 (Branch (Branch (Branch Empty 3868%N 3077502837397225993531929121625473887825295947%positive
 Empty) 3872%N 3791126683750205934061072106350221456016669259%positive
 Empty) 3874%N 30908832845163443674168505525890629047288855115%positive
 (Branch Empty 3878%N 2007067067867756082738214644538352535538235979%positive
 Empty)))))) 3886%N 2943698366206042254682714811989583718789413451%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 3889%N 6511817597970941957328429735613321559746280011%positive
 Empty) 3892%N 25066037603148420411086147338456758332721986123%positive
 Empty) 3896%N 30775028373972259935319291216254738878252972619%positive
 (Branch (Branch Empty 3898%N 247716677665278161856178758572577999608430459467%positive
 Empty) 3902%N 16502551446912661124736431521759787514425506379%positive
 Empty)) 3906%N 3122104327794287239815000558170770610837256779%positive
 (Branch (Branch (Branch Empty 3908%N 53075773572502883076855009488903100384233388619%positive
 Empty) 3910%N 64493755114150562125321297244499061475295361611%positive
 Empty) 3914%N 3835728174147267180344143542895518179028630091%positive
 (Branch (Branch Empty 3917%N 6333411636382696972196143989432134667698436683%positive
 Empty) 3921%N 7760659329088656853254429958881629804081183307%positive
 Empty))) 3923%N 61996071651915132333469296797962444986625555019%positive
 (Branch (Branch (Branch (Branch Empty 3927%N 4192540097323757150608715035257891963124316747%positive
 Empty) 3933%N 3032901347000164747248857685080177164813335115%positive
 Empty) 3935%N 52986570591708760584288866615812506938209466955%positive
 (Branch (Branch Empty 3937%N 64404552133356439632755154371408468029271439947%positive
 Empty) 3941%N 3746525193353144687778000669804924733004708427%positive
 Empty)) 3944%N 6244208655588574479630001116341541221674515019%positive
 (Branch (Branch (Branch Empty 3948%N 7671456348294534360688287085791036358057261643%positive
 Empty) 3950%N 61906868671121009840903153924871851540601633355%positive
 Empty) 3954%N 4103337116529634658042572162167298517100395083%positive
 (Branch Empty 3960%N 11774793464824169018730859247958334875157658187%positive
 Empty)))) 3962%N 211589470443658552366890894970887653968742185547%positive
 (Branch (Branch (Branch (Branch (Branch Empty 3964%N 257261396610249268560756045993271498332990077515%positive
 Empty) 3968%N 14629288850236088780847431186857325147923151435%positive
 Empty) 3971%N 24620022699177807948255432973003791102602377803%positive
 (Branch (Branch Empty 3975%N 30329013470001647472488576850801771648133364299%positive
 Empty) 3977%N 247270662761307549393348044207125032378310851147%positive
 Empty)) 3981%N 16056536542942048661905717156306820284305898059%positive
 (Branch (Branch (Branch Empty 3989%N 12131605388000658988995430740320708659253344843%positive
 Empty) 3992%N 26404082315060257799578290434815660023080811083%positive
 Empty) 3995%N 100620962335770171614609160846189407114983635531%positive
 (Branch Empty 3999%N 123456925419065529711541736357381329297107581515%positive
 Empty))) 4001%N 991223522584289137394979605782674372217817528907%positive
 (Branch (Branch (Branch (Branch Empty 4005%N 66367017710827134469210297579401523841797716555%positive
 Empty) 4008%N 13558853080706618870053716709770203795636091467%positive
 Empty) 4012%N 16413348466118538632170288648669194068401584715%positive
 (Branch (Branch Empty 4015%N 24263210776001317977990861480641417318506691147%positive
 Empty) 4018%N 52808164630120515599156580869631320046161623627%positive
 Empty)) 4021%N 201241924671540343229218321692378814229967272523%positive
 (Branch (Branch (Branch Empty 4025%N 246913850838131059423083472714762658594215164491%positive
 Empty) 4027%N 1982447045168578274789959211565348744435635059275%positive
 Empty) 4031%N 132734035421654268938420595158803047683595434571%positive
 (Branch Empty 4034%N 27117706161413237740107433419540407591272184395%positive
 Empty))))) 4038%N 32826696932237077264340577297338388136803170891%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4041%N 48526421552002635955981722961282834637013383755%positive
 Empty) 4044%N 105616329260241031198313161739262640092323248715%positive
 Empty) 4047%N 402483849343080686458436643384757628459934546507%positive
 (Branch (Branch Empty 4051%N 493827701676262118846166945429525317188430330443%positive
 Empty) 4053%N 3964894090337156549579918423130697488871270120011%positive
 Empty)) 4057%N 265468070843308537876841190317606095367190870603%positive
 (Branch (Branch (Branch Empty 4060%N 54235412322826475480214866839080815182544370251%positive
 Empty) 4064%N 65653393864474154528681154594676776273606343243%positive
 Empty) 4067%N 97052843104005271911963445922565669274026768971%positive
 (Branch Empty 4070%N 211232658520482062396626323478525280184646498891%positive
 Empty))) 4073%N 804967698686161372916873286769515256919869094475%positive
 (Branch (Branch (Branch (Branch Empty 4077%N 987655403352524237692333890859050634376860662347%positive
 Empty) 4079%N 7929788180674313099159836846261394977742540241483%positive
 Empty) 4083%N 530936141686617075753682380635212190734381742667%positive
 (Branch (Branch Empty 4086%N 108470824645652950960429733678161630365088741963%positive
 Empty) 4090%N 131306787728948309057362309189353552547212687947%positive
 Empty)) 4093%N 194105686208010543823926891845131338548053539403%positive
 (Branch (Branch (Branch Empty 4096%N 422465317040964124793252646957050560369292999243%positive
 Empty) 4099%N 1609935397372322745833746573539030513839738190411%positive
 Empty) 4103%N 1975310806705048475384667781718101268753721326155%positive
 (Branch Empty 4105%N 15859576361348626198319673692522789955485080484427%positive
 Empty)))) 4109%N 1061872283373234151507364761270424381468763486795%positive
 (Branch (Branch (Branch (Branch (Branch Empty 4112%N 216941649291305901920859467356323260730177485387%positive
 Empty) 4116%N 262613575457896618114724618378707105094425377355%positive
 Empty) 4119%N 388211372416021087647853783690262677096107080267%positive
 (Branch (Branch Empty 4122%N 844930634081928249586505293914101120738585999947%positive
 Empty) 4125%N 3219870794744645491667493147078061027679476382283%positive
 Empty)) 4129%N 3950621613410096950769335563436202537507442653771%positive
 (Branch (Branch (Branch Empty 4131%N 31719152722697252396639347385045579910970160970315%positive
 Empty) 4135%N 2123744566746468303014729522540848762937526975051%positive
 Empty) 4138%N 433883298582611803841718934712646521460354972235%positive
 (Branch Empty 4142%N 525227150915793236229449236757414210188850756171%positive
 Empty))) 4145%N 1507173563497493634397549983738666864020180433483%positive
 (Branch (Branch (Branch (Branch Empty 4147%N 27083452216788294702962034556273619707998999935563%positive
 Empty) 4149%N 32929458766111906375776773887138751786622730107467%positive
 Empty) 4153%N 1872548972830219363948471191917737618934163569227%positive
 (Branch (Branch Empty 4156%N 3151362905494759417376695420544485261133104544331%positive
 Empty) 4160%N 3882113724160210876478537836902626770961070815819%positive
 Empty)) 4162%N 31650644833447366322348549658512004144423789132363%positive
 (Branch (Branch (Branch Empty 4166%N 2055236677496582228723931796007272996391155137099%positive
 Empty) 4173%N 3014347126994987268795099967477333728040360868427%positive
 Empty) 4176%N 6668101220322244564304312049268041277180192225867%positive
 (Branch Empty 4179%N 25667622505623982500952214874579720532707315284555%positive
 Empty))))))) 4183%N 31513629054947594173766954205444852611331045456459%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 4185%N 253661877929244837740727048778319871599032791988811%positive
 Empty) 4189%N 16898612681638564991730105878282022414771720026699%positive
 Empty) 4193%N 3197034831661350133570560571566869105497352436299%positive
 (Branch (Branch Empty 4195%N 54349592138242952270699529716636774793454991440459%positive
 Empty) 4197%N 66041605236890175616329008378367038950702451784267%positive
 Empty)) 4201%N 3927785650326801592672402987925010615325318707787%positive
 (Branch (Branch (Branch Empty 4204%N 6485413515655881699528851445178505899723200657995%positive
 Empty) 4208%N 7946915152986784617732536277894788919379133200971%positive
 Empty) 4210%N 63483977371561095509472559921113543666304569834059%positive
 (Branch (Branch Empty 4214%N 4293161059659527322223324196104081370239301843531%positive
 Empty) 4220%N 3105690979328168701182830269522101416768856652363%positive
 Empty))) 4222%N 54258248285909770838311799414592007104726495656523%positive
 (Branch (Branch (Branch (Branch Empty 4224%N 65950261384556994183941278076322271261973956000331%positive
 Empty) 4228%N 3836441797993620160284672685880242926596822923851%positive
 Empty) 4231%N 6394069663322700267141121143133738210994704874059%positive
 (Branch (Branch Empty 4235%N 7855571300653603185344805975850021230650637417035%positive
 Empty) 4237%N 63392633519227914077084829619068775977576074050123%positive
 Empty)) 4241%N 4201817207326345889835593894059313681510806059595%positive
 (Branch (Branch (Branch Empty 4247%N 12057388507979949075180399869909334912161443478091%positive
 Empty) 4249%N 216667617734306357623696276450188957663991999494731%positive
 Empty) 4251%N 263435670128895251006214191097110014292981840869963%positive
 (Branch Empty 4255%N 14980391782641754911587769535341900951473308564043%positive
 Empty)))) 4258%N 25210903243958075339013563364355882089064836364875%positive
 (Branch (Branch (Branch (Branch (Branch Empty 4262%N 31056909793281687011828302695221014167688566536779%positive
 Empty) 4264%N 253205158667578930578788397268096033155390313069131%positive
 Empty) 4268%N 16441893419972657829791454368058183971129241107019%positive
 (Branch (Branch Empty 4276%N 24114777015959898150360799739818669824322886957643%positive
 Empty) 4279%N 53344809762577956514434496394144330217441537817163%positive
 Empty)) 4282%N 205340980044991860007617718996637764261658522286667%positive
 (Branch (Branch (Branch Empty 4286%N 252109032439580753390135633643558820890648363661899%positive
 Empty) 4288%N 2029295023433958701925816390226558972792262335920715%positive
 Empty) 4292%N 135188901453108519933840847026256179318173760223819%positive
 (Branch Empty 4296%N 25576278653290801068564484572534952843978819500619%positive
 Empty))) 4298%N 434796737105943618165596237733094198347639931533899%positive
 (Branch (Branch (Branch (Branch Empty 4300%N 528332841895121404930632067026936311605619614284363%positive
 Empty) 4304%N 31422285202614412741379223903400084922602549672523%positive
 Empty) 4307%N 51883308125247053596230811561428047197785605274187%positive
 (Branch (Branch Empty 4311%N 63575321223894276941860290223158311355033065617995%positive
 Empty) 4313%N 507871818972488764075780479368908349330436558682699%positive
 Empty)) 4317%N 34345288477276218577786593568832650961914414758475%positive
 (Branch (Branch (Branch Empty 4323%N 24845527834625349609462642156176811334150853229131%positive
 Empty) 4325%N 434065986287278166706494395316736056837811965262411%positive
 Empty) 4327%N 527602091076455953471530224610578170095791648012875%positive
 (Branch Empty 4331%N 30691534383948961282277381487041943412774583401035%positive
 Empty))))) 4334%N 51152557306581602137128969145069905687957639002699%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4338%N 62844570405228825482758447806800169845205099346507%positive
 Empty) 4340%N 507141068153823312616678636952550207820608592411211%positive
 Empty) 4344%N 33614537658610767118684751152474509452086448486987%positive
 (Branch (Branch Empty 4350%N 96459108063839592601443198959274679297291547834955%positive
 Empty) 4352%N 1733340941874450860989570211601511661311935995968075%positive
 Empty)) 4354%N 2107485361031162008049713528776880114343854726969931%positive
 (Branch (Branch (Branch Empty 4358%N 119843134261134039292702156282735207611786468522571%positive
 Empty) 4361%N 201687225951664602712108506914847056712518690929227%positive
 Empty) 4365%N 248455278346253496094626421561768113341508532304459%positive
 (Branch Empty 4367%N 2025641269340631444630307178144768265243122504563275%positive
 Empty))) 4371%N 131535147359781262638331634944465471769033928866379%positive
 (Branch (Branch (Branch (Branch Empty 4379%N 192918216127679185202886397918549358594583095671371%positive
 Empty) 4382%N 426758478100623652115475971153154641739532302547531%positive
 Empty) 4385%N 1642727840359934880060941751973102114093268178303563%positive
 (Branch (Branch Empty 4389%N 2016872259516646027121085069148470567125186909305419%positive
 Empty) 4391%N 16234360187471669615406531121812471782338098687375947%positive
 Empty)) 4395%N 1081511211624868159470726776210049434545390081800779%positive
 (Branch (Branch (Branch Empty 4399%N 204610229226326408548515876580279622751830556015179%positive
 Empty) 4401%N 3478373896847548945324769901864753586781119452281419%positive
 Empty) 4403%N 4226662735160971239445056536215490492844956914285131%positive
 (Branch Empty 4407%N 251378281620915301931033791227200679380820397390411%positive
 Empty)))) 4410%N 415066465001976428769846492491424377582284842203723%positive
 (Branch (Branch (Branch (Branch (Branch Empty 4414%N 508602569791154215534882321785266490840264524954187%positive
 Empty) 4416%N 4062974551779910112606243834951266794643492469471819%positive
 Empty) 4420%N 274762307818209748622292748550661207695315318078027%positive
 (Branch (Branch Empty 4426%N 198764222677002796875701137249414490673206825843275%positive
 Empty) 4428%N 3472527890298225333651955162533888454702495722109515%positive
 Empty)) 4430%N 4220816728611647627772241796884625360766333184113227%positive
 (Branch (Branch (Branch Empty 4434%N 245532275071591690258219051896335547302196667218507%positive
 Empty) 4437%N 409220458452652817097031753160559245503661112031819%positive
 Empty) 4441%N 502756563241830603862067582454401358761640794782283%positive
 (Branch Empty 4443%N 4057128545230586500933429095620401662564868739299915%positive
 Empty))) 4447%N 268916301268886136949478009219796075616691587906123%positive
 (Branch (Branch (Branch (Branch Empty 4453%N 771672864510716740811545591674197434378332382689867%positive
 Empty) 4455%N 13866727534995606887916561692812093290495487967754827%positive
 Empty) 4457%N 16859882888249296064397708230215040914750837815769675%positive
 (Branch (Branch Empty 4461%N 958745074089072314341617250261881660894291748190795%positive
 Empty) 4464%N 1613497807613316821696868055318776453700149527444043%positive
 Empty)) 4468%N 1987642226770027968757011372494144906732068258445899%positive
 (Branch (Branch (Branch Empty 4470%N 16205130154725051557042457425158146121944980036516427%positive
 Empty) 4474%N 1052281178878250101106653079555723774152271430941259%positive
 Empty) 4482%N 795056890708011187502804548997657962692827303377483%positive
 (Branch Empty 4484%N 13890111561192901334607820650135553818809982888442443%positive
 Empty)))))) 4486%N 16883266914446590511088967187538501443065332736457291%positive
 (Branch (Branch (Branch (Branch (Branch (Branch (Branch Empty 4490%N 982129100286366761032876207585342189208786668878411%positive
 Empty) 4493%N 1636881833810611268388127012642236982014644448131659%positive
 Empty) 4497%N 2011026252967322415448270329817605435046563179133515%positive
 (Branch (Branch Empty 4499%N 16228514180922346003733716382481606650259474957204043%positive
 Empty) 4503%N 1075665205075544547797912036879184302466766351628875%positive
 Empty)) 4509%N 3086691458042866963246182366696789737513329530763851%positive
 (Branch (Branch (Branch Empty 4512%N 6828135649609978433847615538450474267832516840782411%positive
 Empty) 4515%N 26283645445758958080975068031569633825492290852878923%positive
 Empty) 4519%N 32269956152266336433937361106375529074002990548908619%positive
 (Branch (Branch Empty 4521%N 259749762999546713846504497948999548517409578998037067%positive
 Empty) 4525%N 17304179385997890551531628419360790952726241308834379%positive
 Empty))) 4529%N 3273763667621222536776254025284473964029288896264779%positive
 (Branch (Branch (Branch (Branch Empty 4531%N 55653982349560783125196318429836057388497911236524619%positive
 Empty) 4533%N 67626603762575539831120904579447847885519310628584011%positive
 Empty) 4537%N 4022052505934644830896540659635210870093126358268491%positive
 (Branch (Branch Empty 4540%N 6641063440031622860317543879862790041316557475281483%positive
 Empty) 4544%N 8137641116658467448558117148564263853444232399288907%positive
 Empty)) 4546%N 65007592828478561801699901359220268714295879511571019%positive
 (Branch (Branch (Branch Empty 4550%N 4396196925091355977956683976810579323125045089270347%positive
 Empty) 4556%N 935361047891777867650358292938421132579796827503179%positive
 Empty) 4560%N 12346765832171467852984729466787158950053318123059787%positive
 (Branch Empty 4561%N 54250940777723116323720780990428425689628215995267659%positive
 Empty)))) 4564%N 9353610478917778676503582929384211325797968275044939%positive
 (Branch (Branch (Branch (Branch (Branch Empty 4565%N 13843343508798312441225302735488632762180993047067211%positive
 Empty) 4567%N 28809120275066758323631035422503370883457742287141451%positive
 Empty) 4570%N 4115588610723822617661576488929052983351106041018955%positive
 (Branch (Branch Empty 4572%N 3741444191567111470601433171753684530319187310017099%positive
 Empty) 4575%N 7482888383134222941202866343507369060638374620035659%positive
 Empty)) 4578%N 50883641005312716000179491135850109612340947416250955%positive
 (Branch (Branch (Branch Empty 4579%N 218500340787519309883123697230415176570640538905082443%positive
 Empty) 4582%N 38911019592297959294254904986238319115319548024191563%positive
 Empty) 4583%N 56869951711820094353141784210656004860851647112280651%positive
 (Branch Empty 4585%N 116733058776893877882764714958714957345958644072577611%positive
 Empty))) 4588%N 17958932119522135058886879224417685745532099088087627%positive
 (Branch (Branch (Branch (Branch Empty 4591%N 8523%positive
 Empty) 4593%N 151883%positive
 Empty) 4595%N 184651%positive
 (Branch (Branch Empty 4599%N 10571%positive
 Empty) 4602%N 5451%positive
 Empty)) 4605%N 33611%positive
 (Branch (Branch (Branch Empty 4608%N 74571%positive
 Empty) 4611%N 287563%positive
 Empty) 4615%N 353099%positive
 (Branch Empty 4617%N 2843467%positive
 Empty))))) 4621%N 189259%positive
 (Branch (Branch (Branch (Branch (Branch (Branch Empty 4624%N 37707%positive
 Empty) 4628%N 45899%positive
 Empty) 4631%N 35659%positive
 (Branch (Branch Empty 4633%N 609099%positive
 Empty) 4635%N 740171%positive
 Empty)) 4639%N 43851%positive
 (Branch (Branch (Branch Empty 4642%N 72523%positive
 Empty) 4646%N 88907%positive
 Empty) 4648%N 711499%positive
 (Branch Empty 4652%N 47947%positive
 Empty))) 4658%N 10059%positive
 (Branch (Branch (Branch (Branch Empty 4661%N 69451%positive
 Empty) 4662%N 298827%positive
 Empty) 4665%N 53067%positive
 (Branch (Branch Empty 4666%N 77643%positive
 Empty) 4668%N 159563%positive
 Empty)) 4671%N 73547%positive
 (Branch (Branch (Branch Empty 4674%N 155467%positive
 Empty) 4677%N 581451%positive
 Empty) 4681%N 712523%positive
 (Branch Empty 4683%N 5693259%positive
 Empty)))) 4687%N 384843%positive
 (Branch (Branch (Branch (Branch (Branch Empty 4690%N 81739%positive
 Empty) 4694%N 98123%positive
 Empty) 4698%N 555%positive
 (Branch (Branch Empty 4701%N 1195%positive
 Empty) 4704%N 4523%positive
 Empty)) 4708%N 5547%positive
 (Branch (Branch (Branch Empty 4710%N 44459%positive
 Empty) 4714%N 2987%positive
 Empty) 4717%N 619%positive
 (Branch Empty 4721%N 747%positive
 Empty))) 4726%N 527%positive
 (Branch (Branch (Branch (Branch Empty 4727%N 2319%positive
 Empty) 4730%N 399%positive
 Empty) 4731%N 591%positive
 (Branch (Branch Empty 4733%N 1231%positive
 Empty) 4736%N 111%positive
 Empty)) 4737%N 287%positive
 (Branch (Branch (Branch Empty 4739%N 4767%positive
 Empty) 4741%N 5791%positive
 Empty) 4745%N 351%positive
 (Branch Empty 4748%N 191%positive
 Empty)))))))))).

Definition loc_reference (v : N) : list bool :=
  match K215DrainData.lookup locations_reference v with
  | Some c => decode_path c
  | None => []
  end.


Theorem source_nodes_checked :
  forallb (node_ok (ptree p215) k215 loc_source) vertices = true.
Proof. vm_compute; reflexivity. Qed.

Theorem reference_nodes_checked :
  forallb (node_ok (ptree dagPerm) k215 loc_reference) vertices = true.
Proof. vm_compute; reflexivity. Qed.

Theorem source_valid v x : k215 v = Some x -> node_ok (ptree p215) k215 loc_source v = true.
Proof.
  intro H; pose proof source_nodes_checked as A; rewrite forallb_forall in A.
  apply A; eapply defined_vertex_member; eauto.
Qed.

Theorem reference_valid v x : k215 v = Some x -> node_ok (ptree dagPerm) k215 loc_reference v = true.
Proof.
  intro H; pose proof reference_nodes_checked as A; rewrite forallb_forall in A.
  apply A; eapply defined_vertex_member; eauto.
Qed.

Theorem source_graph_bound v x R : k215 v = Some x ->
  rm_halts p215 (loc_source v,R) <-> DrainCore.halts k215 v R.
Proof.
  apply source_graph_halts_iff; [exact source_valid|exact k215_closed].
Qed.

Theorem reference_graph_bound v x R : k215 v = Some x ->
  rm_halts dagPerm (loc_reference v,R) <-> DrainCore.halts k215 v R.
Proof.
  apply source_graph_halts_iff; [exact reference_valid|exact k215_closed].
Qed.

Theorem source_entry : ipeq [] (loc_source 0%N).
Proof. apply NormalizedBisim.ibeq_ok; vm_compute; reflexivity. Qed.
Theorem reference_entry : ipeq [] (loc_reference 0%N).
Proof. apply NormalizedBisim.ibeq_ok; vm_compute; reflexivity. Qed.

Theorem source_entry_halts R : rm_halts p215 ([],R) <-> rm_halts p215 (loc_source 0%N,R).
Proof.
  split; apply NormalizedBisim.halts_ipeq; [exact source_entry|apply ipeq_sym; exact source_entry].
Qed.

Theorem reference_entry_halts R : rm_halts dagPerm ([],R) <-> rm_halts dagPerm (loc_reference 0%N,R).
Proof.
  split; apply NormalizedBisim.halts_ipeq; [exact reference_entry|apply ipeq_sym; exact reference_entry].
Qed.

Theorem entry_node : k215 0%N = Some (Test 8 (Arc 9%N []) (Arc 2%N [])).
Proof. vm_compute; reflexivity. Qed.

Theorem p215_graph_halts R : rm_halts p215 ([],R) <-> DrainCore.halts k215 0%N R.
Proof.
  rewrite source_entry_halts; eapply source_graph_bound; exact entry_node.
Qed.

Theorem dagPerm_graph_halts R : rm_halts dagPerm ([],R) <-> DrainCore.halts k215 0%N R.
Proof.
  rewrite reference_entry_halts; eapply reference_graph_bound; exact entry_node.
Qed.

Theorem p215_core_halts R : rm_halts p215 ([],R) <-> core_halts 6 k215 0%N R.
Proof. rewrite p215_graph_halts; symmetry; apply core_halts_iff. Qed.

Theorem dagPerm_core_halts R : rm_halts dagPerm ([],R) <-> core_halts 6 k215 0%N R.
Proof. rewrite dagPerm_graph_halts; symmetry; apply core_halts_iff. Qed.

(** Exact replacement for the existing public source-correspondence theorem. *)
Theorem p215_dagPerm_affine : forall R,
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. intro R; rewrite p215_core_halts, dagPerm_core_halts; reflexivity. Qed.

Print Assumptions p215_core_halts.
Print Assumptions dagPerm_core_halts.
Print Assumptions p215_dagPerm_affine.
