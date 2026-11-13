#!/usr/bin/env python3
"""Bounded, guarded author rebuild of the expanded selected-project cone."""
import fcntl
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
FIRST_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild'
FIRST_RUNNER_SHA = 'c268533ca55c6eeba33066d591f0b5eff5bd6dd52e107350d924420bfe2350e6'
SECOND_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch02'
SECOND_RUNNER_SHA = '49c6edd8afc3dbd377b112c270b782f299f827e78417a03717e033168b29215c'
THIRD_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch03'
THIRD_RUNNER_SHA = '429502951c2bc723dd68e71ca919df0209d69b1b6976cfe5d24ed6c31a87ab11'
FOURTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch04'
FOURTH_RUNNER_SHA = 'b4864212922631685841d278c30540c14cecf26d00cc1314ee35594d7cca1e87'
FIFTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch05'
FIFTH_RUNNER_SHA = 'b50b03308e14fc46ace9e33e89c3d0d57ddcad8cf70280fa0138b5b555d13e9e'
SIXTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch06'
SIXTH_RUNNER_SHA = '7c4799559684e61532af8909b899ab943a6f4bedded1e7e959b83929d05a9a55'
SEVENTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch07'
SEVENTH_RUNNER_SHA = '168325b02ae463e861f41aafee37ff0e532b98bbe25abb288d35d6de8bbd7636'
EIGHTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch08'
EIGHTH_RUNNER_SHA = '11cfdb9eeb11d97fc8e1b1345125e2a6e542d63eb7d2a640e051133035546a4d'
NINTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch09'
NINTH_RUNNER_SHA = '4048ea046785b8e5605ac1cb08d031b5b5c2ee618238d02b08f7c78f710b9a0d'
TENTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch10'
TENTH_RUNNER_SHA = 'a37cd629ddb5c4b3bfa648298c3ccec7ea365d6591c270714f72c5b59b0a7f01'
ELEVENTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch11'
ELEVENTH_RUNNER_SHA = '6542b81b75d5462262410f1547f78743e029cfc153432eeb3ce3b2d2c51e6df6'
TWELFTH_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch12'
TWELFTH_RUNNER_SHA = '015087abf9cebf5b323654d3484c1600fbb44d8f4b5829f51f01a681dd54e16d'
STAGE57_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage57'
STAGE57_RUNNER_SHA = 'bed7793b0ec0d16e11a9ff5a8f82dccba6a1a6593325d76ca941f737d6344646'
STAGE58_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage58'
STAGE58_RUNNER_SHA = 'bfba83662216ed841bff8a1cccb0ab8a05c4087bc304f76417e1e303c39f1063'
STAGE59_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage59'
STAGE59_RUNNER_SHA = '093a526f20ba8a5e0d2fc14cacf571f5f7887f22528bfd24f3f32ec9316ab427'
STAGE60_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-batch-stage60'
STAGE60_RUNNER_SHA = '29d4553136d6ea37822c075fb3770deed9de618825eef00df8d209b6ec6a0786'
STAGE61_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage61'
STAGE61_RUNNER_SHA = 'c21e2b9784b6a67db9f3b50b5dc2d748f85f77d24b205a1c698702e1153e6443'
STAGE62_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage62'
STAGE62_RUNNER_SHA = 'b933ab40fb473cd26a57c103ac02e3e0df3ff2e5ef3f6e3a94d5527a91d6bcc3'
STAGE63_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage63'
STAGE63_RUNNER_SHA = '7390142e3df6f076c75a65322494c012f4bacca470aa00b2c08966d99992aee3'
STAGE64_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage64-retry'
STAGE64_RUNNER_SHA = '2e58ed63b3947506bc7576fdeccd66d22b3c6f8ba611136a60f875b0db3abb80'
STAGE65_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage65'
STAGE65_RUNNER_SHA = '72ef5736a651e852ad4a077b4462a537326cad2e199ababd3076a29d48ab2833'
STAGE66_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage66'
STAGE66_RUNNER_SHA = 'b27a20fb98bfc91fa332f15734fc6f78abec91b68b03962924c64a23bcc00ad3'
STAGE67_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage67'
STAGE67_RUNNER_SHA = '0b246d22c6d26f1f267fffbea18edcb351e1b9dbe5641e7f9cef79698e8d0f47'
STAGE72_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage72'
STAGE72_RUNNER_SHA = '5abf137a74f932735f52d021458130eebb59c6b6d50102043b2bfa15f0a7d98e'
STAGE77_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage77'
STAGE77_RUNNER_SHA = 'aa1dda158d31d81669a6dd766b7a402b9fdd9d1803e2fb9596c1d9f0a6d2f4fa'
STAGE79_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage79-warning-retry'
STAGE79_RUNNER_SHA = 'f749308aa658453e4ace9bb35a7aed47a4eb822e17cf0077cb3e1c92a39a38d9'
STAGE80_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage80'
STAGE80_RUNNER_SHA = 'b0920ef9ee49036368ce79cd948f5136c9ec9808f64dde445068e28b593ff0d8'
STAGE81_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage81-warning-retry'
STAGE81_RUNNER_SHA = '47fcc5e077e12bfefe324f3a20c44792fcb9437dd1902b5853c65bb72e0ceb48'
STAGE82_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage82'
STAGE82_RUNNER_SHA = '971405d78d1a8869533e1adffcfb97ec2009edacef5c2364905bba8119521731'
STAGE84_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage84-warning-retry'
STAGE84_RUNNER_SHA = 'afe5cce022d23567a573b83570e08a4b6c64dac664b77f50bbd7f0cea9b18843'
STAGE85_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage85'
STAGE85_RUNNER_SHA = '83b33b77293779df6530ef69ded48b42912bd7adf4dea36c05a706cbcf89b8c6'
STAGE90_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage90'
STAGE90_RUNNER_SHA = 'cc48775715939835b0529338d1a5fb5348d7902bfb6f197dac430062df2f470b'
STAGE95_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage95'
STAGE95_FAILED_RUNNER_SHA = 'c3c11a6e5f29fa79bf70d6d1c05d1b914b5933c49b765f5370fbcbba011e4846'
STAGE95_RETRY_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage95-long-retry'
STAGE95_RETRY_RUNNER_SHA = '946b1cb9afdb6e53f9530459f4be7561e078340a198eab21ee1dcd16a1152711'
STAGE96_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage96'
STAGE96_RUNNER_SHA = 'd8bc7c3f981595528b92f175cedeccdad402dec3b1b6849a1d64c554bf047b5e'
STAGE101_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage101'
STAGE101_RUNNER_SHA = '4519e5b66e3fc8f1134dcae3926c9de2acf607470e7400916e3a91000f7b4a3d'
STAGE106_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage106'
STAGE106_RUNNER_SHA = '442bea0843ed614166bc00e9ae8daf95930022e763764fb48ceeae2ed5a1fcaf'
STAGE111_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage111'
STAGE111_RUNNER_SHA = '4c88c9d352d251478ba007c483767bd06ca9f9d6a6b1f444030d992f778e5e94'
STAGE116_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage116'
STAGE116_RUNNER_SHA = 'da39b0f0479e2b6ee60e43550f17e163bdc87b5f47c925fbd1180c1db0a6721f'
STAGE121_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage121'
STAGE121_RUNNER_SHA = 'a97de1ec2aa770cede25f2c4cf73a223214c82a4e82a6541298507bfc87212bd'
STAGE126_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage126'
STAGE126_RUNNER_SHA = '60a6d42394910d3ce5e3430d6d806464b7a9be050ff374b0ca5e1d399b6b994d'
STAGE131_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage131'
STAGE131_RUNNER_SHA = 'e9e61e7e89f956025ac09573a2e4cbf88a0c949ffe7a29a68a4911cf5a7d2737'
STAGE136_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage136'
STAGE136_RUNNER_SHA = '22349e4165491b9861c8135761d3859ee3b17735ba73c8433071642c54f62a22'
STAGE141_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage141'
STAGE141_RUNNER_SHA = '5eb2e5bf63d3e738307f5bed0ec8f0af55b15a71f6085925ab812390243128f3'
STAGE146_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage146'
STAGE146_RUNNER_SHA = '583e05f9d4ddea607df3f3b429ee3fd2b39cfa2743ad5639cbe9f66296ab72cb'
STAGE151_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage151'
STAGE151_RUNNER_SHA = 'b3f7a80f3dab1a4b724564ce2a24876178bffa658db323a9e6f2d28e981b051d'
STAGE156_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage156'
STAGE156_RUNNER_SHA = '846026a513dc994527beb78ea81962a6c1011802a8d454385fdc1c68a2e350eb'
STAGE161_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage161'
STAGE161_RUNNER_SHA = '9a796815750b5c24d806faf1a30aaa95d8cd853e20204f4a888392c2e7f89ec6'
STAGE166_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage166'
STAGE166_RUNNER_SHA = 'a255e5a7111d82cf83646551662dd85b88f44c2a69a4caa366cfed58e4e21ecb'
STAGE171_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage171'
STAGE171_RUNNER_SHA = 'f9cd1aca4fa7b13bc7376f1441102f9aec8f0b2ec5a912e5a5102f6690cafd7b'
STAGE176_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage176'
STAGE176_RUNNER_SHA = '07f9149536f2ee41eecd9d215c55b2a224098bde0bfbcfbd787972040cccf173'
STAGE181_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage181'
STAGE181_RUNNER_SHA = '42ceedf84a6b395ac4c95e59204151f4da530d1ea9662392bb079995c69d5ed5'
STAGE186_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage186'
STAGE186_RUNNER_SHA = 'bc0beedd944cbc7bc8936c805c4356f5cde029a7ad664ef61df9fc0e447879b5'
STAGE191_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage191'
STAGE191_RUNNER_SHA = '8e191a7cb9cc003965e7c2008e6ca18f919af9dae06873ccb8451c666bff4ef8'
STAGE196_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage196'
STAGE196_RUNNER_SHA = 'dec186238774609f31e73c1dd338d14d8ef1d3fb1c4e729252890cca84f30dbc'
STAGE197_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage197-warning-retry'
STAGE197_RUNNER_SHA = '43ed40f592406e902d36be404a3adc4f8ab492a5c80522e5e1d52bbed2e50105'
STAGE198_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage198'
STAGE198_RUNNER_SHA = '5e1d52e715eab8436a192b01d7ea3c790b99050510cdf70d1f6a34bc0fbce258'
STAGE203_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage203'
STAGE203_RUNNER_SHA = '19210479c7951ab61b08f861bbff275ea2f70a2e197becc0e1bac021a76c52cd'
STAGE208_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage208'
STAGE208_RUNNER_SHA = 'fd52d98b6e6daee71d9b769a278bdc8d509359ab7aa0dbdd05c7a8558bd0ba68'
STAGE213_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage213'
STAGE213_RUNNER_SHA = '2e70e69c8ab50c7981bcd63c990337173781b8e583b1ada572c94f5267f72463'
STAGE218_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage218'
STAGE218_RUNNER_SHA = '3a50252e01ca6007940d245cfa1610aba016e493ae76ff6cc9aed1d5f03bb98b'
STAGE223_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage223-retry'
STAGE223_RUNNER_SHA = 'd4f61bd012fd1f1229000def41fdd84a94c701c01270d07a12c7dc919e485a02'
STAGE224_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage224-warning-retry'
STAGE224_RUNNER_SHA = '51538b99aad19ba369c9245e2ed65f8550df3ef3f56ab8b2fcfb84da1f0b0e32'
STAGE225_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage225'
STAGE225_RUNNER_SHA = '685f84d96513998c6f06fc9c49cfbb52fb27b92168f84561beb3d56f2e2221f1'
STAGE240_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage240'
STAGE240_RUNNER_SHA = '91b0e60043119aa9a070208ea8df26cf91a256f69bbfbb565884e4f003cdd886'
STAGE250_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage250-warning-retry'
STAGE250_RUNNER_SHA = '50db07e39ae5824530d9d745acff433947bc4e01203b0f234266ff519ecb6ee2'
STAGE251_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage251'
STAGE251_RUNNER_SHA = 'fa1fb68b7edce1314a80504eea5ade742d2c64023427d77d5a01d27241995176'
STAGE251_RETRY_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage251-warning-retry'
STAGE251_RETRY_RUNNER_SHA = 'd201134eb523fb09439440b620dc33fbb12b416e66d5f18982d4c1f5df75d2b7'
STAGE252_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage252'
STAGE252_RUNNER_SHA = '0c05d702c9f34b0b940517485f257496da92583a8e92d3f1729bedcd94584848'
STAGE263_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage263-warning-retry'
STAGE263_RUNNER_SHA = 'a128c1958a4c138913f29c5fa7f25641c8bdd4dd264f4805448068e301f4cad9'
STAGE264_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage264'
STAGE264_RUNNER_SHA = '5111d5aac1eed68987fea5e90a8da9ee516e6394cfc8023e2e81dbd6502c6186'
STAGE266_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage266-warning-retry'
STAGE266_RUNNER_SHA = 'd9ebd6f7e6f1db823ebf419fea9e0f0ebfb61096d24d8f61e30f3172906252cd'
STAGE267_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage267'
STAGE267_RUNNER_SHA = '43668d14c51bf527732c0cebd29d5982bfa66f9ae855b4d05b539f9a3b7222e0'
STAGE268_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage268-warning-retry'
STAGE268_RUNNER_SHA = 'd1e8817ee880cd4e339077ce5024363f52ca37433ab728a6c1c18b00537fdcca'
STAGE269_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage269'
STAGE269_RUNNER_SHA = 'f8cc928655fa5ae5e6b503d7fc731b2dd7f0cfac9d7ca68c8f61b2c4247dcae7'
STAGE270_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage270-warning-retry'
STAGE270_RUNNER_SHA = 'b65818a868c530d4826bb4ec55f9c51ef89f13f25f7805566678175f480d5d25'
STAGE271_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage271'
STAGE271_RUNNER_SHA = 'c0d248780c823f6b432681311c79118a92b6933b3f36a4a75a6cde608546ef40'
STAGE272_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage272-warning-retry'
STAGE272_RUNNER_SHA = 'b6c44daa4f2cad0c5bf2146fc88c8b427a2d0f739a49dbdccddae8bb06b8b626'
STAGE273_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage273'
STAGE273_RUNNER_SHA = '417b6614486f367c2116b37d36199bb4d7dcad42d59a921fcd7f927a4c00d591'
STAGE275_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage275-warning-retry3'
STAGE275_RUNNER_SHA = '8eafa4193c0d42bb6a0e750e8e2d0bcea2dfe887ee8e490edcf4e6b2970e5ca2'
STAGE276_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage276'
STAGE276_FAILED_RUNNER_SHA = 'f2b3dbea1661fc4702625bafcd7aa474227f4d73b3d77a7cb08cee0098df9788'
STAGE276_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage276-source-retry'
STAGE276_RUNNER_SHA = '1f6f2b0daf803bcde884325e0f0e98696b51f54edac0aaf03b9bc9fa558324b6'
STAGE277_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage277'
STAGE277_RUNNER_SHA = '73f9956a01818dc013d55eb43fe22e1d8838a8f2768ff3c3462ea39a18b95918'
STAGE285_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage285-memory-retry'
STAGE285_RUNNER_SHA = '9d04ae692ea112c478f5ff96e31c82748e1b08184e86554071b0deb6767b8621'
STAGE286_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage286'
STAGE286_RUNNER_SHA = 'f9423dedf276c701995c5b2290f6acbe560ac0a13a7ad6145b36005388ada6b2'
STAGE301_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage301'
STAGE301_FAILED_RUNNER_SHA = '5dcc296672e512a4be1dca0a632dd9fa4e1d9fe9fbaf84d821f001fcf767d506'
STAGE301_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage301-warning-retry'
STAGE301_RUNNER_SHA = '653c2dc346fd9f8c82d9545efefdd877db3eb535a0c1707b4b18724ff1f74fe4'
STAGE306_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage302'
STAGE306_FAILED_RUNNER_SHA = '425b92e4046f6f5e3b66a6a3c8272278000ec130f8c1dc08bd523e01ec27ce2e'
STAGE306_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage306-warning-retry'
STAGE306_RUNNER_SHA = '918245a5afe6d684ba7c476fc776d7e91ebe74ccfe8cde0114bf355272da63d2'
STAGE307_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage307'
STAGE307_FAILED_RUNNER_SHA = 'c7a3946a570839883ed7df4fdd1f97e8e8ba66d30efb17bb27270084c802fd4a'
STAGE307_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage307-warning-retry'
STAGE307_RUNNER_SHA = '7b5ac6eb44c1e8856e71a15e2537d9ce5a5056af76836fc34ca950323e2ee470'
STAGE310_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage308'
STAGE310_FAILED_RUNNER_SHA = 'f593c2933363f230bd5ec416e95f98009c79dd9f4e01e09747f91f7d7ae2ba99'
STAGE310_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage310-warning-retry'
STAGE310_RUNNER_SHA = 'a7fa3991b1833b7b166ae122ca07fea5288fd768832baf85c264ca017d4e1717'
STAGE311_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage311'
STAGE311_FAILED_RUNNER_SHA = '6700067cb9c241dfdf182d1c293b0316d579a0fb0227a097563041bbd196b5b1'
STAGE311_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage311-warning-retry'
STAGE311_RUNNER_SHA = '6c9466e6b29a99de83035b3c0a1cbad25d9d45797accb6c8549a818f1ba02945'
STAGE312_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage312'
STAGE312_FAILED_RUNNER_SHA = '48d94f49639d7f42c70febe0cc4cae724fd261b38e5ef88795bc30aace8859d1'
STAGE312_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage312-warning-retry'
STAGE312_RUNNER_SHA = 'e4ec62df25846188a1e55a4c0f1cb00b797f934f03b1bc84a56aea8da0e9cee7'
STAGE314_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage313'
STAGE314_FAILED_RUNNER_SHA = 'bf437c0338f77e905659557490f6089335a86c6bdd0f8a0e1fb32cc2e630da1b'
STAGE314_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage314-warning-retry'
STAGE314_RUNNER_SHA = '0d569a131b05f2a2a2071ee72c05261103ab6c058c85a20dd01f98fd61ab263f'
STAGE316_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage315'
STAGE316_FAILED_RUNNER_SHA = '51248a1ac3774525cc64bc60d084d715e90e566ddafde171518166d45fa7c31b'
STAGE316_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage316-warning-retry'
STAGE316_RUNNER_SHA = 'df561cfe13086dc1f6281f5818c2c64a159e12b17e34eea58097b22296138f27'
STAGE317_FAILED_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage317'
STAGE317_FAILED_RUNNER_SHA = '9550d97a188c857117f9159dce5eb46972dce0b589305bf2b2c5dd45c1f67311'
STAGE317_PACKET = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage317-source-retry'
STAGE317_RUNNER_SHA = 'a2390feba5e6b02c062aa9b7da6335373611056dc39aa22a5696c8513d3aeced'
WARNING316_VERIFY_SHA = 'e390dd8d324c6b2f15dc59d62df4f28b6c2671228c068f512dace7eb336e63c4'
WARNING316_EXPECTED_SHA = '8564b0ee9aec933716b0c7ee784d2c23c7ae8762a74c41f41ecb4dcaa8f5e42e'
WARNING314_VERIFY_SHA = '6be60bc8eb0b0208f10869272b40ab37eecedd699fd7f70cfea98913f62d0702'
WARNING314_EXPECTED_SHA = '9209c94e607bf7566d7cf385cc7b8390daa22e082327d1541ca38daf51cb2f60'
WARNING312_VERIFY_SHA = '8c414bf62e643d32067d8ac1921b561e95146f9a6490291bcd6efaf2b9dd6250'
WARNING312_EXPECTED_SHA = '19a642ca393e6836a231c71931ca292cc7d4c26f758c35774142409520407b44'
WARNING311_VERIFY_SHA = 'a2b1145b17d9ad678043c6f46915fedffa6c4c29de706da1344810e6da32a062'
WARNING311_EXPECTED_SHA = 'a376d7ebf9e720a00e7a379edfb318b8567a7eefceb4a87171521ea009cc857a'
WARNING310_VERIFY_SHA = 'fac1a5aa52dbac36677ce9d5277bd3e130fbd72247e0a75aaeedb5f24431e304'
WARNING310_EXPECTED_SHA = 'ad7050a6d57fa2d9b1846bd28e563f7fca2692fbd713b97f26236f58f78366e1'
WARNING307_VERIFY_SHA = '25ff6103ff26501fa56a11eaeaa01beb9d76241e70d9e2598d050c59498d3b43'
WARNING307_EXPECTED_SHA = '58fc10967fd146ce94d7feb1082593d2caf3590b7e40f8272573d57501fe7399'
WARNING306_VERIFY_SHA = '63dd2d1f061ac69f0a00b9b31d6f063b3cf4ec33e03aa6a33bb7e02ee857a593'
WARNING306_EXPECTED_SHA = '058a4167adde870fdbacb865da687417046ac070c86a7bc7304bf550aecc9ac7'
WARNING301_VERIFY_SHA = '07ad10de08cd8a7e9a161fbc2ce2e4ff136b5e4ea1f496cc0a23435071bd305b'
WARNING301_EXPECTED_SHA = 'b566b1b13506219eab779caa58a23953a27cc07159d002bce1b475be247861c8'
WARNING275_VERIFY_SHA = '553a664416f4cd22d8d5c33092dc96ff89ee84a287b34a4cc6bc2605a158e5ec'
WARNING275_EXPECTED_SHA = '72c3c834f884ee3d444c96f9db8d23779f3ffdbcc1fab4a329a7211c040ea88d'
WARNING272_VERIFY_SHA = '5809bf51a2d9395d5e42210241d3d7890e89b85eedae6452d618f9a28160ffb8'
WARNING272_EXPECTED_SHA = '5101c4dfb5bcce0b75c54a4aed364edfd4e36a792ec5e756e09179cc22c6b685'
WARNING270_VERIFY_SHA = 'ca07d92b5a7ddb0f827e2f4f1d3296b04091405a16569cb60d6d90d2fc6ae39d'
WARNING270_EXPECTED_SHA = 'c02c9690e3e5fc45eaaddc4d9377f48067984adc34188db64a4990cb80c354b7'
WARNING268_VERIFY_SHA = 'a0c5ed7999834c026c21991481c21d85d5ea377be8bfb4a73d0a70af4f02f3d9'
WARNING268_EXPECTED_SHA = 'af050e63c91d13e3e7983dd1d41541a2bd07d5f85f7bfafc2b9d6fefbea233d0'
WARNING266_VERIFY_SHA = 'ee6e2d4004b4197c5b4d2e52388e2673e3b801bedcffc1fa4805eabf684b4b4f'
WARNING266_EXPECTED_SHA = '34b600113b35c63779639db4b80bb78b6027c160417fff80411fb2abb3a15f7c'
WARNING263_VERIFY_SHA = '74bac949c7853b8156a045757fee0eda3180e46707088af9fa28cdfb07252296'
WARNING263_EXPECTED_SHA = 'a0013896c8f1bd92a651342aa1f1d0c399097b72831a4731147699e81bbeaf71'
WARNING251_VERIFY_SHA = '3a02a2e3941d6e5019aaf5939aaa5f320e0a5ec23f2f2e7c8cd76f7a38cdcd37'
WARNING251_EXPECTED_SHA = '8ada12747e090fa5db22e1b507bc35b463d3247b03d418868a593128b191a32c'
WARNING250_VERIFY_SHA = '45c04e3ace2b77f1f06d51ee3058f5148f1692b31df2f4a12c3eda787637352d'
WARNING250_EXPECTED_SHA = '4907ef8efcf1fb484476b1ea67f1bdf595432f1b3df358ca7ee4a336395794f1'
WARNING224_VERIFY_SHA = '91647165a79121ba71645006675932d96bda7ebb11a7f5c6506964392a7dc940'
WARNING224_EXPECTED_SHA = '8ca0f9a532f94049c3016af5efdfdec0e2ff3c3457f6c0c56efd0d69a65108b0'
WARNING_VERIFY_SHA = '7330742b4934efe8a35fd68f55d6e7e2aa329092a2881cfeba755939dba48c9c'
WARNING_EXPECTED_SHA = '99e2bfd537967357a084cd466ee67eaad26a8892b135d9b66dd1c591e0a81f00'
WARNING81_VERIFY_SHA = 'd05bd282b32a40eb97d72e9dbb05eb904b6d674fa0e9eecf1e9f04650848fada'
WARNING81_EXPECTED_SHA = 'c8876f4a91179aaf43af11f90ca9d67d00491f874c2ded22706c2c4545e9bdfd'
WARNING84_VERIFY_SHA = 'c525d03a80ea7b8b66a82a090f6ca9020bf89507722d9b2d5f861b7de2bffe02'
WARNING84_EXPECTED_SHA = 'ce41a6fcc3c0116286d878add6ddb33c1f9d39970c3d4285d71e77dcf08b9ddb'
WARNING197_VERIFY_SHA = '21c335e90ae8247f5f47638a46d8b6550e3d01a9a27e043a151474cbda7f74fa'
WARNING197_EXPECTED_SHA = '7c0c01e0b041b48ea83b9e4fe5cad46ddbe2c03c542b34ce6107a5aa3c630145'
REPO = HERE.parents[4]
MANIFEST = HERE.parent / 'compact12-ipra-integration-build/observations/attempt01/manifest.json'
FULL_SCAN = HERE.parent / 'compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
OLD_CONE = STAGE64_PACKET / 'cone-repinned.json'
PREV_CONE = STAGE276_PACKET / 'cone-repinned.json'
CONE = STAGE317_PACKET / 'cone-repinned.json'
EXPECT = {
    MANIFEST: '36ee7a0c7b881cefffafebd7d3a3ff678aec8010ca2019fe71dc8ff8ed29486e',
    FULL_SCAN: 'bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2',
    OLD_CONE: 'c9f4190a0d8807e5643f245a59ca53b23e52ca6c1dc1c1b74a5028651da049ec',
    PREV_CONE: 'aa2ec030a843382be4dc6fe621174d80d46bf9799d9b52d1616dac52661a9699',
    CONE: 'eb5a8a3c8efb7b1d936d4c77ba2c6d201aff6d03f23c9e1697dd2b518aefcbf2',
}
OVERLAY = Path('/tmp/compact12-ipra-integrated-20261102/lib')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PROJECT = Path('/tmp/compact12-ipra-expanded-coherent-20261102')
LIB = PROJECT / 'lib'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def check_resources():
    available = next(int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines()
                     if line.startswith('MemAvailable:'))
    if available < 8 * 1024 * 1024:
        raise RuntimeError('less than 8 GiB MemAvailable before a new stage')
    ps = subprocess.run(['ps', '-eo', 'args='], capture_output=True, text=True, check=True)
    live = [line for line in ps.stdout.splitlines() if '/bin/lean ' in line]
    if len(live) >= 2:
        raise RuntimeError('two Lean children already live before a new stage')

def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    if not path.is_file():
        raise RuntimeError(f'not a regular file or dangling dependency: {path}')
    return {'sha256': digest(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}

def check_pins():
    for path, value in EXPECT.items():
        if digest(path) != value:
            raise RuntimeError(f'prerequisite drift: {path}')

def check_sources(cone):
    for m, row in cone['candidate_sources'].items():
        if len(row['canonical_candidates']) != 1 or not row['selected_imports_match']:
            raise RuntimeError(f'unsupported source: {m}')
        if digest(REPO / row['canonical_candidates'][0]) != row['source_sha256']:
            raise RuntimeError(f'source drift: {m}')

def verify_overlay(manifest):
    selected = manifest['overlay']
    actual = {p.relative_to(OVERLAY).as_posix() for p in OVERLAY.rglob('*') if p.is_file()}
    if actual != set(selected):
        raise RuntimeError('original overlay file set changed')
    for rel, row in selected.items():
        p = OVERLAY / rel
        if digest(p) != row['sha256'] or str(p.resolve(strict=True)) != row['resolved']:
            raise RuntimeError(f'original overlay drift: {rel}')

def receipt_dir(index):
    batch = (index - 1) // 5 + 1
    base = (FIRST_PACKET if index <= 5 else SECOND_PACKET if index <= 10 else
            THIRD_PACKET if index <= 15 else FOURTH_PACKET if index <= 20 else
            FIFTH_PACKET if index <= 25 else SIXTH_PACKET if index <= 30 else
            SEVENTH_PACKET if index <= 35 else EIGHTH_PACKET if index <= 40 else
            NINTH_PACKET if index <= 45 else TENTH_PACKET if index <= 50 else
            ELEVENTH_PACKET if index <= 55 else TWELFTH_PACKET if index <= 56 else
            STAGE57_PACKET if index <= 57 else STAGE58_PACKET if index <= 58 else
            STAGE59_PACKET if index <= 59 else STAGE60_PACKET if index <= 60 else
            STAGE61_PACKET if index <= 61 else STAGE62_PACKET if index <= 62 else
            STAGE63_PACKET if index <= 63 else STAGE64_PACKET if index <= 64 else
            STAGE65_PACKET if index <= 65 else STAGE66_PACKET if index <= 66 else
            STAGE67_PACKET if index <= 71 else STAGE72_PACKET if index <= 76 else
            STAGE77_PACKET if index <= 78 else STAGE79_PACKET if index <= 79 else
            STAGE80_PACKET if index <= 80 else STAGE81_PACKET if index <= 81 else
            STAGE82_PACKET if index <= 83 else STAGE84_PACKET if index <= 84 else
            STAGE85_PACKET if index <= 89 else STAGE90_PACKET if index <= 94 else
            STAGE95_RETRY_PACKET if index <= 95 else STAGE96_PACKET if index <= 100 else
            STAGE101_PACKET if index <= 105 else STAGE106_PACKET if index <= 110 else
            STAGE111_PACKET if index <= 115 else STAGE116_PACKET if index <= 120 else
            STAGE121_PACKET if index <= 125 else STAGE126_PACKET if index <= 130 else
            STAGE131_PACKET if index <= 135 else STAGE136_PACKET if index <= 140 else
            STAGE141_PACKET if index <= 145 else STAGE146_PACKET if index <= 150 else
            STAGE151_PACKET if index <= 155 else STAGE156_PACKET if index <= 160 else
            STAGE161_PACKET if index <= 165 else STAGE166_PACKET if index <= 170 else
            STAGE171_PACKET if index <= 175 else STAGE176_PACKET if index <= 180 else
            STAGE181_PACKET if index <= 185 else STAGE186_PACKET if index <= 190 else
            STAGE191_PACKET if index <= 195 else STAGE196_PACKET if index <= 196 else
            STAGE197_PACKET if index <= 197 else STAGE198_PACKET if index <= 202 else
            STAGE203_PACKET if index <= 207 else STAGE208_PACKET if index <= 212 else
            STAGE213_PACKET if index <= 217 else STAGE218_PACKET if index <= 222 else STAGE223_PACKET if index <= 223 else STAGE224_PACKET if index <= 224 else STAGE225_PACKET if index <= 239 else STAGE240_PACKET if index <= 249 else STAGE250_PACKET if index <= 250 else STAGE251_RETRY_PACKET if index <= 251 else STAGE252_PACKET if index <= 262 else STAGE263_PACKET if index <= 263 else STAGE264_PACKET if index <= 265 else STAGE266_PACKET if index <= 266 else STAGE267_PACKET if index <= 267 else STAGE268_PACKET if index <= 268 else STAGE269_PACKET if index <= 269 else STAGE270_PACKET if index <= 270 else STAGE271_PACKET if index <= 271 else STAGE272_PACKET if index <= 272 else STAGE273_PACKET if index <= 274 else STAGE275_PACKET if index <= 275 else STAGE276_PACKET if index <= 276 else STAGE277_PACKET if index <= 284 else STAGE285_PACKET if index <= 285 else STAGE286_PACKET if index <= 300 else STAGE301_PACKET if index <= 301 else STAGE306_FAILED_PACKET if index <= 305 else STAGE306_PACKET if index <= 306 else STAGE307_PACKET if index <= 307 else STAGE310_FAILED_PACKET if index <= 309 else STAGE310_PACKET if index <= 310 else STAGE311_PACKET if index <= 311 else STAGE312_PACKET if index <= 312 else STAGE314_FAILED_PACKET if index <= 313 else STAGE314_PACKET if index <= 314 else STAGE316_FAILED_PACKET if index <= 315 else STAGE316_PACKET if index <= 316 else STAGE317_PACKET if index <= 317 else HERE)
    return base / 'observations' / f'batch-{batch:03d}' / f'stage-{index:04d}'

def check_prior(order, base):
    previous, gap = [], False
    for index, module in enumerate(order, 1):
        obs = receipt_dir(index)
        terminal = obs / 'terminal.json'
        if not terminal.exists():
            if obs.exists():
                raise RuntimeError(f'incomplete previous stage: {obs}')
            gap = True
            continue
        if gap:
            raise RuntimeError(f'noncontiguous stage: {obs}')
        row = json.loads(terminal.read_text())
        output = LIB / (module.replace('.', '/') + '.olean')
        if (row.get('module') != module or not row.get('success') or row.get('exit_code') != 0 or
            not output.is_file() or output.is_symlink() or digest(output) != row.get('object_sha256') or
            digest(obs / 'compile.log') != row.get('log_sha256') or
            row.get('guards') != {p: record(p) for p in row.get('guards', {})}):
            raise RuntimeError(f'prior stage validation failed: {obs}')
        if index == 79:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE79_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 79 warning baseline no longer validates')
        if index == 81:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE81_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 81 warning baseline no longer validates')
        if index == 84:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE84_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 84 warning baseline no longer validates')
        if index == 197:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE197_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 197 warning baseline no longer validates')
        if index == 224:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE224_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 224 warning baseline no longer validates')
        if index == 250:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE250_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 250 warning baseline no longer validates')
        if index == 251:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE251_RETRY_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 251 warning baseline no longer validates')
        if index == 263:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE263_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 263 warning baseline no longer validates')
        if index == 266:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE266_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 266 warning baseline no longer validates')
        if index == 268:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE268_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 268 warning baseline no longer validates')
        if index == 270:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE270_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 270 warning baseline no longer validates')
        if index == 272:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE272_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 272 warning baseline no longer validates')
        if index == 275:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE275_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 275 warning baseline no longer validates')
        if index == 301:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE301_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 301 warning baseline no longer validates')
        if index == 306:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE306_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 306 warning baseline no longer validates')
        if index == 307:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE307_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 307 warning baseline no longer validates')
        if index == 310:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE310_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 310 warning baseline no longer validates')
        if index == 311:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE311_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 311 warning baseline no longer validates')
        if index == 312:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE312_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 312 warning baseline no longer validates')
        if index == 314:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE314_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 314 warning baseline no longer validates')
        if index == 316:
            verify = subprocess.run([sys.executable, '-I', '-B', str(STAGE316_PACKET / 'verify_warning.py'),
                                     str(obs / 'compile.log')], capture_output=True, text=True)
            if not row.get('accepted_exact_warning') or verify.returncode != 0 or verify.stderr:
                raise RuntimeError('stage 316 warning baseline no longer validates')
        previous.append(row)
    expected = set(base) | {m.replace('.', '/') + '.olean' for m in order[:len(previous)]}
    actual = {p.relative_to(LIB).as_posix() for p in LIB.rglob('*') if p.is_file()}
    if actual != expected:
        raise RuntimeError('merged build file set mismatch')
    for rel, row in base.items():
        p = LIB / rel
        if not p.is_symlink() or digest(p) != row['sha256'] or str(p.resolve(strict=True)) != row['resolved']:
            raise RuntimeError(f'merged selected input drift: {rel}')
    return previous

def main():
    count = int(sys.argv[1]) if len(sys.argv) == 2 else 1
    if not 1 <= count <= 15:
        raise ValueError('pass a stage count from 1 through 15')
    if shutil.disk_usage('/tmp').free < 4 * 1024**3:
        raise RuntimeError('less than 4 GiB free')
    if digest(FIRST_PACKET / 'run.py') != FIRST_RUNNER_SHA:
        raise RuntimeError('first batch runner drift')
    if digest(SECOND_PACKET / 'run.py') != SECOND_RUNNER_SHA:
        raise RuntimeError('second batch runner drift')
    if digest(THIRD_PACKET / 'run.py') != THIRD_RUNNER_SHA:
        raise RuntimeError('third batch runner drift')
    if digest(FOURTH_PACKET / 'run.py') != FOURTH_RUNNER_SHA:
        raise RuntimeError('fourth batch runner drift')
    if digest(FIFTH_PACKET / 'run.py') != FIFTH_RUNNER_SHA:
        raise RuntimeError('fifth batch runner drift')
    if digest(SIXTH_PACKET / 'run.py') != SIXTH_RUNNER_SHA:
        raise RuntimeError('sixth batch runner drift')
    if digest(SEVENTH_PACKET / 'run.py') != SEVENTH_RUNNER_SHA:
        raise RuntimeError('seventh batch runner drift')
    if digest(EIGHTH_PACKET / 'run.py') != EIGHTH_RUNNER_SHA:
        raise RuntimeError('eighth batch runner drift')
    if digest(NINTH_PACKET / 'run.py') != NINTH_RUNNER_SHA:
        raise RuntimeError('ninth batch runner drift')
    if digest(TENTH_PACKET / 'run.py') != TENTH_RUNNER_SHA:
        raise RuntimeError('tenth batch runner drift')
    if digest(ELEVENTH_PACKET / 'run.py') != ELEVENTH_RUNNER_SHA:
        raise RuntimeError('eleventh batch runner drift')
    if digest(TWELFTH_PACKET / 'run.py') != TWELFTH_RUNNER_SHA:
        raise RuntimeError('twelfth batch runner drift')
    if digest(STAGE57_PACKET / 'run.py') != STAGE57_RUNNER_SHA:
        raise RuntimeError('stage 57 runner drift')
    if digest(STAGE58_PACKET / 'run.py') != STAGE58_RUNNER_SHA:
        raise RuntimeError('stage 58 runner drift')
    if digest(STAGE59_PACKET / 'run.py') != STAGE59_RUNNER_SHA:
        raise RuntimeError('stage 59 runner drift')
    if digest(STAGE60_PACKET / 'run.py') != STAGE60_RUNNER_SHA:
        raise RuntimeError('stage 60 runner drift')
    if digest(STAGE61_PACKET / 'run.py') != STAGE61_RUNNER_SHA:
        raise RuntimeError('stage 61 runner drift')
    if digest(STAGE62_PACKET / 'run.py') != STAGE62_RUNNER_SHA:
        raise RuntimeError('stage 62 runner drift')
    if digest(STAGE63_PACKET / 'run.py') != STAGE63_RUNNER_SHA:
        raise RuntimeError('stage 63 runner drift')
    if digest(STAGE64_PACKET / 'run.py') != STAGE64_RUNNER_SHA:
        raise RuntimeError('stage 64 retry runner drift')
    if digest(STAGE65_PACKET / 'run.py') != STAGE65_RUNNER_SHA:
        raise RuntimeError('stage 65 runner drift')
    if digest(STAGE66_PACKET / 'run.py') != STAGE66_RUNNER_SHA:
        raise RuntimeError('stage 66 runner drift')
    if digest(STAGE67_PACKET / 'run.py') != STAGE67_RUNNER_SHA:
        raise RuntimeError('stages 67–71 runner drift')
    if digest(STAGE72_PACKET / 'run.py') != STAGE72_RUNNER_SHA:
        raise RuntimeError('stages 72–76 runner drift')
    if digest(STAGE77_PACKET / 'run.py') != STAGE77_RUNNER_SHA:
        raise RuntimeError('stages 77–78 runner drift')
    if digest(STAGE79_PACKET / 'run.py') != STAGE79_RUNNER_SHA:
        raise RuntimeError('stage 79 retry runner drift')
    if digest(STAGE80_PACKET / 'run.py') != STAGE80_RUNNER_SHA:
        raise RuntimeError('stage 80 runner drift')
    if digest(STAGE81_PACKET / 'run.py') != STAGE81_RUNNER_SHA:
        raise RuntimeError('stage 81 retry runner drift')
    if digest(STAGE82_PACKET / 'run.py') != STAGE82_RUNNER_SHA:
        raise RuntimeError('stages 82–83 runner drift')
    if digest(STAGE84_PACKET / 'run.py') != STAGE84_RUNNER_SHA:
        raise RuntimeError('stage 84 retry runner drift')
    if digest(STAGE85_PACKET / 'run.py') != STAGE85_RUNNER_SHA:
        raise RuntimeError('stages 85–89 runner drift')
    if digest(STAGE90_PACKET / 'run.py') != STAGE90_RUNNER_SHA:
        raise RuntimeError('stages 90–94 runner drift')
    if digest(STAGE95_FAILED_PACKET / 'run.py') != STAGE95_FAILED_RUNNER_SHA:
        raise RuntimeError('failed stage 95 runner drift')
    if digest(STAGE95_RETRY_PACKET / 'run.py') != STAGE95_RETRY_RUNNER_SHA:
        raise RuntimeError('stage 95 retry runner drift')
    if digest(STAGE96_PACKET / 'run.py') != STAGE96_RUNNER_SHA:
        raise RuntimeError('stages 96–100 runner drift')
    if digest(STAGE101_PACKET / 'run.py') != STAGE101_RUNNER_SHA:
        raise RuntimeError('stages 101–105 runner drift')
    if digest(STAGE106_PACKET / 'run.py') != STAGE106_RUNNER_SHA:
        raise RuntimeError('stages 106–110 runner drift')
    if digest(STAGE111_PACKET / 'run.py') != STAGE111_RUNNER_SHA:
        raise RuntimeError('stages 111–115 runner drift')
    if digest(STAGE116_PACKET / 'run.py') != STAGE116_RUNNER_SHA:
        raise RuntimeError('stages 116–120 runner drift')
    if digest(STAGE121_PACKET / 'run.py') != STAGE121_RUNNER_SHA:
        raise RuntimeError('stages 121–125 runner drift')
    if digest(STAGE126_PACKET / 'run.py') != STAGE126_RUNNER_SHA:
        raise RuntimeError('stages 126–130 runner drift')
    if digest(STAGE131_PACKET / 'run.py') != STAGE131_RUNNER_SHA:
        raise RuntimeError('stages 131–135 runner drift')
    if digest(STAGE136_PACKET / 'run.py') != STAGE136_RUNNER_SHA:
        raise RuntimeError('stages 136–140 runner drift')
    if digest(STAGE141_PACKET / 'run.py') != STAGE141_RUNNER_SHA:
        raise RuntimeError('stages 141–145 runner drift')
    if digest(STAGE146_PACKET / 'run.py') != STAGE146_RUNNER_SHA:
        raise RuntimeError('stages 146–150 runner drift')
    if digest(STAGE151_PACKET / 'run.py') != STAGE151_RUNNER_SHA:
        raise RuntimeError('stages 151–155 runner drift')
    if digest(STAGE156_PACKET / 'run.py') != STAGE156_RUNNER_SHA:
        raise RuntimeError('stages 156–160 runner drift')
    if digest(STAGE161_PACKET / 'run.py') != STAGE161_RUNNER_SHA:
        raise RuntimeError('stages 161–165 runner drift')
    if digest(STAGE166_PACKET / 'run.py') != STAGE166_RUNNER_SHA:
        raise RuntimeError('stages 166–170 runner drift')
    if digest(STAGE171_PACKET / 'run.py') != STAGE171_RUNNER_SHA:
        raise RuntimeError('stages 171–175 runner drift')
    if digest(STAGE176_PACKET / 'run.py') != STAGE176_RUNNER_SHA:
        raise RuntimeError('stages 176–180 runner drift')
    if digest(STAGE181_PACKET / 'run.py') != STAGE181_RUNNER_SHA:
        raise RuntimeError('stages 181–185 runner drift')
    if digest(STAGE186_PACKET / 'run.py') != STAGE186_RUNNER_SHA:
        raise RuntimeError('stages 186–190 runner drift')
    if digest(STAGE191_PACKET / 'run.py') != STAGE191_RUNNER_SHA:
        raise RuntimeError('stages 191–195 runner drift')
    if digest(STAGE196_PACKET / 'run.py') != STAGE196_RUNNER_SHA:
        raise RuntimeError('stage 196 runner drift')
    if digest(STAGE197_PACKET / 'run.py') != STAGE197_RUNNER_SHA:
        raise RuntimeError('stage 197 retry runner drift')
    if digest(STAGE198_PACKET / 'run.py') != STAGE198_RUNNER_SHA:
        raise RuntimeError('stages 198–202 runner drift')
    if digest(STAGE203_PACKET / 'run.py') != STAGE203_RUNNER_SHA:
        raise RuntimeError('stages 203–207 runner drift')
    if digest(STAGE208_PACKET / 'run.py') != STAGE208_RUNNER_SHA:
        raise RuntimeError('stages 208–212 runner drift')
    if digest(STAGE213_PACKET / 'run.py') != STAGE213_RUNNER_SHA:
        raise RuntimeError('stages 213–217 runner drift')
    if digest(STAGE218_PACKET / 'run.py') != STAGE218_RUNNER_SHA:
        raise RuntimeError('stages 218–222 runner drift')
    if digest(STAGE223_PACKET / 'run.py') != STAGE223_RUNNER_SHA:
        raise RuntimeError('stage 223 runner drift')
    if digest(STAGE224_PACKET / 'run.py') != STAGE224_RUNNER_SHA:
        raise RuntimeError('stage 224 runner drift')
    if digest(STAGE225_PACKET / 'run.py') != STAGE225_RUNNER_SHA:
        raise RuntimeError('stages 225–239 runner drift')
    if digest(STAGE240_PACKET / 'run.py') != STAGE240_RUNNER_SHA:
        raise RuntimeError('stages 240–249 runner drift')
    if digest(STAGE250_PACKET / 'run.py') != STAGE250_RUNNER_SHA:
        raise RuntimeError('stage 250 runner drift')
    if digest(STAGE251_PACKET / 'run.py') != STAGE251_RUNNER_SHA:
        raise RuntimeError('stage 251 stopped runner drift')
    if digest(STAGE251_RETRY_PACKET / 'run.py') != STAGE251_RETRY_RUNNER_SHA:
        raise RuntimeError('stage 251 retry runner drift')
    if digest(STAGE252_PACKET / 'run.py') != STAGE252_RUNNER_SHA:
        raise RuntimeError('stages 252–262 runner drift')
    if digest(STAGE263_PACKET / 'run.py') != STAGE263_RUNNER_SHA:
        raise RuntimeError('stage 263 runner drift')
    if digest(STAGE264_PACKET / 'run.py') != STAGE264_RUNNER_SHA:
        raise RuntimeError('stages 264–265 runner drift')
    if digest(STAGE266_PACKET / 'run.py') != STAGE266_RUNNER_SHA:
        raise RuntimeError('stage 266 runner drift')
    if digest(STAGE267_PACKET / 'run.py') != STAGE267_RUNNER_SHA:
        raise RuntimeError('stage 267 runner drift')
    if digest(STAGE268_PACKET / 'run.py') != STAGE268_RUNNER_SHA:
        raise RuntimeError('stage 268 runner drift')
    if digest(STAGE269_PACKET / 'run.py') != STAGE269_RUNNER_SHA:
        raise RuntimeError('stage 269 runner drift')
    if digest(STAGE270_PACKET / 'run.py') != STAGE270_RUNNER_SHA:
        raise RuntimeError('stage 270 runner drift')
    if digest(STAGE271_PACKET / 'run.py') != STAGE271_RUNNER_SHA:
        raise RuntimeError('stage 271 runner drift')
    if digest(STAGE272_PACKET / 'run.py') != STAGE272_RUNNER_SHA:
        raise RuntimeError('stage 272 runner drift')
    if digest(STAGE273_PACKET / 'run.py') != STAGE273_RUNNER_SHA:
        raise RuntimeError('stage 273 runner drift')
    if digest(STAGE275_PACKET / 'run.py') != STAGE275_RUNNER_SHA:
        raise RuntimeError('stage 275 runner drift')
    if digest(STAGE276_FAILED_PACKET / 'run.py') != STAGE276_FAILED_RUNNER_SHA:
        raise RuntimeError('stage 276 failed runner drift')
    if digest(STAGE276_PACKET / 'run.py') != STAGE276_RUNNER_SHA:
        raise RuntimeError('stage 276 corrected runner drift')
    if digest(STAGE277_PACKET / 'run.py') != STAGE277_RUNNER_SHA:
        raise RuntimeError('stages 277–284 runner drift')
    if digest(STAGE285_PACKET / 'run.py') != STAGE285_RUNNER_SHA:
        raise RuntimeError('stage 285 retry runner drift')
    if digest(STAGE286_PACKET / 'run.py') != STAGE286_RUNNER_SHA:
        raise RuntimeError('stages 286–300 runner drift')
    if digest(STAGE301_FAILED_PACKET / 'run.py') != STAGE301_FAILED_RUNNER_SHA:
        raise RuntimeError('stage 301 failed runner drift')
    if digest(STAGE301_PACKET / 'run.py') != STAGE301_RUNNER_SHA:
        raise RuntimeError('stage 301 retry runner drift')
    if digest(STAGE306_FAILED_PACKET / 'run.py') != STAGE306_FAILED_RUNNER_SHA:
        raise RuntimeError('stage 306 failed runner drift')
    if digest(STAGE306_PACKET / 'run.py') != STAGE306_RUNNER_SHA:
        raise RuntimeError('stage 306 retry runner drift')
    if digest(STAGE307_FAILED_PACKET / 'run.py') != STAGE307_FAILED_RUNNER_SHA:
        raise RuntimeError('stage 307 failed runner drift')
    if digest(STAGE307_PACKET / 'run.py') != STAGE307_RUNNER_SHA:
        raise RuntimeError('stage 307 retry runner drift')
    if digest(STAGE310_FAILED_PACKET / 'run.py') != STAGE310_FAILED_RUNNER_SHA:
        raise RuntimeError('stage 310 failed runner drift')
    if digest(STAGE310_PACKET / 'run.py') != STAGE310_RUNNER_SHA:
        raise RuntimeError('stage 310 retry runner drift')
    if digest(STAGE311_FAILED_PACKET / 'run.py') != STAGE311_FAILED_RUNNER_SHA:
        raise RuntimeError('stage 311 failed runner drift')
    if digest(STAGE311_PACKET / 'run.py') != STAGE311_RUNNER_SHA:
        raise RuntimeError('stage 311 retry runner drift')
    if digest(STAGE312_FAILED_PACKET / 'run.py') != STAGE312_FAILED_RUNNER_SHA:
        raise RuntimeError('stage 312 failed runner drift')
    if digest(STAGE312_PACKET / 'run.py') != STAGE312_RUNNER_SHA:
        raise RuntimeError('stage 312 retry runner drift')
    if digest(STAGE314_FAILED_PACKET / 'run.py') != STAGE314_FAILED_RUNNER_SHA:
        raise RuntimeError('stage 314 failed runner drift')
    if digest(STAGE314_PACKET / 'run.py') != STAGE314_RUNNER_SHA:
        raise RuntimeError('stage 314 retry runner drift')
    if digest(STAGE316_FAILED_PACKET / 'run.py') != STAGE316_FAILED_RUNNER_SHA:
        raise RuntimeError('stage 316 failed runner drift')
    if digest(STAGE316_PACKET / 'run.py') != STAGE316_RUNNER_SHA:
        raise RuntimeError('stage 316 retry runner drift')
    if digest(STAGE317_FAILED_PACKET / 'run.py') != STAGE317_FAILED_RUNNER_SHA:
        raise RuntimeError('stage 317 failed runner drift')
    if digest(STAGE317_PACKET / 'run.py') != STAGE317_RUNNER_SHA:
        raise RuntimeError('stage 317 corrected runner drift')
    if digest(STAGE316_PACKET / 'verify_warning.py') != WARNING316_VERIFY_SHA or digest(STAGE316_PACKET / 'expected-warning.txt') != WARNING316_EXPECTED_SHA:
        raise RuntimeError('stage 316 warning verifier or baseline drift')
    if digest(STAGE314_PACKET / 'verify_warning.py') != WARNING314_VERIFY_SHA or digest(STAGE314_PACKET / 'expected-warning.txt') != WARNING314_EXPECTED_SHA:
        raise RuntimeError('stage 314 warning verifier or baseline drift')
    if digest(STAGE312_PACKET / 'verify_warning.py') != WARNING312_VERIFY_SHA or digest(STAGE312_PACKET / 'expected-warning.txt') != WARNING312_EXPECTED_SHA:
        raise RuntimeError('stage 312 warning verifier or baseline drift')
    if digest(STAGE311_PACKET / 'verify_warning.py') != WARNING311_VERIFY_SHA or digest(STAGE311_PACKET / 'expected-warning.txt') != WARNING311_EXPECTED_SHA:
        raise RuntimeError('stage 311 warning verifier or baseline drift')
    if digest(STAGE310_PACKET / 'verify_warning.py') != WARNING310_VERIFY_SHA or digest(STAGE310_PACKET / 'expected-warning.txt') != WARNING310_EXPECTED_SHA:
        raise RuntimeError('stage 310 warning verifier or baseline drift')
    if digest(STAGE307_PACKET / 'verify_warning.py') != WARNING307_VERIFY_SHA or digest(STAGE307_PACKET / 'expected-warning.txt') != WARNING307_EXPECTED_SHA:
        raise RuntimeError('stage 307 warning verifier or baseline drift')
    if digest(STAGE306_PACKET / 'verify_warning.py') != WARNING306_VERIFY_SHA or digest(STAGE306_PACKET / 'expected-warning.txt') != WARNING306_EXPECTED_SHA:
        raise RuntimeError('stage 306 warning verifier or baseline drift')
    if digest(STAGE301_PACKET / 'verify_warning.py') != WARNING301_VERIFY_SHA or digest(STAGE301_PACKET / 'expected-warning.txt') != WARNING301_EXPECTED_SHA:
        raise RuntimeError('stage 301 warning verifier or baseline drift')
    if digest(STAGE275_PACKET / 'verify_warning.py') != WARNING275_VERIFY_SHA or digest(STAGE275_PACKET / 'expected-warning.txt') != WARNING275_EXPECTED_SHA:
        raise RuntimeError('stage 275 warning verifier or baseline drift')
    if digest(STAGE272_PACKET / 'verify_warning.py') != WARNING272_VERIFY_SHA or digest(STAGE272_PACKET / 'expected-warning.txt') != WARNING272_EXPECTED_SHA:
        raise RuntimeError('stage 272 warning verifier or baseline drift')
    if digest(STAGE270_PACKET / 'verify_warning.py') != WARNING270_VERIFY_SHA or digest(STAGE270_PACKET / 'expected-warning.txt') != WARNING270_EXPECTED_SHA:
        raise RuntimeError('stage 270 warning verifier or baseline drift')
    if digest(STAGE268_PACKET / 'verify_warning.py') != WARNING268_VERIFY_SHA or digest(STAGE268_PACKET / 'expected-warning.txt') != WARNING268_EXPECTED_SHA:
        raise RuntimeError('stage 268 warning verifier or baseline drift')
    if digest(STAGE266_PACKET / 'verify_warning.py') != WARNING266_VERIFY_SHA or digest(STAGE266_PACKET / 'expected-warning.txt') != WARNING266_EXPECTED_SHA:
        raise RuntimeError('stage 266 warning verifier or baseline drift')
    if digest(STAGE263_PACKET / 'verify_warning.py') != WARNING263_VERIFY_SHA or digest(STAGE263_PACKET / 'expected-warning.txt') != WARNING263_EXPECTED_SHA:
        raise RuntimeError('stage 263 warning verifier or baseline drift')
    if digest(STAGE251_RETRY_PACKET / 'verify_warning.py') != WARNING251_VERIFY_SHA or digest(STAGE251_RETRY_PACKET / 'expected-warning.txt') != WARNING251_EXPECTED_SHA:
        raise RuntimeError('stage 251 warning verifier or baseline drift')
    if digest(STAGE250_PACKET / 'verify_warning.py') != WARNING250_VERIFY_SHA or digest(STAGE250_PACKET / 'expected-warning.txt') != WARNING250_EXPECTED_SHA:
        raise RuntimeError('stage 250 warning verifier or baseline drift')
    if digest(STAGE224_PACKET / 'verify_warning.py') != WARNING224_VERIFY_SHA or digest(STAGE224_PACKET / 'expected-warning.txt') != WARNING224_EXPECTED_SHA:
        raise RuntimeError('stage 224 warning verifier or baseline drift')
    if digest(STAGE79_PACKET / 'verify_warning.py') != WARNING_VERIFY_SHA or digest(STAGE79_PACKET / 'expected-warning.txt') != WARNING_EXPECTED_SHA:
        raise RuntimeError('warning verifier or baseline drift')
    if digest(STAGE81_PACKET / 'verify_warning.py') != WARNING81_VERIFY_SHA or digest(STAGE81_PACKET / 'expected-warning.txt') != WARNING81_EXPECTED_SHA:
        raise RuntimeError('stage 81 warning verifier or baseline drift')
    if digest(STAGE84_PACKET / 'verify_warning.py') != WARNING84_VERIFY_SHA or digest(STAGE84_PACKET / 'expected-warning.txt') != WARNING84_EXPECTED_SHA:
        raise RuntimeError('stage 84 warning verifier or baseline drift')
    if digest(STAGE197_PACKET / 'verify_warning.py') != WARNING197_VERIFY_SHA or digest(STAGE197_PACKET / 'expected-warning.txt') != WARNING197_EXPECTED_SHA:
        raise RuntimeError('stage 197 warning verifier or baseline drift')
    PROJECT.mkdir(exist_ok=True)
    lock = (PROJECT / 'build.lock').open('a+')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    check_pins()
    manifest = json.loads(MANIFEST.read_text())
    full = json.loads(FULL_SCAN.read_text())
    cone = json.loads(CONE.read_text())
    if (not full['complete'] or not full['overlay_unchanged'] or not full['omitted_unchanged'] or
        full['unresolved_direct_imports'] or cone['scan_sha256'] != EXPECT[FULL_SCAN]):
        raise RuntimeError('selected-object scan did not pass')
    order = cone['topological_candidate']
    if len(order) != 425 or len(set(order)) != 425:
        raise RuntimeError('unexpected candidate cone')
    check_sources(cone)
    verify_overlay(manifest)
    omitted_families = {m.replace('.', '/') + '.olean' for m in order}
    base = {rel: row for rel, row in manifest['overlay'].items() if rel not in omitted_families}
    if len(base) != len(manifest['overlay']) - 366:
        raise RuntimeError('unexpected removed selected object count')
    baseline = {'scope': 'selected project object rebuild preflight; package and dynamic ancestry remain open',
                'input_sha256': {str(p): EXPECT[p] for p in (MANIFEST, FULL_SCAN, OLD_CONE)},
                'lean_sha256': digest(LEAN), 'runner_sha256': FIRST_RUNNER_SHA,
                'retained_selected_objects': base,
                'removed_object_families': sorted(omitted_families), 'topological_order': order,
                'source_sha256': {m: cone['candidate_sources'][m]['source_sha256'] for m in order}}
    original_baseline = FIRST_PACKET / 'observations' / 'baseline.json'
    if digest(original_baseline) != 'f89d5466637be18ca5e95492df05e329a8ccc1be6d9fb150602fc975089b1aea':
        raise RuntimeError('original baseline drift')
    original = json.loads(original_baseline.read_text())
    if (original['retained_selected_objects'] != base or original['topological_order'] != order or
        original['source_sha256']['BusyBeaver.ZFC.L2Root254'] != '20b2ef7733a0d85c5248ee598b5386f42ad46319a003488fb63bfacb7f737e9f'):
        raise RuntimeError('re-pin changes baseline beyond the intended source')
    original_sources = dict(original['source_sha256'])
    original_sources['BusyBeaver.ZFC.L2Root254'] = 'fee84717177d6575f576ae3e09a3a034071f02422b7a5ef8d9d68e7822864d10'
    original_sources['ZFCinPA.NativeSchema'] = 'd6042135723adce366def247894e63cd3ad5d05d1dc57256718e6c82100f3210'
    original_sources['ZFCinPA.LSchema'] = 'c68dbfb6e9b152ab71654de3a2b2cf3559ebe1f8e616edabd12e24209ea568f2'
    if original_sources != baseline['source_sha256']:
        raise RuntimeError('other source pins changed')
    baseline['supersedes_baseline_sha256'] = digest(original_baseline)
    previous_baseline = STAGE64_PACKET / 'observations' / 'baseline-repinned.json'
    previous = json.loads(previous_baseline.read_text())
    old_baseline = dict(baseline)
    old_baseline['source_sha256'] = dict(baseline['source_sha256'])
    old_baseline['source_sha256']['ZFCinPA.NativeSchema'] = '266f7f619e3f01fc0a64c38036b14a5854c7264fef0cceb999a437fefab99982'
    old_baseline['source_sha256']['ZFCinPA.LSchema'] = 'f7edf5e44ae544506a97859e7ab8937f9d69ff6b89cc821350dfb1b6f1be09f5'
    if previous != old_baseline:
        raise RuntimeError('previous baseline differs beyond the intended source correction')
    previous276_path = STAGE276_PACKET / 'observations' / 'baseline-repinned.json'
    previous276 = json.loads(previous276_path.read_text())
    expected276 = dict(baseline)
    expected276['source_sha256'] = dict(baseline['source_sha256'])
    expected276['source_sha256']['ZFCinPA.LSchema'] = 'f7edf5e44ae544506a97859e7ab8937f9d69ff6b89cc821350dfb1b6f1be09f5'
    expected276['input_sha256'] = {str(p): EXPECT[p] for p in (MANIFEST, FULL_SCAN, OLD_CONE, PREV_CONE)}
    expected276['supersedes_stage64_baseline_sha256'] = digest(previous_baseline)
    if previous276 != expected276: raise RuntimeError('stage 276 baseline changed beyond intended source correction')
    new_baseline = dict(baseline)
    new_baseline['input_sha256'] = {str(p): h for p, h in EXPECT.items()}
    new_baseline['supersedes_stage64_baseline_sha256'] = digest(previous_baseline)
    new_baseline['supersedes_stage276_baseline_sha256'] = digest(previous276_path)
    baseline_text = json.dumps(new_baseline, indent=2, sort_keys=True) + '\n'
    baseline_path = STAGE317_PACKET / 'observations' / 'baseline-repinned.json'
    baseline_path.parent.mkdir(parents=True, exist_ok=True)
    if baseline_path.exists():
        if baseline_path.read_text() != baseline_text: raise RuntimeError('new baseline drift')
    else:
        raise RuntimeError('new baseline is missing')
    if not LIB.exists():
        LIB.mkdir()
        for rel, row in base.items():
            p = LIB / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.symlink_to(row['resolved'])
    # The rejected attempt's newly emitted object must never be imported.
    # Move only the exact recorded rejected bytes to a fresh quarantine path.
    rejected = LIB / 'BusyBeaver/ZFC/L2Root254.olean'
    quarantine = PROJECT / 'quarantine/stage-0064-rejected.olean'
    expected_rejected = '16e2ea23478f0720e51544e6ff25c51f061b2513d2f0871ec079b00a4eb63202'
    if not quarantine.is_file() or digest(quarantine) != expected_rejected:
        raise RuntimeError('missing rejected-object quarantine')
    rejected79 = LIB / 'BusyBeaver/ZFC/KLowerRaw.olean'
    quarantine79 = PROJECT / 'quarantine/stage-0079-rejected.olean'
    rejected79_sha = 'ca70aa5d67e2fdc4efef374b6071d4e5801046b2bc1cb863ebb43e5440dcca1c'
    failed_obs = STAGE77_PACKET / 'observations/batch-016/stage-0079'
    if digest(failed_obs / 'terminal.json') != '3caf2da10031812c42037dc9c03adfe253c7f1c8d2c1ee19a8a099cd4988d94a':
        raise RuntimeError('rejected stage 79 receipt drift')
    failed = json.loads((failed_obs / 'terminal.json').read_text())
    if failed['guards'] != {p: record(p) for p in failed['guards']}:
        raise RuntimeError('rejected stage 79 dependency drift')
    own79 = receipt_dir(79) / 'terminal.json'
    if not own79.exists():
        if rejected79.exists():
            if rejected79.is_symlink() or digest(rejected79) != rejected79_sha or quarantine79.exists():
                raise RuntimeError('unexpected rejected stage 79 object state')
            quarantine79.parent.mkdir(parents=True, exist_ok=True)
            rejected79.rename(quarantine79)
        if not quarantine79.is_file() or digest(quarantine79) != rejected79_sha:
            raise RuntimeError('missing stage 79 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected79), 'quarantine_path': str(quarantine79),
                             'sha256': rejected79_sha, 'reason': 'rejected unbaselined linter warning'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage79.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine79.is_file() or digest(quarantine79) != rejected79_sha:
        raise RuntimeError('stage 79 rejected-object quarantine drift')
    rejected81 = LIB / 'BusyBeaver/ZFC/KLowerTag.olean'
    quarantine81 = PROJECT / 'quarantine/stage-0081-rejected.olean'
    rejected81_sha = '48cf2bbd2d623aa105568704dc61b0ec1c073531e85d133a5df46e603d796829'
    failed81_obs = STAGE80_PACKET / 'observations/batch-017/stage-0081'
    if digest(failed81_obs / 'terminal.json') != '3867e52e153de570e8042e78d5b3ec4ce9a982bbb5fe16a04f81ecdccbb5030f':
        raise RuntimeError('rejected stage 81 receipt drift')
    failed81 = json.loads((failed81_obs / 'terminal.json').read_text())
    if failed81['guards'] != {p: record(p) for p in failed81['guards']}:
        raise RuntimeError('rejected stage 81 dependency drift')
    own81 = receipt_dir(81) / 'terminal.json'
    if not own81.exists():
        if rejected81.exists():
            if rejected81.is_symlink() or digest(rejected81) != rejected81_sha or quarantine81.exists():
                raise RuntimeError('unexpected rejected stage 81 object state')
            quarantine81.parent.mkdir(parents=True, exist_ok=True)
            rejected81.rename(quarantine81)
        if not quarantine81.is_file() or digest(quarantine81) != rejected81_sha:
            raise RuntimeError('missing stage 81 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected81), 'quarantine_path': str(quarantine81),
                             'sha256': rejected81_sha, 'reason': 'rejected unbaselined linter warning'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage81.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine81.is_file() or digest(quarantine81) != rejected81_sha:
        raise RuntimeError('stage 81 rejected-object quarantine drift')
    rejected84 = LIB / 'BusyBeaver/ZFC/KQ1Model.olean'
    quarantine84 = PROJECT / 'quarantine/stage-0084-rejected.olean'
    rejected84_sha = 'e52477f9a7fc2b6aae82a387281beb829246270cf7b3fbf6d3bdadb052077729'
    failed84_obs = STAGE82_PACKET / 'observations/batch-017/stage-0084'
    if digest(failed84_obs / 'terminal.json') != '371aac007260fc9b65875c5e57c9ac279f63ca3dc509227dcbbc9ed426f78539':
        raise RuntimeError('rejected stage 84 receipt drift')
    failed84 = json.loads((failed84_obs / 'terminal.json').read_text())
    if failed84['guards'] != {p: record(p) for p in failed84['guards']}:
        raise RuntimeError('rejected stage 84 dependency drift')
    own84 = receipt_dir(84) / 'terminal.json'
    if not own84.exists():
        if rejected84.exists():
            if rejected84.is_symlink() or digest(rejected84) != rejected84_sha or quarantine84.exists():
                raise RuntimeError('unexpected rejected stage 84 object state')
            quarantine84.parent.mkdir(parents=True, exist_ok=True)
            rejected84.rename(quarantine84)
        if not quarantine84.is_file() or digest(quarantine84) != rejected84_sha:
            raise RuntimeError('missing stage 84 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected84), 'quarantine_path': str(quarantine84),
                             'sha256': rejected84_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage84.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine84.is_file() or digest(quarantine84) != rejected84_sha:
        raise RuntimeError('stage 84 rejected-object quarantine drift')
    rejected197 = LIB / 'BusyBeaver/ZFC/KQ1Basic.olean'
    quarantine197 = PROJECT / 'quarantine/stage-0197-rejected.olean'
    rejected197_sha = 'fd61d67e686d620b818bb53cca8d9e2eb2fa49c6cd70731bfdffea92c078c171'
    failed197_obs = STAGE196_PACKET / 'observations/batch-040/stage-0197'
    if digest(failed197_obs / 'terminal.json') != 'f45cbcae8451ef8800ffdd028b2e962f6fc6a81ebf68b3b742e5f4d4643f4662':
        raise RuntimeError('rejected stage 197 receipt drift')
    failed197 = json.loads((failed197_obs / 'terminal.json').read_text())
    if failed197['guards'] != {p: record(p) for p in failed197['guards']}:
        raise RuntimeError('rejected stage 197 dependency drift')
    own197 = receipt_dir(197) / 'terminal.json'
    if not own197.exists():
        if rejected197.exists():
            if rejected197.is_symlink() or digest(rejected197) != rejected197_sha or quarantine197.exists():
                raise RuntimeError('unexpected rejected stage 197 object state')
            quarantine197.parent.mkdir(parents=True, exist_ok=True)
            rejected197.rename(quarantine197)
        if not quarantine197.is_file() or digest(quarantine197) != rejected197_sha:
            raise RuntimeError('missing stage 197 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected197), 'quarantine_path': str(quarantine197),
                             'sha256': rejected197_sha, 'reason': 'rejected unbaselined linter warning'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage197.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine197.is_file() or digest(quarantine197) != rejected197_sha:
        raise RuntimeError('stage 197 rejected-object quarantine drift')
    rejected224 = LIB / 'BusyBeaver/ZFC/KLowerQHyp.olean'
    quarantine224 = PROJECT / 'quarantine/stage-0224-rejected.olean'
    rejected224_sha = 'e4012864d6877d2c0591c859c51d87fedf8f44578e6b3552cc9d063531b82671'
    failed224_obs = STAGE223_PACKET / 'observations/batch-045/stage-0224'
    if digest(failed224_obs / 'terminal.json') != '20ac6f6fa43c17f63f8b2d7e9f070a47ecf6ff2c78bd8df8e26f18add18bb39f':
        raise RuntimeError('rejected stage 224 receipt drift')
    failed224 = json.loads((failed224_obs / 'terminal.json').read_text())
    if failed224['guards'] != {p: record(p) for p in failed224['guards']}:
        raise RuntimeError('rejected stage 224 dependency drift')
    own224 = receipt_dir(224) / 'terminal.json'
    if not own224.exists():
        if rejected224.exists():
            if rejected224.is_symlink() or digest(rejected224) != rejected224_sha or quarantine224.exists():
                raise RuntimeError('unexpected rejected stage 224 object state')
            quarantine224.parent.mkdir(parents=True, exist_ok=True)
            rejected224.rename(quarantine224)
        if not quarantine224.is_file() or digest(quarantine224) != rejected224_sha:
            raise RuntimeError('missing stage 224 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected224), 'quarantine_path': str(quarantine224),
                             'sha256': rejected224_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage224.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine224.is_file() or digest(quarantine224) != rejected224_sha:
        raise RuntimeError('stage 224 rejected-object quarantine drift')
    rejected250 = LIB / 'ZFCinPA/ModelCodedDecoderRho4_254.olean'
    quarantine250 = PROJECT / 'quarantine/stage-0250-rejected.olean'
    rejected250_sha = '417c68884d4f44ded4c2a8beccc05f85ee10739a49057c2bf6427acc82d918d5'
    failed250_obs = STAGE240_PACKET / 'observations/batch-050/stage-0250'
    if digest(failed250_obs / 'terminal.json') != '3ccf6bbecce598c1282d83306bd43d2a78ba89e8bc59ef55459c90602784a251':
        raise RuntimeError('rejected stage 250 receipt drift')
    failed250 = json.loads((failed250_obs / 'terminal.json').read_text())
    if failed250['guards'] != {p: record(p) for p in failed250['guards']}:
        raise RuntimeError('rejected stage 250 dependency drift')
    own250 = receipt_dir(250) / 'terminal.json'
    if not own250.exists():
        if rejected250.exists():
            if rejected250.is_symlink() or digest(rejected250) != rejected250_sha or quarantine250.exists():
                raise RuntimeError('unexpected rejected stage 250 object state')
            quarantine250.parent.mkdir(parents=True, exist_ok=True)
            rejected250.rename(quarantine250)
        if not quarantine250.is_file() or digest(quarantine250) != rejected250_sha:
            raise RuntimeError('missing stage 250 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected250), 'quarantine_path': str(quarantine250),
                             'sha256': rejected250_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage250.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine250.is_file() or digest(quarantine250) != rejected250_sha:
        raise RuntimeError('stage 250 rejected-object quarantine drift')
    rejected251 = LIB / 'ZFCinPA/ModelCodedDecoderRho6_254.olean'
    quarantine251 = PROJECT / 'quarantine/stage-0251-rejected.olean'
    rejected251_sha = 'b05e062b607425f9a3c651ac90d83b7be037384014a0b1553703b8dc3d6f47b2'
    failed251_obs = STAGE251_PACKET / 'observations/batch-051/stage-0251'
    if digest(failed251_obs / 'terminal.json') != 'fcf79b39082baf508ec0c3153808335cc109bfbed2961c45f6ff326bcdf6d932':
        raise RuntimeError('rejected stage 251 receipt drift')
    failed251 = json.loads((failed251_obs / 'terminal.json').read_text())
    if failed251['guards'] != {p: record(p) for p in failed251['guards']}:
        raise RuntimeError('rejected stage 251 dependency drift')
    own251 = receipt_dir(251) / 'terminal.json'
    if not own251.exists():
        if rejected251.exists():
            if rejected251.is_symlink() or digest(rejected251) != rejected251_sha or quarantine251.exists():
                raise RuntimeError('unexpected rejected stage 251 object state')
            quarantine251.parent.mkdir(parents=True, exist_ok=True)
            rejected251.rename(quarantine251)
        if not quarantine251.is_file() or digest(quarantine251) != rejected251_sha:
            raise RuntimeError('missing stage 251 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected251), 'quarantine_path': str(quarantine251),
                             'sha256': rejected251_sha, 'reason': 'rejected unbaselined linter warning'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage251.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine251.is_file() or digest(quarantine251) != rejected251_sha:
        raise RuntimeError('stage 251 rejected-object quarantine drift')
    rejected263 = LIB / 'ZFCinPA/ConstructibleInterpretation.olean'
    quarantine263 = PROJECT / 'quarantine/stage-0263-rejected.olean'
    rejected263_sha = '7b24b2a930ba755a9d9e9ff2c98200042cb409e801c64eeb07903ad7ae83864d'
    failed263_obs = STAGE252_PACKET / 'observations/batch-053/stage-0263'
    if digest(failed263_obs / 'terminal.json') != '8fc641db04dc50035455ab14da35bbaeb800cf2486228f8ba7505cb056356eb6':
        raise RuntimeError('rejected stage 263 receipt drift')
    failed263 = json.loads((failed263_obs / 'terminal.json').read_text())
    if failed263['guards'] != {p: record(p) for p in failed263['guards']}:
        raise RuntimeError('rejected stage 263 dependency drift')
    own263 = receipt_dir(263) / 'terminal.json'
    if not own263.exists():
        if rejected263.exists():
            if rejected263.is_symlink() or digest(rejected263) != rejected263_sha or quarantine263.exists():
                raise RuntimeError('unexpected rejected stage 263 object state')
            quarantine263.parent.mkdir(parents=True, exist_ok=True)
            rejected263.rename(quarantine263)
        if not quarantine263.is_file() or digest(quarantine263) != rejected263_sha:
            raise RuntimeError('missing stage 263 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected263), 'quarantine_path': str(quarantine263),
                             'sha256': rejected263_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage263.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine263.is_file() or digest(quarantine263) != rejected263_sha:
        raise RuntimeError('stage 263 rejected-object quarantine drift')
    rejected266 = LIB / 'ZFCinPA/ModelCodedDecoderCollection254.olean'
    quarantine266 = PROJECT / 'quarantine/stage-0266-rejected.olean'
    rejected266_sha = '1cae5502955e62c4f5838b1f53e043cc73b2ab8c196b8608fe3181c9b86b5975'
    failed266_obs = STAGE264_PACKET / 'observations/batch-054/stage-0266'
    if digest(failed266_obs / 'terminal.json') != '20f275931f23891fd6b67332441ecaa956ec4d6eeedee627f8a3b066911616b3':
        raise RuntimeError('rejected stage 266 receipt drift')
    failed266 = json.loads((failed266_obs / 'terminal.json').read_text())
    if failed266['guards'] != {p: record(p) for p in failed266['guards']}:
        raise RuntimeError('rejected stage 266 dependency drift')
    own266 = receipt_dir(266) / 'terminal.json'
    if not own266.exists():
        if rejected266.exists():
            if rejected266.is_symlink() or digest(rejected266) != rejected266_sha or quarantine266.exists():
                raise RuntimeError('unexpected rejected stage 266 object state')
            quarantine266.parent.mkdir(parents=True, exist_ok=True)
            rejected266.rename(quarantine266)
        if not quarantine266.is_file() or digest(quarantine266) != rejected266_sha:
            raise RuntimeError('missing stage 266 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected266), 'quarantine_path': str(quarantine266),
                             'sha256': rejected266_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage266.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine266.is_file() or digest(quarantine266) != rejected266_sha:
        raise RuntimeError('stage 266 rejected-object quarantine drift')
    rejected268 = LIB / 'ZFCinPA/ModelCodedDecoderAccepted254.olean'
    quarantine268 = PROJECT / 'quarantine/stage-0268-rejected.olean'
    rejected268_sha = 'c77acd4034ea48878c4acde8a6282e346dfaf063875d8b27b476735f501e89b2'
    failed268_obs = STAGE267_PACKET / 'observations/batch-054/stage-0268'
    if digest(failed268_obs / 'terminal.json') != '2634f8b59928fe3b643d7708fb046f32920e65467e2e3bc4e16e754f00d5fc0a':
        raise RuntimeError('rejected stage 268 receipt drift')
    failed268 = json.loads((failed268_obs / 'terminal.json').read_text())
    if failed268['guards'] != {p: record(p) for p in failed268['guards']}:
        raise RuntimeError('rejected stage 268 dependency drift')
    own268 = receipt_dir(268) / 'terminal.json'
    if not own268.exists():
        if rejected268.exists():
            if rejected268.is_symlink() or digest(rejected268) != rejected268_sha or quarantine268.exists():
                raise RuntimeError('unexpected rejected stage 268 object state')
            quarantine268.parent.mkdir(parents=True, exist_ok=True)
            rejected268.rename(quarantine268)
        if not quarantine268.is_file() or digest(quarantine268) != rejected268_sha:
            raise RuntimeError('missing stage 268 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected268), 'quarantine_path': str(quarantine268),
                             'sha256': rejected268_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage268.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine268.is_file() or digest(quarantine268) != rejected268_sha:
        raise RuntimeError('stage 268 rejected-object quarantine drift')
    rejected270 = LIB / 'ZFCinPA/NativeTheory.olean'
    quarantine270 = PROJECT / 'quarantine/stage-0270-rejected.olean'
    rejected270_sha = 'f72e7e6f13676cc4675e402cd479124cfe70a222cabc1d041cf6b38be79242bb'
    failed270_obs = STAGE269_PACKET / 'observations/batch-054/stage-0270'
    if digest(failed270_obs / 'terminal.json') != '9cc4d4e0d0ceeb96202e0d082123d9108fe2013d24b9570eb07c7d57a3b05865':
        raise RuntimeError('rejected stage 270 receipt drift')
    failed270 = json.loads((failed270_obs / 'terminal.json').read_text())
    if failed270['guards'] != {p: record(p) for p in failed270['guards']}:
        raise RuntimeError('rejected stage 270 dependency drift')
    own270 = receipt_dir(270) / 'terminal.json'
    if not own270.exists():
        if rejected270.exists():
            if rejected270.is_symlink() or digest(rejected270) != rejected270_sha or quarantine270.exists():
                raise RuntimeError('unexpected rejected stage 270 object state')
            quarantine270.parent.mkdir(parents=True, exist_ok=True)
            rejected270.rename(quarantine270)
        if not quarantine270.is_file() or digest(quarantine270) != rejected270_sha:
            raise RuntimeError('missing stage 270 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected270), 'quarantine_path': str(quarantine270),
                             'sha256': rejected270_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage270.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine270.is_file() or digest(quarantine270) != rejected270_sha:
        raise RuntimeError('stage 270 rejected-object quarantine drift')
    rejected272 = LIB / 'ZFCinPA/NativeInterp.olean'
    quarantine272 = PROJECT / 'quarantine/stage-0272-rejected.olean'
    rejected272_sha = '1217722f6af7a78773dc27059348be28a0e25d31aee7327a15e3c218011ca909'
    failed272_obs = STAGE271_PACKET / 'observations/batch-055/stage-0272'
    if digest(failed272_obs / 'terminal.json') != 'aec2118148671ea1688aefd405ca638ba7566d39b4d4b58f742d634f184e3746':
        raise RuntimeError('rejected stage 272 receipt drift')
    failed272 = json.loads((failed272_obs / 'terminal.json').read_text())
    if failed272['guards'] != {p: record(p) for p in failed272['guards']}:
        raise RuntimeError('rejected stage 272 dependency drift')
    own272 = receipt_dir(272) / 'terminal.json'
    if not own272.exists():
        if rejected272.exists():
            if rejected272.is_symlink() or digest(rejected272) != rejected272_sha or quarantine272.exists():
                raise RuntimeError('unexpected rejected stage 272 object state')
            quarantine272.parent.mkdir(parents=True, exist_ok=True)
            rejected272.rename(quarantine272)
        if not quarantine272.is_file() or digest(quarantine272) != rejected272_sha:
            raise RuntimeError('missing stage 272 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected272), 'quarantine_path': str(quarantine272),
                             'sha256': rejected272_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage272.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine272.is_file() or digest(quarantine272) != rejected272_sha:
        raise RuntimeError('stage 272 rejected-object quarantine drift')
    rejected275 = LIB / 'ZFCinPA/NativeSchemaSem.olean'
    quarantine275 = PROJECT / 'quarantine/stage-0275-rejected.olean'
    rejected275_sha = '3a096eb8f79bd3983c0cae8397705572058b2c2bfe70068db7e4da94e59c360a'
    failed275_obs = STAGE273_PACKET / 'observations/batch-055/stage-0275'
    if digest(failed275_obs / 'terminal.json') != '5b43a50a330db7820e12345c6dcbf5e511406f752a37a1c7663fb6d43a161293':
        raise RuntimeError('rejected stage 275 receipt drift')
    failed275 = json.loads((failed275_obs / 'terminal.json').read_text())
    if failed275['guards'] != {p: record(p) for p in failed275['guards']}:
        raise RuntimeError('rejected stage 275 dependency drift')
    own275 = receipt_dir(275) / 'terminal.json'
    if not own275.exists():
        if rejected275.exists():
            if rejected275.is_symlink() or digest(rejected275) != rejected275_sha or quarantine275.exists():
                raise RuntimeError('unexpected rejected stage 275 object state')
            quarantine275.parent.mkdir(parents=True, exist_ok=True)
            rejected275.rename(quarantine275)
        if not quarantine275.is_file() or digest(quarantine275) != rejected275_sha:
            raise RuntimeError('missing stage 275 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected275), 'quarantine_path': str(quarantine275),
                             'sha256': rejected275_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage275.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine275.is_file() or digest(quarantine275) != rejected275_sha:
        raise RuntimeError('stage 275 rejected-object quarantine drift')
    failed276_obs = STAGE276_FAILED_PACKET / 'observations/batch-056/stage-0276'
    if digest(failed276_obs / 'terminal.json') != '763980f5977e32502f7c14ab67d05ee09d26232d499652496e33a1c342a955a8' or digest(failed276_obs / 'compile.log') != 'fd6622abe8021e5e334d9e8033af6737724e858dccf7a719d7f3e1f2bf2a8abb':
        raise RuntimeError('failed stage 276 receipt or log drift')
    failed276 = json.loads((failed276_obs / 'terminal.json').read_text())
    if failed276['exit_code'] != 1 or failed276['object_sha256'] is not None or failed276['guards'] != {p: record(p) for p in failed276['guards']}:
        raise RuntimeError('failed stage 276 outcome or dependencies drift')
    failed285_obs = STAGE277_PACKET / 'observations/batch-057/stage-0285'
    if digest(failed285_obs / 'terminal.json') != '5005f50cf5106944e2cc8bd769678f1055b76f84dc013d8f5a6e65d53ae63434' or digest(failed285_obs / 'compile.log') != '9f3a47adba61f209e2aa1459ac0f396159071ed7e4a92a8706981058c60557eb':
        raise RuntimeError('failed stage 285 receipt or log drift')
    failed285 = json.loads((failed285_obs / 'terminal.json').read_text())
    if failed285['exit_code'] != 1 or failed285['object_sha256'] is not None or failed285['guards'] != {p: record(p) for p in failed285['guards']}:
        raise RuntimeError('failed stage 285 outcome or dependencies drift')
    rejected301 = LIB / 'ZFCinPA/LDriverBase.olean'
    quarantine301 = PROJECT / 'quarantine/stage-0301-rejected.olean'
    rejected301_sha = '0bba9aba3ebbd6a5847f62c7d6cbf54cbf759c611c437f6e3bbfd558956b52eb'
    failed301_obs = STAGE301_FAILED_PACKET / 'observations/batch-061/stage-0301'
    if digest(failed301_obs / 'terminal.json') != 'bb6d82d79621db11f7ca3161a06f472c7502051e46ddf0d6b74b1269f01d72c2':
        raise RuntimeError('rejected stage 301 receipt drift')
    failed301 = json.loads((failed301_obs / 'terminal.json').read_text())
    if failed301['guards'] != {p: record(p) for p in failed301['guards']}:
        raise RuntimeError('rejected stage 301 dependency drift')
    own301 = receipt_dir(301) / 'terminal.json'
    if not own301.exists():
        if rejected301.exists():
            if rejected301.is_symlink() or digest(rejected301) != rejected301_sha or quarantine301.exists():
                raise RuntimeError('unexpected rejected stage 301 object state')
            quarantine301.parent.mkdir(parents=True, exist_ok=True)
            rejected301.rename(quarantine301)
        if not quarantine301.is_file() or digest(quarantine301) != rejected301_sha:
            raise RuntimeError('missing stage 301 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected301), 'quarantine_path': str(quarantine301),
                             'sha256': rejected301_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage301.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine301.is_file() or digest(quarantine301) != rejected301_sha:
        raise RuntimeError('stage 301 rejected-object quarantine drift')
    rejected306 = LIB / 'ZFCinPA/LFvBound.olean'
    quarantine306 = PROJECT / 'quarantine/stage-0306-rejected.olean'
    rejected306_sha = '021f78a695755002890c3f881601fc9197e50147cdc73776738f675d7fafc964'
    failed306_obs = STAGE306_FAILED_PACKET / 'observations/batch-062/stage-0306'
    if digest(failed306_obs / 'terminal.json') != 'ba1bb274d87934d5ba9cbf1eddb1776faaf7a3e22169b39aede156e3d8b3d3fb':
        raise RuntimeError('rejected stage 306 receipt drift')
    failed306 = json.loads((failed306_obs / 'terminal.json').read_text())
    if failed306['guards'] != {p: record(p) for p in failed306['guards']}:
        raise RuntimeError('rejected stage 306 dependency drift')
    own306 = receipt_dir(306) / 'terminal.json'
    if not own306.exists():
        if rejected306.exists():
            if rejected306.is_symlink() or digest(rejected306) != rejected306_sha or quarantine306.exists():
                raise RuntimeError('unexpected rejected stage 306 object state')
            quarantine306.parent.mkdir(parents=True, exist_ok=True)
            rejected306.rename(quarantine306)
        if not quarantine306.is_file() or digest(quarantine306) != rejected306_sha:
            raise RuntimeError('missing stage 306 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected306), 'quarantine_path': str(quarantine306),
                             'sha256': rejected306_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage306.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine306.is_file() or digest(quarantine306) != rejected306_sha:
        raise RuntimeError('stage 306 rejected-object quarantine drift')
    rejected307 = LIB / 'ZFCinPA/LMatch.olean'
    quarantine307 = PROJECT / 'quarantine/stage-0307-rejected.olean'
    rejected307_sha = 'bdba0367fea01e1c0532bea2d1a0486f763ff150aec86315ac4c8f28ab98a2c6'
    failed307_obs = STAGE307_FAILED_PACKET / 'observations/batch-062/stage-0307'
    if digest(failed307_obs / 'terminal.json') != '3b320db1ad21de198e762299b5c25fc94998e3c558db0d7a38e25eb1f3d7ec30':
        raise RuntimeError('rejected stage 307 receipt drift')
    failed307 = json.loads((failed307_obs / 'terminal.json').read_text())
    if failed307['guards'] != {p: record(p) for p in failed307['guards']}:
        raise RuntimeError('rejected stage 307 dependency drift')
    own307 = receipt_dir(307) / 'terminal.json'
    if not own307.exists():
        if rejected307.exists():
            if rejected307.is_symlink() or digest(rejected307) != rejected307_sha or quarantine307.exists():
                raise RuntimeError('unexpected rejected stage 307 object state')
            quarantine307.parent.mkdir(parents=True, exist_ok=True)
            rejected307.rename(quarantine307)
        if not quarantine307.is_file() or digest(quarantine307) != rejected307_sha:
            raise RuntimeError('missing stage 307 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected307), 'quarantine_path': str(quarantine307),
                             'sha256': rejected307_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage307.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine307.is_file() or digest(quarantine307) != rejected307_sha:
        raise RuntimeError('stage 307 rejected-object quarantine drift')
    rejected310 = LIB / 'ZFCinPA/LGlue1.olean'
    quarantine310 = PROJECT / 'quarantine/stage-0310-rejected.olean'
    rejected310_sha = '7a8d49aa7939dc3c3bbdb282c7bd1c858841b48a7b94268657b958559636df2e'
    failed310_obs = STAGE310_FAILED_PACKET / 'observations/batch-062/stage-0310'
    if digest(failed310_obs / 'terminal.json') != 'd5e422c7a161e8f1733f7a40bf21ff5283b59bdab3e2817a762b0fff48949048':
        raise RuntimeError('rejected stage 310 receipt drift')
    failed310 = json.loads((failed310_obs / 'terminal.json').read_text())
    if failed310['guards'] != {p: record(p) for p in failed310['guards']}:
        raise RuntimeError('rejected stage 310 dependency drift')
    own310 = receipt_dir(310) / 'terminal.json'
    if not own310.exists():
        if rejected310.exists():
            if rejected310.is_symlink() or digest(rejected310) != rejected310_sha or quarantine310.exists():
                raise RuntimeError('unexpected rejected stage 310 object state')
            quarantine310.parent.mkdir(parents=True, exist_ok=True)
            rejected310.rename(quarantine310)
        if not quarantine310.is_file() or digest(quarantine310) != rejected310_sha:
            raise RuntimeError('missing stage 310 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected310), 'quarantine_path': str(quarantine310),
                             'sha256': rejected310_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage310.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine310.is_file() or digest(quarantine310) != rejected310_sha:
        raise RuntimeError('stage 310 rejected-object quarantine drift')
    rejected311 = LIB / 'ZFCinPA/LGlue2.olean'
    quarantine311 = PROJECT / 'quarantine/stage-0311-rejected.olean'
    rejected311_sha = '2c3e11e27c2456bbe716313fda6b0d26b5e24450b10f34553c0accbbe75b8d6b'
    failed311_obs = STAGE311_FAILED_PACKET / 'observations/batch-063/stage-0311'
    if digest(failed311_obs / 'terminal.json') != '9bec5d1be1488851230a7b5146eb1153054109559215f0cd92748db5a0dbb733':
        raise RuntimeError('rejected stage 311 receipt drift')
    failed311 = json.loads((failed311_obs / 'terminal.json').read_text())
    if failed311['guards'] != {p: record(p) for p in failed311['guards']}:
        raise RuntimeError('rejected stage 311 dependency drift')
    own311 = receipt_dir(311) / 'terminal.json'
    if not own311.exists():
        if rejected311.exists():
            if rejected311.is_symlink() or digest(rejected311) != rejected311_sha or quarantine311.exists():
                raise RuntimeError('unexpected rejected stage 311 object state')
            quarantine311.parent.mkdir(parents=True, exist_ok=True)
            rejected311.rename(quarantine311)
        if not quarantine311.is_file() or digest(quarantine311) != rejected311_sha:
            raise RuntimeError('missing stage 311 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected311), 'quarantine_path': str(quarantine311),
                             'sha256': rejected311_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage311.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine311.is_file() or digest(quarantine311) != rejected311_sha:
        raise RuntimeError('stage 311 rejected-object quarantine drift')
    rejected312 = LIB / 'ZFCinPA/LGlue3.olean'
    quarantine312 = PROJECT / 'quarantine/stage-0312-rejected.olean'
    rejected312_sha = '415705e33108c5c44b9bff0c431c8ec6fccee281b701d04f00e5cf9412adf417'
    failed312_obs = STAGE312_FAILED_PACKET / 'observations/batch-063/stage-0312'
    if digest(failed312_obs / 'terminal.json') != '668a42c577a27d1daca23ffd234b1e83ac340be6179ca1ab505260ed7546bd2f':
        raise RuntimeError('rejected stage 312 receipt drift')
    failed312 = json.loads((failed312_obs / 'terminal.json').read_text())
    if failed312['guards'] != {p: record(p) for p in failed312['guards']}:
        raise RuntimeError('rejected stage 312 dependency drift')
    own312 = receipt_dir(312) / 'terminal.json'
    if not own312.exists():
        if rejected312.exists():
            if rejected312.is_symlink() or digest(rejected312) != rejected312_sha or quarantine312.exists():
                raise RuntimeError('unexpected rejected stage 312 object state')
            quarantine312.parent.mkdir(parents=True, exist_ok=True)
            rejected312.rename(quarantine312)
        if not quarantine312.is_file() or digest(quarantine312) != rejected312_sha:
            raise RuntimeError('missing stage 312 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected312), 'quarantine_path': str(quarantine312),
                             'sha256': rejected312_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage312.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine312.is_file() or digest(quarantine312) != rejected312_sha:
        raise RuntimeError('stage 312 rejected-object quarantine drift')
    rejected314 = LIB / 'ZFCinPA/LPeel.olean'
    quarantine314 = PROJECT / 'quarantine/stage-0314-rejected.olean'
    rejected314_sha = '4bc3f4677aaf7b8f9110b491bbac6f0df5808a59d8eab57b40235145903d97d9'
    failed314_obs = STAGE314_FAILED_PACKET / 'observations/batch-063/stage-0314'
    if digest(failed314_obs / 'terminal.json') != '2a33a80b87af5cae6d6d312667e5ad11b9dc7d6a897fde0c955de5758a1e5723':
        raise RuntimeError('rejected stage 314 receipt drift')
    failed314 = json.loads((failed314_obs / 'terminal.json').read_text())
    if failed314['guards'] != {p: record(p) for p in failed314['guards']}:
        raise RuntimeError('rejected stage 314 dependency drift')
    own314 = receipt_dir(314) / 'terminal.json'
    if not own314.exists():
        if rejected314.exists():
            if rejected314.is_symlink() or digest(rejected314) != rejected314_sha or quarantine314.exists():
                raise RuntimeError('unexpected rejected stage 314 object state')
            quarantine314.parent.mkdir(parents=True, exist_ok=True)
            rejected314.rename(quarantine314)
        if not quarantine314.is_file() or digest(quarantine314) != rejected314_sha:
            raise RuntimeError('missing stage 314 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected314), 'quarantine_path': str(quarantine314),
                             'sha256': rejected314_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage314.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine314.is_file() or digest(quarantine314) != rejected314_sha:
        raise RuntimeError('stage 314 rejected-object quarantine drift')
    rejected316 = LIB / 'ZFCinPA/LReplBase.olean'
    quarantine316 = PROJECT / 'quarantine/stage-0316-rejected.olean'
    rejected316_sha = '46cf01d55ba0724905e6b3eeb075a4ee72f34679920617fc48afbdb112a3e880'
    failed316_obs = STAGE316_FAILED_PACKET / 'observations/batch-064/stage-0316'
    if digest(failed316_obs / 'terminal.json') != '1a66a6d4cf78ee23d4964f55613fe73844977218c3fe39e8d2a78c1e46b61e19':
        raise RuntimeError('rejected stage 316 receipt drift')
    failed316 = json.loads((failed316_obs / 'terminal.json').read_text())
    if failed316['guards'] != {p: record(p) for p in failed316['guards']}:
        raise RuntimeError('rejected stage 316 dependency drift')
    own316 = receipt_dir(316) / 'terminal.json'
    if not own316.exists():
        if rejected316.exists():
            if rejected316.is_symlink() or digest(rejected316) != rejected316_sha or quarantine316.exists():
                raise RuntimeError('unexpected rejected stage 316 object state')
            quarantine316.parent.mkdir(parents=True, exist_ok=True)
            rejected316.rename(quarantine316)
        if not quarantine316.is_file() or digest(quarantine316) != rejected316_sha:
            raise RuntimeError('missing stage 316 rejected-object quarantine')
        quarantine_record = {'original_path': str(rejected316), 'quarantine_path': str(quarantine316),
                             'sha256': rejected316_sha, 'reason': 'rejected unbaselined linter warnings'}
        (HERE / 'observations').mkdir(parents=True, exist_ok=True)
        (HERE / 'observations/quarantine-stage316.json').write_text(json.dumps(quarantine_record, indent=2, sort_keys=True) + '\n')
    elif not quarantine316.is_file() or digest(quarantine316) != rejected316_sha:
        raise RuntimeError('stage 316 rejected-object quarantine drift')
    failed317_obs = STAGE317_FAILED_PACKET / 'observations/batch-064/stage-0317'
    if digest(failed317_obs / 'terminal.json') != '88bfb2bc6571cc5ec5a42057d3a13f0df0c280ea7c257347f1170c7e91abfc0d' or digest(failed317_obs / 'compile.log') != '35d364ee6cecd56d40079806c8dbb9818518b118b9a2a1af1e186c1ca5b4c0c2':
        raise RuntimeError('failed stage 317 receipt or log drift')
    failed317 = json.loads((failed317_obs / 'terminal.json').read_text())
    if failed317['exit_code'] != 1 or failed317['object_sha256'] is not None or failed317['guards'] != {p: record(p) for p in failed317['guards']}:
        raise RuntimeError('failed stage 317 outcome or dependencies drift')
    failed95_obs = STAGE95_FAILED_PACKET / 'observations/batch-019/stage-0095'
    if digest(failed95_obs / 'terminal.json') != '80ab9eeb822e89f2664b7b2c3884ffaf3ae96dd718c3fb54ba85c3e86f95bb1e':
        raise RuntimeError('failed stage 95 receipt drift')
    failed95 = json.loads((failed95_obs / 'terminal.json').read_text())
    if (failed95['exit_code'] is not None or failed95['object_sha256'] is not None or
        not failed95['source_unchanged'] or not failed95['guards_unchanged'] or
        failed95['guards'] != {p: record(p) for p in failed95['guards']}):
        raise RuntimeError('failed stage 95 guards or outcome changed')
    previous = check_prior(order, base)
    env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': f'{LIB}:{PACKAGE}', 'LEAN_NUM_THREADS': '1'}
    for position in range(len(previous), min(len(previous) + count, len(order))):
        check_resources()
        if shutil.disk_usage('/tmp').free < 4 * 1024**3:
            raise RuntimeError('less than 4 GiB free')
        module = order[position]
        index = position + 1
        if index == 285:
            available = next(int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
            if available < 12 * 1024 * 1024:
                raise RuntimeError('less than 12 GiB available for higher-memory stage 285')
        row = cone['candidate_sources'][module]
        source = REPO / row['canonical_candidates'][0]
        suffix = module.replace('.', '/') + '.lean'
        root = str(source)[:-len(suffix)].rstrip('/')
        if str(source) != root + '/' + suffix:
            raise RuntimeError(f'source root mismatch: {module}')
        output = LIB / (module.replace('.', '/') + '.olean')
        if os.path.lexists(output):
            raise RuntimeError(f'output already exists: {output}')
        output.parent.mkdir(parents=True, exist_ok=True)
        obs = receipt_dir(index)
        obs.mkdir(parents=True, exist_ok=False)
        (obs / 'source.lean').write_bytes(source.read_bytes())
        deps = subprocess.run([str(LEAN), '--deps', str(source)], env=env,
                              capture_output=True, text=True, timeout=120)
        (obs / 'deps').write_text(deps.stdout)
        (obs / 'deps.stderr').write_text(deps.stderr)
        if deps.returncode != 0 or deps.stderr:
            raise RuntimeError(f'dependency scan failed: {module}')
        guards = {}
        for line in deps.stdout.splitlines():
            path = Path(line)
            if not path.is_absolute() or not path.is_file() or path.suffix != '.olean':
                raise RuntimeError(f'missing or invalid dependency for {module}: {line}')
            stem = str(path)[:-len('.olean')]
            for ending in SUFFIXES:
                guards[stem + ending] = record(stem + ending)
        command = [str(LEAN), '-M6000' if index == 285 else '-M3000', '-j1', '-DElab.async=false', f'--root={root}',
                   str(source), '-o', str(output)]
        start = time.monotonic()
        try:
            proc = subprocess.run(command, env=env, capture_output=True, text=True,
                                  timeout=600 if index == 95 else 360 if index == 285 else 180)
            code, log = proc.returncode, proc.stdout + proc.stderr
        except subprocess.TimeoutExpired as exc:
            code = None
            log = ((exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout, bytes) else (exc.stdout or ''))
            log += ((exc.stderr or b'').decode(errors='replace') if isinstance(exc.stderr, bytes) else (exc.stderr or ''))
        (obs / 'compile.log').write_text(log)
        guards_ok = guards == {path: record(path) for path in guards}
        source_ok = digest(source) == row['source_sha256']
        accepted_warning = False
        if index in (79, 81, 84, 197, 224, 250, 251, 263, 266, 268, 270, 272, 275, 301, 306, 307, 310, 311, 312, 314, 316):
            verifier = (STAGE79_PACKET / 'verify_warning.py' if index == 79 else
                        STAGE81_PACKET / 'verify_warning.py' if index == 81 else
                        STAGE84_PACKET / 'verify_warning.py' if index == 84 else
                        STAGE197_PACKET / 'verify_warning.py' if index == 197 else
                        STAGE224_PACKET / 'verify_warning.py' if index == 224 else
                        STAGE250_PACKET / 'verify_warning.py' if index == 250 else
                        STAGE251_RETRY_PACKET / 'verify_warning.py' if index == 251 else
                        STAGE263_PACKET / 'verify_warning.py' if index == 263 else
                        STAGE266_PACKET / 'verify_warning.py' if index == 266 else
                        STAGE268_PACKET / 'verify_warning.py' if index == 268 else
                        STAGE270_PACKET / 'verify_warning.py' if index == 270 else
                        STAGE272_PACKET / 'verify_warning.py' if index == 272 else
                        STAGE275_PACKET / 'verify_warning.py' if index == 275 else
                        STAGE301_PACKET / 'verify_warning.py' if index == 301 else
                        STAGE306_PACKET / 'verify_warning.py' if index == 306 else
                        STAGE307_PACKET / 'verify_warning.py' if index == 307 else
                        STAGE310_PACKET / 'verify_warning.py' if index == 310 else STAGE311_PACKET / 'verify_warning.py' if index == 311 else STAGE312_PACKET / 'verify_warning.py' if index == 312 else STAGE314_PACKET / 'verify_warning.py' if index == 314 else STAGE316_PACKET / 'verify_warning.py')
            verified = subprocess.run([sys.executable, '-I', '-B', str(verifier),
                                       str(obs / 'compile.log')], capture_output=True, text=True)
            (obs / 'warning-verifier.stdout').write_text(verified.stdout)
            (obs / 'warning-verifier.stderr').write_text(verified.stderr)
            accepted_warning = (verified.returncode == 0 and not verified.stderr)
        clean = not any(x in log for x in ('error:', 'warning:', 'sorryAx'))
        success = (code == 0 and output.is_file() and not output.is_symlink() and guards_ok and source_ok and
                   (accepted_warning if index in (79, 81, 84, 197, 224, 250, 251, 263, 266, 268, 270, 272, 275, 301, 306, 307, 310, 311, 312, 314, 316) else clean))
        terminal = {'index': index, 'module': module, 'command': command, 'exit_code': code,
                    'duration_seconds': round(time.monotonic() - start, 3),
                    'wall_timeout_seconds': 600 if index == 95 else 360 if index == 285 else 180,
                    'runner_sha256': digest(Path(__file__)), 'lean_sha256': digest(LEAN),
                    'source_sha256': digest(source), 'source_unchanged': source_ok,
                    'guards': guards, 'guards_unchanged': guards_ok,
                    'object_sha256': digest(output) if output.is_file() else None,
                    'log_sha256': digest(obs / 'compile.log'), 'success': success,
                    'accepted_exact_warning': accepted_warning,
                    'scope': 'author prefix; dynamic, package and original provider ancestry not authenticated'}
        (obs / 'terminal.json').write_text(json.dumps(terminal, indent=2, sort_keys=True) + '\n')
        print(json.dumps({k: terminal[k] for k in ('index', 'module', 'exit_code', 'duration_seconds', 'success')},
                         sort_keys=True), flush=True)
        if not success:
            raise RuntimeError(f'stage failed: {module}; inspect before retry')
    check_pins()
    check_sources(cone)
    verify_overlay(manifest)
    done = check_prior(order, base)
    print(json.dumps({'completed': len(done), 'total': len(order), 'overlay_unchanged': True}, sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
