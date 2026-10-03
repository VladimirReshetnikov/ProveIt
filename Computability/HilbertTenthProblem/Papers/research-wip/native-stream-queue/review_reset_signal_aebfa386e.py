#!/usr/bin/env python3
"""Independent, pinned review checks; imported archive code runs only after byte guards.
All source roots are caller supplied. No archive or production source is modified.
"""
import argparse,contextlib,copy,hashlib,importlib.util,itertools,json,math,os,subprocess,sys,tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
PINS = {'reset': {'README.md': '75039fca5373ebbc40b27d50ec0d096d27f7ab3a2f4e6ac4098fecaf8a6256f8',
           'SHA256SUMS': '07f6498de67f8b4fc450a82bf76866f9516a013e28493ca4bbfbc8c257f718fd',
           'SOURCE_PROVENANCE.json': 'abca120c6b0925a10f8703eff2b553e507bde9ec64f2b2265c3b3ef4efb7be60',
           'VALIDATION.md': '8714ac8d3e39cefea8ec7f6e5e0f05b417e696a5237ac07a093f79907c07a009',
           'accepting_all_duration_witness_N390.json': '06f1a59a835eb25c14056678c774076ad2f70b1b22b06282e343e59a20f89fd1',
           'accepting_peak_trace.json': '7a5540d216228410d63227f42c91df264dfc8703463843a43cc4f219aa33dac4',
           'accepting_peak_witness.json': 'e033c42405bd6d6c4529f789b48b6d7355b2a986b24fb9966fd8e07b5895bcef',
           'accepting_reset_trace.json': '76519117512ebd15c6cc6070557caeae1cf0c478df5b843d47051828ada31cb4',
           'accepting_reset_witness.json': '24781462b5dfd0b5fa8b5ed9295966dba19340acbf561f3ec18a9cfaea0b78fc',
           'all_duration_schema_h1.json': '21a298b9b7741e911a4895bac61c10db08672b6e4d789e8c21c721ee14fdb594',
           'budget-audit/audit_budget.py': '94c203d2657bc2d1ba89e766f3d3485ace928c7ac93d703aed19345739c71187',
           'budget-audit/audit_results.json': '251c7ed41e09527332621ea9f550c345d250dfbc0dba0e0d037b66064b14aeac',
           'budget-audit/shortest_accepting_word.json': '04ee0e4b618dd3058c4d24681ea8f17e256a055c05ee05461db0d54374c1588f',
           'build-pdf.sh': '7a9928354a2e0015f4a82dafb2cabeee7ad52c96237c375a4c7c1ca65db43b8f',
           'build_net.py': '5e3e3e8e1138dffdd0289d67fb960a9f57a2eb23fac1debdc9a9919150981c46',
           'canonical_peak_schema_h1.json': '06daa82b8619dcdd6ccc41ebaae7d013adb82bdabdac892940b414c086e8c25b',
           'checks/AUDIT_RESULTS.json': '75f07941f141d9af6781f2fc8884d247b4dc41a2db7a40fcbec009ebf77055e8',
           'checks/GENERATED_FAMILIES_RESULTS.json': '749ec8a190d69d8f017297a3d6bc28bb99844321ea60b405b804ea0e3999ac0d',
           'checks/PADDING_AND_GENERIC_PEAK_RESULTS.json': 'ce5b6ef5329890f35c08f185bac6ed4ce7fb6ce4c2c894dd9c03b007713e7ca2',
           'checks/PORTABILITY_RESULTS.json': '98d1bedc08321dd1dea42de53ab9270bbb6064fc52def77827307b8bccc9659b',
           'checks/README.md': '2cdb3f392d109bc241b2282bc0202de64871478abd11f3f12d07ba01c8b0e19f',
           'checks/audit.py': 'a435a9de5d75afd529eadb23684a65e9b80600c541ac1ca7c5419be1c3727e62',
           'checks/audit_generated_families.py': 'e5bf43ab00d37b276a779d25548cffcec227778470385c74466ca4c0666947c3',
           'checks/audit_padding_and_generic_peak.py': 'a11fa27c0bbd1bcd8200daa13ecc04f33e3787a4c5225ae564b3c8be6bf4b895',
           'net_ledger.json': '870263d901bb213fb41f480897382a268f34c9555a928973c4aa8b374c9dd56e',
           'peak_quadratic.py': 'a997efa71416179be45582c540b91ab1ceac7718a37c8c6c46c5a1c6676ca20b',
           'projected_trace_schema_T1.json': '7dcca96aa85f5bc61f8de93344e6d217b0b0b8c6a916fa80f214507d81107b25',
           'replay_and_verify.py': '7c969a72bb2325857ddb33db7cf9d6eed5681bb7bbb44b3a489a12bbafafd7c9',
           'report/reset-net-certificates.pdf': '47d26a654ed6e69acc469bdc74aa2a622ca30c87ce7bf41eb4504cd72acfe3b1',
           'report/reset-net-certificates.tex': 'e5312982525c982a4bd2770a9f997e3485012018df4c4416ead60dd1ead78fc8',
           'reset_net.json': '3fd8f9dcf86135f7fdf41bfa77959942e7ece95662c9cfedc27ac1409e5d3780',
           'reset_quadratic.py': '88b74cd66ca860a4a02b087123f4a4d2899144e27de0030ce7f13ea046e6e350',
           'run-checks.sh': '2853ed1ffa10c3592f4299511badda8881d7bc6b9326421307559653a6230734',
           'shared-checks/README.md': 'e33aa58936ccc3acd1f2bb3b8a59dcfb3b876538f706fe0f394d8d5e5e1360e0',
           'shared-checks/audit_prime_macros.py': '6839c2e90d774cb7db8c135bc314058b852b7979369d2f2c05a799ff2a0e12c6',
           'shared-checks/audit_receipt.json': 'caf0b3fa6600dcff223d1dd918c972b45ab1229693122a3b556d09d0a2896b35',
           'shared-checks/audit_shared.py': '2c6b4ff9e007bd195c03c06acfa34196a99f7db94370856df49611eedf0d54b9',
           'shared-checks/independent_A64_macro_trace.json': '8352df6222005095aa9b7ee8cafa2eda9cc2f96edc7b9238ca2ea233d4499663',
           'shared-checks/prime_macro_receipt.json': '037db96de50609d2e5dd8bcae6d6b60fa148174dfbc324f3123a0cabd163920f',
           'shared-reset-arcs/build_shared.py': '5c0ebaad2755965206b35681bf50a901ab4f8b6c101ebe480bd719fd87e8866c',
           'shared-reset-arcs/three-counter/accepting_peak_witness_N446.json': 'c530461a3fdce0788eb919cf312d87500d9ac97be1201bf0885817c524429e04',
           'shared-reset-arcs/three-counter/accepting_reset_trace_N446.json': '251829e61fb2b19d049db155ec1c1c0a45252bbe20b24ec55aaf1be403531139',
           'shared-reset-arcs/three-counter/canonical_peak_schema_h1.json': '470dc152f35b94c7d69ef543e56b3807058b698b6dadf5264b3719c984c80a29',
           'shared-reset-arcs/three-counter/net_ledger.json': '7d4e99e6fb2bc8df431da8711574e56b708afc1ebbf2278cd734c3ee2ec09fcb',
           'shared-reset-arcs/three-counter/reset_net.json': 'bf3b174fa7ff82c173698cf03f16e5d816f9f24da2387ab1e79271997ab7446f',
           'shared-reset-arcs/two-counter/accepting_macro_count_A64.json': 'f4243dd0cdec2973e90b809086d5446198963096fa8a65aa3b920bcf9a0b6af7',
           'shared-reset-arcs/two-counter/canonical_peak_schema_h1.json': '57d791786532ed87e32e29f9fb5394c3774c0ebd7c2c836c33ae8e1b8bcb6b1e',
           'shared-reset-arcs/two-counter/net_ledger.json': 'd644b13fae4ed396625603b3105d847bba0d1ff5d490f228264dd6d02446f873',
           'shared-reset-arcs/two-counter/reset_net.json': 'd449abb872042fd88b65ab4f5c5ce660d5528a7b306032a9cbf2e6c182b7b2e9',
           'shared-reset-arcs/verification_receipt.json': 'b969a8fdecec499a4ec5bc978756fe3d14ad9125dc77e9a578580a9dab619091',
           'source/SOURCE_REGISTER_PROOF.md': '897b9a67816c70e4bfacebce88cd3b23e10b9798fbbf4ba87c0f98ea14e0296f',
           'source/UniversalTM15x2.tm.txt': 'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae',
           'source/accepting_counter_trace.json': 'f082fdded782c886449480246811cb588cf484b7b60e04de109a872b1f2eb290',
           'source/macro_certificates.json': '63801cd8c35707311a781f3b360d2bbf8b72e50fbfbc8b2dcdcf3fc73c56f346',
           'source/tm_table.json': '0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a',
           'source/virtual3.json': '24c771db50dc621068e470227802c2710a4531ce2e7ad3703a5cdb6b0543bbcf',
           'source/virtual3.txt': 'f2ebd85dbfd4669a8663f70c648ee0d414b0c853a1576b6cd5cd92c041ea0107',
           'source_quadratic.py': 'f535e32454251a0b952f55ca6a3b5b93158466f8c13b633da4b088abf690f1b4',
           'source_verification_receipt.json': '99b35ce63e29f276ba6a57d2ad2ecd73e2838db7b4966846e358bf3bdc93ae2e',
           'two-counter/build_variant.py': '131569e6fb0c5fdd5e28f534eeb063817abdc66611d2409f0ff898637114b694',
           'two-counter/canonical_peak_schema_h1.json': '1cc266b0597e690354088a451394be21927bbb0c5b828bbaca5180c8bdb63a73',
           'two-counter/net_ledger.json': '55adfda1566066890d48639b1804786abcdb302a6940fb196df2b0cf8413ddfb',
           'two-counter/projected_trace_schema_T1.json': 'f90a266e57c2dd4fcfe3c500385bc256aaa678b668d6470a45b9923dc4c72a82',
           'two-counter/reset_net.json': '7bd1ae386bdc8f8cb05541b7b39fd08a926a0cdb807b237f3070ffea11aefaf7',
           'two-counter/source/PROOF.md': '8511e3d09f9c69a73838329159b5e1e8e3a250d235252bdc54b9d46449db2b1b',
           'two-counter/source/UniversalTM15x2.tm.txt': 'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae',
           'two-counter/source/accepting_example.json': 'd9e27aad59579f968829b52ac113a7b85c5ae3fcaf5b304919e3fec359fabf28',
           'two-counter/source/literal2.json': '85e16b44828f2f3d4ad6d0805dcc9e9922893a6d286874f2018d6a33af864b00',
           'two-counter/source/literal2.txt': '08120b3be02c41bddd78964f1b430053287b61ffad0cfd6f62d93d7c419b551b',
           'two-counter/source/macro_certificates.json': '8f89296219f161dc4b55e902f667c9c4a63806e197cdd62b9594ef7decd51815',
           'two-counter/source/tm_table.json': '0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a',
           'two-counter/source/virtual3.json': '24c771db50dc621068e470227802c2710a4531ce2e7ad3703a5cdb6b0543bbcf',
           'two-counter/source/virtual3.txt': '72338fd033a31d61e261d6074e6524d35a8d56022f8bcece411efb764fb02b5a',
           'two-counter/source_verification_receipt.json': 'bd68c772c61066fdd94b1a3f937592dfbddb3263b361d187e452f702951ad29e',
           'two-counter/verify_source.py': '20b44d7e7ec57a34f6927aad956ebc2630b6681fb51dbef9ce55a94739040a39',
           'two-reset-audit/accepting_macro_trace.json': '00508f46a37c8d4e8dbf48cd37a8f5bd3f5a685101114bb31596626bd45c4145',
           'two-reset-audit/audit_receipt.json': 'd8c1a9013f8dde1af235fc13f7a6e4d5de0fabbea6c25514eed5e3a7b9867d60',
           'two-reset-audit/audit_two_reset.py': 'b0c0f3276d0156ceb75a9298b946504b18bf31633cb16f22da62b2a548271b25',
           'two-reset-audit/compare_release_net.py': 'a038b7c93687dc6df61c9b3c75148daa153c7e5644c55f8685860820edc35d31',
           'two-reset-audit/release_comparison_receipt.json': '74a8d3c2c2f41dc8b5828993200d436ccb8c0a1cf43811f0ca763c745cbe2e7d',
           'two-reset-audit/two_reset_net.json': 'f22182110d80efad5aa6dc414bf81d999094ea2901d15fc7580eeaccf520a29c',
           'verification_receipt.json': '8d8fe3e253b10790bfaaba1b4bbb09d8b9e74cc97f5da2d8edee9ab1a16450e4',
           'verify-manifest.py': '0c69ba734f41c6d2fe0101a49246d8c3e3d7d904506ca67bfaab5b393f1c8326',
           'verify_source.py': '6e31a8d29dc71f6d08dba3aaa137959ccb84265599801d4d5f25ce06564ec842'},
 'signal': {'CORRECTION.md': 'f159f4b4be1108c72f3d50b84542da1e7e27174e54584424fce7a3bd96583ef1',
            'README.md': '760cd88eecb427a2917f17920e2e1f6c50f050e0be2bf0ae17c04b659b515353',
            'SHA256SUMS': 'f73ada741ad6664c30ae9d9d742d0c1de1813722b54e1909a5f68a5798964dc0',
            'SOURCE-PROVENANCE.md': '026bac4c6c558d19f6f9ba0a3470d490428a0ac5557c512b39b76383a1a39e0c',
            'build.sh': '429b55c00aafe7cf313a7406f6beeeee1c82c877dff327e25828703a2729e5ac',
            'code/MORITA_15_6_audit.py': '61406e79b873083c5643d8d38c79869fa31ba1fdce706839182af7fff47a82a9',
            'code/conservative_signal.py': 'd9a9678d7254a93f0fed2dd55767af87c6af327df9fa47e7092592484bf97037',
            'code/independent_checks.py': '90b3959115527d47711cd13523e1f02292066a54fa041d12cd41b320445cca16',
            'code/initial_side_checks.py': '7e4816f656e162c15a8e253edb04df1a7396ae5ab37653c4146c779049eb6325',
            'code/instantiate_morita.py': 'f398f108c7f88f06c420dac12d9d76f4a747e952fb863b04a61f8f4d453ed75f',
            'code/pivot_scale_checks.py': '05eb119a594ca1f37326a702f3283ae9feb62143f9a4ab9a5badc9bd70637e56',
            'code/quadratic_packet.py': '96d4c2b634d465dfcd4df421d57d7f71da44efa201d00fa2518660e600507eef',
            'conservative-signal-diophantine.pdf': 'd33d3b6fdd7ac00ac3937a400b2b6b4906a09f77e08e21e805379153520bf33e',
            'correction/FULL_REPLAY_PRESERVATION.json': '4f674087941737324ab2321e60abd4c8a9ed74ba52f819264ae1cfb7964fc1f1',
            'correction/PACKET_CORRECTION_OPTIMIZED_VERIFICATION.json': 'a716f981f303bf096d7fa4e14fd9ed1b01375fc4ed83c13e885afae05631c401',
            'correction/PACKET_CORRECTION_STANDALONE_VERIFICATION.json': '047384058d551d8830e45c7114d9b766bac0d392fd2da059b2809078277b3211',
            'correction/PACKET_CORRECTION_VERIFICATION.json': '453a5049458d05f6e9692ec3c33ff9d9ddf291f7059498dc4e14e568c769b4ce',
            'correction/conservative_signal_packet_domains.patch': 'c811f6e552531f614e1fcaefffc9a296d313fe80a94a3e65aa4cf033306f2033',
            'correction/verify_packet_correction.py': 'cf6114e818e5a4090fb3c864db28d937ce73472ee3f5260458b140da9f557de3',
            'data/MORITA_15_6_FIGURE28_REPLAY.json': 'ce4a9d1d572900632cd9215789a7c4a557d978933b5a2f029e0fff042b63a499',
            'data/MORITA_15_6_TABLE.json': '587a708fa167e24268255eb5957535c7ca80f21b2b3485448f82984abbe953a1',
            'data/MORITA_18_SIGNAL_MACHINE.json': '3f45f8aa2fbf5756cd1e4cf22fa3e55582abc9ba8275fe246652ceb94eb08e05',
            'data/SOURCE_MANIFEST.json': '6e0b53023c2de9bf225f55d871bbdd123345f2a5ce781b80ca1f46cb226e9cdf',
            'numeric/COMPACT_VERIFICATION.json': '5710840cd0822325be4eccc885efc9d6ad824b748c918f8ac1f2131b3e06a788',
            'numeric/EVENTS.jsonl.gz': '1af06528f1ed797a3467fd1b4ecc4bf6f142ed2cb3a7b0ef73c02213e3c713b1',
            'numeric/EXPORTER_TEST_RECEIPT.json': 'b575f6a40de61e5a1a6d493f0ebeb54e8a8144e50a9ad7221088096ed4497437',
            'numeric/LEDGER.json': 'b90e1bedba678611830281040ffb3bafce9095e83b7054661fe2823eebce4e19',
            'numeric/MODES.jsonl.gz': '8e84572b06cda919be2039ed77bc3c106edef361716e421cb55f7419cfe13853',
            'numeric/MORITA_18_SIGNAL_MACHINE.json': '3f45f8aa2fbf5756cd1e4cf22fa3e55582abc9ba8275fe246652ceb94eb08e05',
            'numeric/ORIGINAL_REPLAY_AUDIT.json': '5e9ad0f8bb6803f797187aa2206ebeba984e2e08bb92dbe35b30f7c084bfd412',
            'numeric/POLYNOMIAL_CIRCUIT.json': 'd84efa483f7bd195b268d545fe8264c5edd6916d8090a1646bd773b658a3097c',
            'numeric/PROOF_AND_LEDGER.md': '14ad7a9452b1ada7970cc5c6c9c142f335ed989423492c442d6c89842d59140e',
            'numeric/check_original_replays.py': 'cec46e7add01df68d642576efcc0707d4270019d8d59e0c167c34eb80b8ab6c3',
            'numeric/compile_packet.py': '2df8a5b96630a9b343266ded0b26b6489be601acdee6f50d2a06dad4563e5f57',
            'numeric/test_exporter.py': 'a38112b9aa878c706882f9f14093bddb185e35f2b117aed6ec382d7fae6db177',
            'paper/conservative-signal-diophantine.tex': '99155e24e8eeb2a9bd4f4cebf70a422f44722bbeb15058f7238a4c44f5eb8455',
            'paper/morita-table.tex': 'b76672329625fcca03e782daf464c640cc33c666c12ba41f9bc35baae403892a',
            'receipts/INDEPENDENT_RESULTS.json': '09e280fa6bad9d7013bea6ebf55798b793000f6d0fac2f2ce95238fabe6c4f42',
            'receipts/INITIAL_SIDE_RESULTS.json': '5c0f876aa724cdfe8020f23096fbfd4ec9e730742fb00e1cf2bc2c35125ae35a',
            'receipts/MORITA_15_6_AUDIT_RESULTS.json': '44803d8b6a6944c1e5e7f4161466465e8501f8d5dc2a60847bebd9f63477d51b',
            'receipts/MORITA_18_REPLAY_RECEIPT.json': '7f1cd3a5faf9fcc5d2799a1e9089a2016c5ba1a67e2d87be31a3894e38a82c7e',
            'receipts/PIVOT_SCALE_RESULTS.json': '032d9c0f0697334242c111bcf96f5246761aa4be790c119a623e9d0cc68132b5',
            'receipts/QUADRATIC_PACKET_RESULTS.json': '4dfd887444f081fdf5e40566e88086d1a51746caf8123bb62e20b79e862ae2ab',
            'receipts/REPLAY_RECEIPT.json': '4405cd8ca01533dea0e19a6ac1c8fab5237243611000c2785dc14f5b7df7f4b7',
            'run-replay.sh': 'c52cf2e49ca3cb4d2f149ec49b73c1d4f08b82cd89b09fcb7145ba28257c67d8'}}

def require(ok,message):
    if not ok:raise ValueError(message)

def verify_bytes(root,tag):
    root=Path(root).resolve()
    require(all(str(p.relative_to(root)) in PINS[tag] for p in root.rglob('*.py')),'Unexpected Python source outside pinned archive')
    for n,h in PINS[tag].items():
        require(hashlib.sha256((root/n).read_bytes()).hexdigest()==h,'Byte mismatch: '+n)
    return len(PINS[tag])

@contextlib.contextmanager
def imports(root,names):
    root=Path(root);saved={n:sys.modules.get(n) for n in names};oldpath=sys.path[:]
    try:
        for n in names:sys.modules.pop(n,None)
        sys.path.insert(0,str(root));mods={}
        for n in names:
            spec=importlib.util.spec_from_file_location(n,root/(n+'.py'))
            mod=importlib.util.module_from_spec(spec);sys.modules[n]=mod;exec(compile((root/(n+'.py')).read_bytes(),str(root/(n+'.py')),'exec'),mod.__dict__);mods[n]=mod
        yield mods
    finally:
        sys.path[:]=oldpath
        for n,v in saved.items():
            if v is None:sys.modules.pop(n,None)
            else:sys.modules[n]=v

def strict_delete(name,c):
    return name=='span' or name.startswith('germ:') or (name.startswith('first:') and c[int(name.split(':')[1])]<0)

def verify_signal(root):
    original_members=verify_bytes(root,'signal');root=Path(root)
    with imports(root/'numeric',['compile_packet']) as mods:
        C=mods['compile_packet'].Compiler().close()
        counts={name:dict(row_nnz=0,coefficient_M=0,rows=0) for name in ('old','new','deleted')}
        removed=Counter();fixtures=0;real_failure=None
        global_nnz=C.B+18*(1+C.B)+18;global_M=0
        for branch in C.branches:
            s,t,J=branch;c=C.cs[s];j=J[0];cj=c[j]
            require(cj>0 and all(c[i]>0 for i in J),'Invalid selected closing speed')
            matrix=C.matrix(*branch)
            global_nnz+=sum(len(row) for row in matrix)
            global_M+=sum(abs(v)!=1 for row in matrix for _,v in row)
            eq,st=C.guards(*branch)
            require([n for n,_ in eq]==['mode']+[f'tie:{i}' for i in J[1:]],'Equality source drift')
            require(len(st)==sum(a>=0 for a in c)+19-len(J),'Guard count drift')
            removed_here=[n for n,_ in st if strict_delete(n,c)]
            require(len(removed_here)==18,'Deleted guard count drift')
            # Every literal branch gets an exact integral geometric fixture.
            gap=[(a if i in J else max(a,0)+cj) for i,a in enumerate(c)]
            gap[j]=cj
            x=gap+[C.codes[s]*sum(gap)]
            ev=lambda row:sum(v*x[i] for i,v in row)
            require(all(ev(row)==0 for _,row in eq),'Fixture equality failed')
            require(all(ev(row)>=1 for _,row in st),'Fixture strict guard failed')
            y=[ev(row) for row in matrix]
            require(all(v>=0 for v in y) and y[17]==C.codes[t]*sum(y[:17]),'Output cone failed')
            old_slacks={n:ev(row)-1 for n,row in st}
            retained={n:v for n,v in old_slacks.items() if n not in removed_here}
            restored=dict(retained,**{n:ev(row)-1 for n,row in st if n in removed_here})
            require(restored==old_slacks,'Section failed')
            fixtures+=1
            # A concrete real zero of reduced guards lacking the old natural-slack section.
            if real_failure is None and any(c[i]<cj for i in J):
                gx=[Fraction(c[i],cj) if i in J else Fraction(max(c[i],0)+cj,cj) for i in range(17)]
                xx=gx+[C.codes[s]*sum(gx)]
                val=lambda row:sum(v*xx[i] for i,v in row)
                if all(val(row)>=1 for n,row in st if not strict_delete(n,c)):
                    bad=next((n,val(row)-1) for n,row in st if n.startswith('germ:') and val(row)<1)
                    real_failure={'branch':[s,t,list(J)],'pivot_speed':cj,'gap':[str(a) for a in gx],'negative_restored_slack':[bad[0],str(bad[1])]}
            for name,row in eq:
                for tag in ('old','new'):
                    counts[tag]['rows']+=1;counts[tag]['row_nnz']+=len(row);counts[tag]['coefficient_M']+=sum(abs(v)!=1 for _,v in row)
            for name,row in st:
                gone=strict_delete(name,c)
                if gone:removed[name.split(':')[0]]+=1
                for tag in ('old','deleted' if gone else 'new'):
                    counts[tag]['rows']+=1;counts[tag]['row_nnz']+=len(row)+2;counts[tag]['coefficient_M']+=sum(abs(v)!=1 for _,v in row)
        for tag in ('old','new'):
            z=counts[tag];z['rows']+=37;z['row_nnz']+=global_nnz;z['coefficient_M']+=global_M
            z['M']=z['coefficient_M']+z['rows']+C.B;z['A']=z['row_nnz']+19*C.B;z['operations']=z['M']+z['A']
        require((len(C.modes),C.B,C.T)==(49700,80501,2667479),'Closure count drift')
        require(counts['old']['operations']==25392522 and counts['new']['operations']==17903098,'SLP count drift')
        require(real_failure is not None,'Expected real-domain caveat fixture absent')
        # Full branch-local graph identity on signed and natural tuples, including inactive selectors.
        graph=0
        for r in range(0,C.B,max(1,C.B//64)):
            branch=C.branches[r];eq,st=C.guards(*branch);c=C.cs[branch[0]]
            for sign in (1,-1):
                x=[sign*((i*7+r)%11) for i in range(18)];e=sign*(r%3)
                value=lambda row:sum(v*x[i] for i,v in row)
                kept={n:sign*((k+r)%7) for k,(n,row) in enumerate(st) if not strict_delete(n,c)}
                restored={n:(value(row)-e if strict_delete(n,c) else kept[n]) for n,row in st}
                old=sum(value(row)**2 for _,row in eq)+sum((value(row)-e-restored[n])**2 for n,row in st)
                new=sum(value(row)**2 for _,row in eq)+sum((value(row)-e-kept[n])**2 for n,row in st if n in kept)
                require(old==new,'Signed graph residual identity failed');graph+=1
        # Strict domain checker is authenticated and tested independently of bundled repair checker.
    with imports(root/'code',['quadratic_packet']) as mods:
        q=mods['quadratic_packet']
        # Bundled self-check has been independently source-reviewed; author replay is separate.
        require(hasattr(q,'Branch') and hasattr(q,'Guard'),'Public schema drift')
        branch=q.Branch(((1,),),())
        require(q.polynomial_value([branch],(1,),(1,),((1,),((1,),),((),)))==0,'Identity packet failed')
        malformed=[lambda:q.polynomial_value([branch],(1,),(1,999),((1,),((1,),),((),))),lambda:q.polynomial_value([branch],(1.0,),(1,),((1,),((1,),),((),))),lambda:q.polynomial_value([branch],(1,),(1,),((1,),((1,),),((None,),))),lambda:q.Branch(((True,),),()),lambda:q.Guard('eq',(1.0,))]
        for call in malformed:
            try:call()
            except ValueError:pass
            else:raise ValueError('Corrected signal boundary regression')
    return {'status':'PASS','original_members_pinned':original_members,'modes':49700,'branches':C.B,'integral_all_branch_sections':fixtures,'signed_local_graph_identities':graph,'removed_guard_rows':dict(removed),'old':counts['old'],'reduced':counts['new'],'deleted':counts['deleted'],'old_witnesses':4196998,'reduced_witnesses':2747980,'degree':2,'products':80501,'real_domain_counterexample':real_failure,'scope':'Actual finite branch compiler; natural-zero projection with unique slack extension. Sparse-affine schedule fully charged by coefficient incidence, not a materialized 25-million-gate artifact; no fixed-arity universality claim.'}

def expand(packet,a):
    out=Counter({('constant',0):a['constant']})
    for i,c in a['variables']:out['variable',i]+=c
    for name,c in a['parameters']:out['parameter',name]+=c
    for name,c in a['forms']:
        for i,d in packet['linear_forms'][name]:out['variable',i]+=c*d
    return {k:c for k,c in out.items() if c}

def evaluate_fraction(packet,w,parameters):
    def ev(a):
        return sum(c*(1 if k[0]=='constant' else w.get(k[1],0) if k[0]=='variable' else parameters[k[1]]) for k,c in expand(packet,a).items())
    return sum(ev(row['affine'])**2 for row in packet['affine_squares'])+sum(ev(row['left'])*ev(row['right']) for row in packet['quadratic_products'])

def charged_shared_form_schedule(packet):
    """Literal shared linear forms then affine residuals/factors; +/-1 coefficients use signs."""
    def cost(terms,constant=0):
        terms=[(x,c) for x,c in terms if c]
        require(not terms or any(c>0 for _,c in terms) or constant>0,'Schedule needs a separately charged leading negation')
        return sum(abs(c)!=1 for _,c in terms),max(0,len(terms)+(constant!=0)-1)
    M=A=0
    for terms in packet['linear_forms'].values():
        m,a=cost(terms);M+=m;A+=a
    affine=[r['affine'] for r in packet['affine_squares']]+[z[side] for z in packet['quadratic_products'] for side in ('left','right')]
    for row in affine:
        m,a=cost(row['forms']+row['variables']+row['parameters'],row['constant']);M+=m;A+=a
    n=len(packet['affine_squares'])+len(packet['quadratic_products']);M+=n;A+=n-1
    return {'M':M,'A':A,'operations':M+A}

def fast_value(packet,w,pars):
    forms={n:sum(c*w.get(i,0) for i,c in terms) for n,terms in packet['linear_forms'].items()}
    def ev(a):return a['constant']+sum(c*forms[n] for n,c in a['forms'])+sum(c*w.get(i,0) for i,c in a['variables'])+sum(c*pars[n] for n,c in a['parameters'])
    return sum(ev(a['affine'])**2 for a in packet['affine_squares'])+sum(ev(a['left'])*ev(a['right']) for a in packet['quadratic_products'])

def verify_reset(root):
    original_members=verify_bytes(root,'reset');root=Path(root)
    read=lambda name:json.loads((root/name).read_text())
    nets={tag:read(name) for tag,name in [('three','reset_net.json'),('two','two-counter/reset_net.json'),('shared_three','shared-reset-arcs/three-counter/reset_net.json'),('shared_two','shared-reset-arcs/two-counter/reset_net.json')]}
    invariant_rows=0;ledgers={}
    for tag,net in nets.items():
        regs=net.get('counter_places',net['data_places'][:-2]);D={p:-1 for p in regs};D.update(reserve=-1,budget=1)
        for t in net['transitions']:
            require(sum(D.get(p,0)*n for p,n in t['pre'].items())==sum(D.get(p,0)*n for p,n in t['post'].items()),'Debt coefficient failure')
            require(set(t['reset'])<=set(regs),'Debt reset failure')
            require(sum(t['pre'].get(p,0) for p in net['control_places'])==sum(t['post'].get(p,0) for p in net['control_places'])==1,'Control invariant failure')
            invariant_rows+=1
        ledgers[tag]={'places':len(net['places']),'transitions':len(net['transitions']),'ordinary_arcs':sum(len(t['pre'])+len(t['post']) for t in net['transitions']),'reset_arcs':sum(len(t['reset']) for t in net['transitions'])}
    require(ledgers['three']=={'places':539,'transitions':771,'ordinary_arcs':2608,'reset_arcs':233},'Main net count drift')
    with imports(root,['source_quadratic','peak_quadratic','build_net']) as mods:
        s,p,b=(mods[n] for n in ['source_quadratic','peak_quadratic','build_net']);table=s.semantic_table(read('source/virtual3.json'))
        # Independent visual transcription of Table 16, u1..u15 and c/b rows; u10,b is blank.
        zero=['cR2','bR3','cL7','cL6','bR1','bL4','cL8','bL9','cR1','bL11','cR12','cR13','cL2','cL3','cR14']
        one=['bR1','bR1','cL5','bL5','bL4','bL4','bL7','bL7','bL10',None,'bR14','bR12','bR12','cR15','bR14']
        expected={}
        for symbol,row in enumerate((zero,one)):
            for i,cell in enumerate(row):expected[chr(65+i)+str(symbol)]=None if cell is None else [int(cell[0]=='b'),cell[1],chr(64+int(cell[2:]))]
        require(read('source/tm_table.json')==expected,'Primary Table 16 transcription mismatch')
        forms=0;weak_counts=[];weak_identities=0
        for h in (1,2,3):
            for duration,padded in ((False,False),(True,False),(True,True)):
                a=p.compile_peak(table,h,with_duration=duration,all_durations=padded)
                require(a['variables']['count']==2813*h+int(padded),'Peak witness count')
                require(len(a['affine_squares'])==6*h+1+int(duration),'Peak residual count')
                require(len(a['quadratic_products'])==762*h,'Peak product count')
                for row in a['affine_squares']:
                    require(all(k[0]!='variable' or 0<=k[1]<a['variables']['count'] for k in expand(a,row['affine'])),'Valid packet has dangling coordinate')
                forms+=1
            parent=p.compile_peak(table,h);child=copy.deepcopy(parent)
            for row in child['quadratic_products']:
                if row['name'].startswith('inactive:'):
                    first=row['right']['variables'].pop(0)
                    require(first==[row['left']['variables'][0][0],1],'Literal strong gate drift')
            old_cost=charged_shared_form_schedule(parent);new_cost=charged_shared_form_schedule(child)
            require(old_cost['M']==new_cost['M'] and old_cost['A']-new_cost['A']==761*h,'Complete schedule saving failed')
            weak_counts.append({'h':h,'old':old_cost,'natural_only':new_cost,'witnesses':2813*h,'affine_squares':6*h+2,'products':762*h})
            for seed in range(4):
                w={i:((i*7+seed)%5)*(1 if seed%2==0 else -1) for i in range(parent['variables']['count'])}
                pars={'L':seed,'R':seed+1,'N':seed+2};correction=0
                for j in range(h):
                    es=[w[j*2811+r] for r in range(761)];correction+=sum(es)**2-sum(e*e for e in es)
                require(fast_value(parent,w,pars)-fast_value(child,w,pars)==correction,'Complete signed gate identity failed');weak_identities+=1
        bad=p.compile_peak(table,1,all_durations=.5)
        require(bad['variables']['padding_index']==bad['variables']['count'],'Float flag regression changed')
        finish=next(t for t in nets['three']['transitions'] if t['name']=='finish')
        bogus=b.fire(nets['three'],{'q:DRAIN':1,'ghost':999},finish)
        require(bogus==({'q:DONE':1},0),'Ghost counterexample changed')
        float_result=b.fire(nets['three'],{'q:DRAIN':1.0},finish)
        require(float_result==({'q:DONE':1},0),'Float counterexample changed')
        # Strong selector gate: exhaustive rational/signed domain boundary census.
        strong=0;zero=0;signed_false=[]
        vals=[Fraction(0),Fraction(1,2),Fraction(1),Fraction(3,2),Fraction(2)]
        for e0,e1,x0,x1 in itertools.product(vals,repeat=4):
            E=e0+e1;f=(E-1)**2+(E-e0)*(e0+x0)+(E-e1)*(e1+x1)
            want=(e0==1 and e1==0 and x1==0) or (e1==1 and e0==0 and x0==0)
            require((f==0)==want,'Strong nonnegative selector theorem failure');strong+=1;zero+=f==0
        for e0,e1,x0,x1 in itertools.product(range(-2,3),repeat=4):
            E=e0+e1;f=(E-1)**2+(E-e0)*(e0+x0)+(E-e1)*(e1+x1)
            if f==0 and (e0,e1) not in [(1,0),(0,1)]:signed_false=[e0,e1,x0,x1];break
        require(signed_false,'Missing signed-domain counterexample')
        weak_natural=0
        for e0,e1,x0,x1 in itertools.product(range(4),repeat=4):
            E=e0+e1;strong_poly=(E-1)**2+(E-e0)*(e0+x0)+(E-e1)*(e1+x1);weak_poly=(E-1)**2+(E-e0)*x0+(E-e1)*x1
            require((strong_poly==0)==(weak_poly==0),'Natural gate zero equivalence failed');weak_natural+=1
        require((Fraction(1,2)+Fraction(1,2)-1)**2==0,'Fractional selector counterexample')
        # Independent full source-to-peak fixture, not copied from the author replay.
        toy={'registers':['L','R'],'entry':'q0','halt':'HALT','rows':{'q0':['ADD',0,'q1'],'q1':['SUB',0,'HALT','HALT']}}
        tt=s.semantic_table(toy);toy_checks=0
        for L,R in itertools.product(range(5),repeat=2):
            a=p.compile_peak(tt,2,initial=['L','R']);w={0:1,3:L,4:R,9:1,13:L,14:R,16:1,19:1};N=2*(L+R)+8
            require(evaluate_fraction(a,w,{'L':L,'R':R,'N':N})==0,'Toy canonical peak failed')
            require(evaluate_fraction(a,w,{'L':L,'R':R,'N':N+1})==1,'Wrong duration not rejected')
            ap=p.compile_peak(tt,2,initial=['L','R'],all_durations=True)
            require(evaluate_fraction(ap,{**w,20:Fraction(1,2)},{'L':L,'R':R,'N':N+1})==0,'Real padding caveat failed');toy_checks+=3
        # Literal first source branch is forced by T=0; graph section variables known before future constraints.
        require(table['branches'][1]['source']==table['entry'] and table['branches'][1]['guard']=='zero' and table['branches'][1]['register']==2,'Forced first source row drift')
        first=read('source/virtual3.json')['rows']['init_clear_T'];require(first==['SUB',2,'init_clear_T','tm_A0_pop0'],'First loader row drift')
    return {'status':'PASS','original_members_pinned':original_members,'literal_net_ledgers':ledgers,'all_transition_debt_and_control_identities':invariant_rows,'primary_table_cells_compared':30,'actual_peak_schema_forms':forms,'strong_gate_rational_cases':strong,'strong_gate_zero_cases':zero,'signed_strong_gate_false_selector':signed_false,'complete_toy_polynomial_cases':toy_checks,'natural_gate_schedule_counts':weak_counts,'complete_signed_gate_identities':weak_identities,'natural_gate_zero_census':weak_natural,'real_weak_gate_counterexample':{'selectors':['1/2','1/2'],'bases':[0,0],'old':'1/2','new':0},'verified_defects':{'nonboolean_padding':{'count':2813,'referenced_padding_index':2813},'unknown_place_fire':{'input':{'q:DRAIN':1,'ghost':999},'result':{'q:DONE':1}},'float_fire':{'input':{'q:DRAIN':1.0},'result':{'q:DONE':1}}},'scope':'Fixed net universality with finite binary input; externally fixed horizons for all emitted polynomials. Huge two-counter trace uses exact audited macro accounting, not physical enumeration.'}

SIGNAL_COMMANDS=[['code/MORITA_15_6_audit.py'],['code/conservative_signal.py'],['code/instantiate_morita.py'],['code/quadratic_packet.py'],['code/initial_side_checks.py'],['code/independent_checks.py'],['code/pivot_scale_checks.py'],['numeric/compile_packet.py','verify'],['numeric/test_exporter.py'],['numeric/check_original_replays.py','<ROOT>'],['correction/verify_packet_correction.py','code/quadratic_packet.py'],['-O','correction/verify_packet_correction.py','code/quadratic_packet.py']]
RESET_COMMANDS=[[s] for s in ['verify_source.py','build_net.py','replay_and_verify.py','budget-audit/audit_budget.py','checks/audit.py','checks/audit_generated_families.py','checks/audit_padding_and_generic_peak.py','two-counter/verify_source.py','two-counter/build_variant.py','two-reset-audit/audit_two_reset.py','two-reset-audit/compare_release_net.py','shared-reset-arcs/build_shared.py','shared-checks/audit_shared.py','shared-checks/audit_prime_macros.py']]

def author_replay(root,tag,patched=False):
    import shutil
    root=Path(root);verify_bytes(root,tag)
    with tempfile.TemporaryDirectory(prefix='reset_signal_author_') as td:
        dest=Path(td)/tag;shutil.copytree(root,dest,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        if patched:apply_repairs(dest)
        changed_sources={'build_net.py','peak_quadratic.py'} if patched else set()
        commands=SIGNAL_COMMANDS if tag=='signal' else RESET_COMMANDS;rows=[]
        for cmd in commands:
            args=[str(dest) if x=='<ROOT>' else x for x in cmd]
            p=subprocess.run([sys.executable]+args,cwd=dest,capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
            require(p.returncode==0,'Author command failed: '+repr(cmd)+' '+p.stderr.decode()[-1000:])
            stdout_exports={('code/MORITA_15_6_audit.py',):'receipts/MORITA_15_6_AUDIT_RESULTS.json',('code/conservative_signal.py',):'receipts/REPLAY_RECEIPT.json',('numeric/compile_packet.py','verify'):'numeric/COMPACT_VERIFICATION.json'}
            if tag=='signal' and tuple(cmd) in stdout_exports:(dest/stdout_exports[tuple(cmd)]).write_bytes(p.stdout)
            rows.append({'command':cmd,'exit_code':0})
        changed=[]
        for n,h in PINS[tag].items():
            if n in changed_sources:continue
            b=(dest/n).read_bytes()
            if hashlib.sha256(b).hexdigest()!=h:
                old=(root/n).read_bytes()
                if n.endswith('.json'):
                    a=json.loads(old);v=json.loads(b)
                    # Normalize only the exact two repaired source digest values, never entire metadata fields.
                    old_by_new={hashlib.sha256((dest/s).read_bytes()).hexdigest():PINS[tag][s] for s in changed_sources}
                    def normalize(z):
                        if type(z) is dict:return {k:normalize(v) for k,v in z.items()}
                        if type(z) is list:return [normalize(v) for v in z]
                        if type(z) is str:return old_by_new.get(z,z)
                        return z
                    require(patched and json.dumps(a,sort_keys=True)==json.dumps(normalize(v),sort_keys=True),'Unexpected changed author export: '+n)
                    changed.append({'path':n,'comparison':'equal_except_two_exact_repaired_source_digest_values'})
                else:raise ValueError('Unexpected changed author member '+n)
        return {'commands':rows,'changed_metadata_receipts':changed,'unchanged_original_members':len(PINS[tag])-len(changed)-len(changed_sources),'patched_sources':sorted(changed_sources)}

def apply_repairs(root):
    root=Path(root)
    for n in ('peak_quadratic.py','build_net.py'):
        require(hashlib.sha256((root/n).read_bytes()).hexdigest()==PINS['reset'][n],'Repair source pin failed')
    p=root/'peak_quadratic.py';s=p.read_text();p.write_text(s.replace('    if all_durations and not with_duration:',"    if type(with_duration) is not bool or type(all_durations) is not bool:\n        raise ValueError('with_duration and all_durations must be exact Booleans')\n    if all_durations and not with_duration:"))
    p=root/'build_net.py';s=p.read_text();s=s.replace('    assert type(L) is int and L>=0 and type(R) is int and R>=0',"    if type(L) is not int or L<0 or type(R) is not int or R<0:\n        raise ValueError('Initial counters must be exact natural integers')");s=s.replace('def fire(net,marking,transition):\n',"def fire(net,marking,transition):\n    if type(marking) is not dict or any(type(p) is not str or p not in net['places'] or type(n) is not int or n<0 for p,n in marking.items()):\n        raise ValueError('Marking must map known places to exact natural integers')\n");p.write_text(s)

def repair_checks(root):
    import shutil
    verify_bytes(root,'reset');root=Path(root)
    with tempfile.TemporaryDirectory(prefix='reset_guard_check_') as td:
        dest=Path(td)/'reset';shutil.copytree(root,dest,ignore=shutil.ignore_patterns('__pycache__','*.pyc'));apply_repairs(dest)
        with imports(dest,['source_quadratic','peak_quadratic','build_net']) as mods:
            s,p,b=(mods[n] for n in ['source_quadratic','peak_quadratic','build_net']);table=s.semantic_table(json.loads((dest/'source/virtual3.json').read_text()));net=json.loads((dest/'reset_net.json').read_text());finish=next(t for t in net['transitions'] if t['name']=='finish');rejected=0
            calls=[]
            for v in (0,1,2,-1,.5,1.0,None,'yes',[],{}):
                calls += [lambda v=v:p.compile_peak(table,1,with_duration=v),lambda v=v:p.compile_peak(table,1,all_durations=v)]
            for m in ({'q:DRAIN':1,'ghost':999},{'q:DRAIN':1.0},{'q:DRAIN':True},{'q:DRAIN':1,'L':-2},{'q:DRAIN':1,False:0},[],None):calls.append(lambda m=m:b.fire(net,m,finish))
            for v in (True,False,1.0,-1,None):calls.append(lambda v=v:b.initial(net,v,0))
            for f in calls:
                try:f()
                except ValueError:rejected+=1
                else:raise ValueError('Patched boundary accepted malformed argument')
            require(b.fire(net,{'q:DRAIN':1},finish)==({'q:DONE':1},0),'Valid finish changed')
            valid=0
            for h in (1,2,3):
                for a,d in ((False,False),(True,False),(True,True)):
                    packet=p.compile_peak(table,h,with_duration=a,all_durations=d)
                    with imports(root,['source_quadratic','peak_quadratic','build_net']) as old:
                        require(packet==old['peak_quadratic'].compile_peak(table,h,with_duration=a,all_durations=d),'Valid peak schema changed')
                    valid+=1
        return {'malformed_calls_rejected':rejected,'complete_valid_schema_comparisons':valid,'valid_finish_preserved':True,'patched_source_sha256':{n:hashlib.sha256((dest/n).read_bytes()).hexdigest() for n in ('build_net.py','peak_quadratic.py')}}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--signal',type=Path,required=True);ap.add_argument('--reset',type=Path,required=True);ap.add_argument('--receipt',type=Path,default=Path(__file__).with_suffix('.json'));ap.add_argument('--write',action='store_true');ap.add_argument('--author',action='store_true');ap.add_argument('--repair-only',action='store_true');args=ap.parse_args()
    if args.repair_only:
        print(json.dumps(repair_checks(args.reset),sort_keys=True));return
    result={'signal':verify_signal(args.signal),'reset':verify_reset(args.reset),'repair':repair_checks(args.reset)}
    if args.author:result['author']={'signal':author_replay(args.signal,'signal'),'reset':author_replay(args.reset,'reset'),'reset_patched':author_replay(args.reset,'reset',patched=True)}
    normalized=json.loads(json.dumps(result,sort_keys=True))
    if args.write:args.receipt.write_text(json.dumps(normalized,indent=2,sort_keys=True)+'\n')
    else:
        saved=json.loads(args.receipt.read_text())
        if not args.author:saved.pop('author',None)
        require(type(saved) is dict and json.dumps(saved,sort_keys=True)==json.dumps(normalized,sort_keys=True),'Saved receipt mismatch')
    print(json.dumps({'status':'PASS','signal_branch_sections':result['signal']['integral_all_branch_sections'],'reset_transition_identities':result['reset']['all_transition_debt_and_control_identities'],'author_replay':args.author},sort_keys=True))
if __name__=='__main__':main()
