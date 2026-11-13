#!/usr/bin/env python3
"""Identify trace75 bounded rank with its recovered main index."""
from pathlib import Path
from hashlib import sha256
import json, os, re, shutil, subprocess, sys, tempfile, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H = Path(__file__).resolve().parent
D = H.parents[1]
SRC = H / 'Trace75GraphUnweighted.lean'
GRAPHPOWER = Path('/tmp/trace75-graphpower-2136o7kc/Trace75GraphPower.olean')
UNWEIGHTED = Path('/tmp/absorb89-chain-ctjv042u/lib/Direct80UnweightedProjection.olean')
HEIGHT = Path('/tmp/trace75-variableheight-unjxjs_5/Trace75VariableHeight.olean')
GRAPHPROD = Path('/tmp/trace75-graphproduct-a_f7xzko/Trace75GraphProduct.olean')
PRODPOWER = Path('/tmp/trace75-productpower-q28seu81/Trace75ProductPower.olean')
PRODHEIGHT = Path('/tmp/trace75-productheight-dj1cseev/Trace75ProductHeight.olean')
VARIABLE = Path('/tmp/pell-variable-generic-7r3_ts9x/PellVariableGrowth.olean')
PROJ = Path('/tmp/trace75-projection-g5m1hwzf/Trace75Projection.olean')
PRODUCT = Path('/tmp/absorb89-chain-gbvs3lwh/lib/Direct80ProjectionProduct.olean')
ALIGNMENT = Path('/tmp/trace75-indexalignment-w8cm68g2/Trace75IndexAlignment.olean')
GROWTH = Path('/tmp/absorb89-chain-8h1sfgle/lib/Direct80ScaledGrowthMinus.olean')
FIRSTRES = Path('/tmp/trace75-firstresidue-9thrt5_j/Trace75FirstResidue.olean')
EXACT = Path('/tmp/trace75-rankexact-fk1_orgc/Trace75RankExact.olean')
CONGRUENCE = Path('/tmp/trace75-offsetcongruence-_fmdaxmm/Trace75OffsetCongruence.olean')
PELL = Path('/tmp/trace75-pell-79kzmzfi/Trace75Pell.olean')
OFFDIV = Path('/tmp/trace75-offsetdiv-m1wthwir/Trace75OffsetDiv.olean')
RINDEX = Path('/tmp/trace75-rankindex-g00v7ao8/Trace75RankIndex.olean')
MAININDEX = Path('/tmp/trace75-mainindex-6jrdblag/Trace75MainIndex.olean')
REDUCTION = Path('/tmp/pell-rank-generic-_nzvtqaf/PellRankReduction.olean')
RANK = Path('/tmp/trace75-rank-4hiva0nq/Trace75Rank.olean')
JOINED = Path('/tmp/trace75-joinedsquare-qur93i_u/Trace75JoinedSquare.olean')
SIGNED = Path('/tmp/trace75-signedrank-wtu23ycl/Trace75SignedRank.olean')
TRANSPORT = Path('/tmp/trace75-transport-iiurih17/Trace75Transport.olean')
CARRIER = Path('/tmp/trace75-carrierbound-dztlf9a0/Trace75CarrierBound.olean')
OFFGRAPH = Path('/tmp/trace75-offsetbound-6cyh823t/Trace75OffsetBound.olean')
KPOS = Path('/tmp/trace75-kpos-rq1vg901/Trace75Kpos.olean')
SIZE = Path('/tmp/trace75-size-ogywv9bg/Trace75Size.olean')
RESIDUE = Path('/tmp/trace75-residue-mpo1d0xl/Trace75Residue.olean')
OFFSET = Path('/tmp/generic-transport-ufzumibs/OffsetBound.olean')
TRANS = Path('/tmp/generic-transport-ufzumibs/CarrierTransport.olean')
ORDER = Path('/tmp/generic-transport-ufzumibs/TransportOrder.olean')
FACTORS = Path('/tmp/trace75-factors-4hp2mk1k/Trace75Factors.olean')
ADJ = Path('/tmp/tenpositive-adjacent-integer-uhhde7iz/AdjacentInteger.olean')
NONZERO = Path('/tmp/trace75-nonzero-8vawxqqm/Trace75RootNonzero.olean')
ROOTOBJ = Path('/tmp/trace75-root-wxe5rr8_/Trace75Root.olean')
MASK = Path('/tmp/tenpositive-product-root-kdq8sqms/ProductRoot.olean')
DOUBLE = Path('/tmp/tenpositive-doubling-z_t6ngdp/TenPositiveDoubling.olean')
SCALED = Path('/tmp/tenpositive-scaledsquare-rat00ki8/ScaledSquare.olean')
LIB = Path('/tmp/direct90-ipra-join-b66u_qqo/lib')
MODEL = LIB/'DiophantineConsistency/ModelDifferenceRing.olean'
PROVIDER = Path('/tmp/trace75-provider-wljjm6ws/DiophantineConsistency/TenPositiveTrace75.olean')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
pins = {
    Path('/tmp/trace75-graphpower-2136o7kc/DiophantineConsistency/ModelRatioBounds.olean'): 'fcf4152e49cb9a989bd9f8ba08259a26c646dfca18370b0c6e1ce7ebfb33b8a7',
    Path('/tmp/trace75-variableheight-unjxjs_5/DiophantineConsistency/ModelRatioBounds.olean'): 'fcf4152e49cb9a989bd9f8ba08259a26c646dfca18370b0c6e1ce7ebfb33b8a7',
    SRC: '07a41db0b8cd67ec084c9409dac8f7d41dbfb4a7ad170063c65ba3123bb1b75b',
    GRAPHPOWER: '5704c79a5e8a267190a59ac245282eb119c7e3ea039d43cbc4b55dde1802d9a9',
    UNWEIGHTED: '50737fd41a2cb8f3c689b7dc5e8a554136e477baba84e85bafafa76f69c448fa',
    HEIGHT: 'fee9fe34286e4a3b9027e4218a773efa8d22856f5d49e02ce53cf85e59b46419',
    GRAPHPROD: '82aff3b3fa8a20751434ecf00942304837f966d4fc3b9e282379eed7b7b7abe4',
    PRODPOWER: '2999b26c4638f4d192f3a13784f1da2dd88e6c67f67b3ecbc3c21884dbeeb35e',
    PRODHEIGHT: '53fc07fe56761edc1a8769bb96c350c4e845e99f8914bc4ccd2d698ed7944b49',
    VARIABLE: '4f082f68b44ec02452f69a012f104ce82debbc46806f9fd83e2d5ad70fdf59f8',
    PROJ: '8404795f081ea826e14cdb2bce21fa985977c760d1b0c08fe8e2148019ef9400',
    PRODUCT: '25b274e6e2e8d7770a2b33f8ce83f8a40c77f68b9cd98d19fb82c928a4643690',
    ALIGNMENT: 'b1ebde37ca118b5262b4c4b5c023feb9192622c40e42ee173169b4936caa7a49',
    GROWTH: '2eec905d0c1eff64395322328a3ee0e7ad30d08c169990e9b74e578affbc826e',
    FIRSTRES: '048623caba4e3c2b20d9e7640793bdf8d37274650a92f85034fbb5c5fe9728a6',
    EXACT: '26c9d2ab4e3a06a3f72906eb1a2b2604081324f1488fc1308f594ec3985436ee',
    LIB/'DiophantineConsistency/ArithmeticPellFirstIndex.olean': '20d3769d891a42810c1985203768b122bf936884494d2829415e3140d6deb9c2',
    CONGRUENCE: '68f62881983fd6457780b66ebe12e38ae8613e177cac4f5f987a59dfe94808d3',
    PELL: 'cea9dcd9cc72467aa28113a65178cb7763170960ef0a4b215153537fb77bfbb9',
    LIB/'DiophantineConsistency/ArithmeticPellCongruences.olean': 'ff395c82ca9ea770a64ec69e4b4b7f8e1e2d655d67db4831af39a2d8a78ae664',
    OFFDIV: '994ed10ffec11931a4231a88100ab14fdb45cc0acd1eb92715c9a7c56ea99cde',
    RINDEX: '9eeb3bbba40a1cb450220a8b64592c5ece3838d3f6093f6955d8c3e3f79cf248',
    MAININDEX: '9296c438f1fc9dbaec85b2e67db0e3088b0b852072cc2867621cbcfb2f60b55c',
    REDUCTION: '1cb551f5865a5c7a2ba6cdf762415181cef24a01dc5666a1ca9d5bd529f27325',
    RANK: '1cc63c96d4f6f59de021d41d8a2b2ac0db544235d6b43cef63be05c47259898b',
    JOINED: '09ab5f30401baa3f93c69db97a44b4c6f5c3fc0dbdd7b08770ba623af925d620',
    SIGNED: '7b0050d97800e27c67bed2912b68c5653861c8af2527c911701721bdcfbebe51',
    TRANSPORT: 'c660d042eaa9e9e525d7bb0d09ca03651f2ec9b702a93f5bbd48da0e3c5ade54',
    LIB/'DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.olean': 'b887dccdf37f4741abdd7bb80c2dd1efcaa57ee73db9674e82f5b118ffba9561',
    CARRIER: '8ef47fc9a296744657c3f3dfd7130aeab24058371533a995a247e045318af923',
    OFFGRAPH: 'ff61154c7dfec50724c92d55a95b3610d41bccb8c294b02b0a888ef4db11236b',
    KPOS: 'c9dcda78a63d32accfcd4efc52e19f8e69747cc704c26f5fbdbd29e2eb9aa7d6',
    Path('/tmp/tenpositive-80carrierestimate-nuzwvv82/Direct80CarrierEstimate.olean'): 'fcc445ea6f87910a045de2a0dc15489d945927ba1f618f5a7ce8ded167ed5399',
    Path('/tmp/tenpositive-80carriersizes-fx4pgnk0/CarrierSizes.olean'): '4f9cb91f6cbdfdc450be5a4dadc46c72d6b2b742c377d585efa430600a4d9fab',
    SIZE: '2a536f3a3eb2129213dd4b30df564cff717068221c8e7b9b5e864475c29cf058',
    Path('/tmp/trace75-adjacent-4nlbt6ev/Trace75Adjacent.olean'): 'f8b22b6107778dd98a51e6aa356d8190a0be377c811bceeff43dfcd1b19f17ea',
    Path('/tmp/trace75-index-ri6h6wbv/Trace75Index.olean'): '6cc75eb28726516d4901542f26f083ecceeb682d459ff4a71022f3d88b1a3a34',
    Path('/tmp/trace75-pell-79kzmzfi/Trace75Pell.olean'): 'cea9dcd9cc72467aa28113a65178cb7763170960ef0a4b215153537fb77bfbb9',
    Path('/tmp/trace75-fold-b2hmelpc/Trace75Fold.olean'): '60d26b62219b41539aecf950465beee7e90df5a50f78e14ac8670d47c2ef5263',
    Path('/tmp/trace75-joined-ketw_770/Trace75Joined.olean'): 'be92565d27f2893ed85e46c44d726a7a699d51ee9019105f932446831be7b305',
    RESIDUE: '205d69b70c084f2613a94f465f3b46fd59f142f755e34897dd4257b16c819e8d',
    OFFSET: '1702af9273f8d0211bc57a013b97fe58c7e58a0791bb4b217f1207c6a27923a4',
    TRANS: '05b15e987fa4eeb289936785ac2aaf7d4d2b0916fe29fd44ad9d52402c9da53d',
    ORDER: '6696792c784a1f6dc56e06076350015ca235a8973caf3ecda2a9328128056da2',
    LIB/'DiophantineConsistency/ArithmeticPellHalfIndex.olean': '6142ab8eaac6e281c3372817a6f1a8cbc14704717d4f5479c28603c754c3a4d7',
    FACTORS: '1bae9331cfbca4e35cb48916f135b63eedc8b5c827f8f24ae6f12b2dff111975',
    ADJ: '19321c96c92462072fc3fe6cf30212535baa29e7915e1e59ca2c26073873dc34',
    Path('/tmp/tenpositive-adjacent-complete-w9h57aeb/AdjacentComplete.olean'): 'e75ae912b24068b600e79d93eaef81e314146b7b50e0c4268c2f6db6fd0e650b',
    Path('/tmp/tenpositive-adjacent-step-r3dpq5z3/AdjacentStep.olean'): 'cf3fee46a9e362a5b474f1d983c25e7dc67cb65436b3c4f0625ecf1cf17710a7',
    Path('/tmp/tenpositive-adjacent-bounds-tceau5u7/AdjacentBounds.olean'): 'b6afea28cda32503292760953f1773b183089b151689af8f80d1d76a18da8101',
    Path('/tmp/tenpositive-adjacent-nk5miisb/AdjacentDenominator.olean'): '83c7300a38a6d5619d9802679be749fbe8088a1be0e34c3683aecd7965dc9ff9',
    Path('/tmp/tenpositive-adjacent-preserve-9uy_qhmf/AdjacentPreserve.olean'): 'bf2cef6fd83385d21a3553ca2a774273bf9b8febb0c6dedae2ef40c5e8e2e2e2',
    NONZERO: '35e467ec9e32fb7e0e0b02f917c576811341e89d4a593ccc8dcd8603a5474802',
    ROOTOBJ: 'bf8d56a7526a5324d04c7178d8265e619a15aa624d117d11ba8b864831624958',
    MASK: '92dbb47e969d3603f6f496f53c7995493a989293a37e5272c308ff79d3fb09d5',
    DOUBLE: '138dbf9563aab2a4b867547b8f2ee9650faec64b2f403c17b1598b11db66522f',
    SCALED: '37ce988b94587130947097a868dd153f5564718dd280fafe6fd3b75aa2028691',
    MODEL: 'd0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74',
    LIB/'DiophantineConsistency/ArithmeticGcdNormalization.olean': '254b88abe787829f8bfad61f9606a14318cb31186b593e0cb76821e4e1ad1242',
    PROVIDER: '1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c',
    LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    PACK / 'Mathlib/Tactic/Ring.olean': 'cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4',
    PACK / 'Mathlib/Tactic/LinearCombination.olean': 'e4487ef3e033c8a8cfe8562ee7a96d2926444bd73c7f138f265b58a8d1d14c08',
}
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def need(test, message):
    if not test: raise RuntimeError(message)
def resources():
    rows = subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],check=True,capture_output=True,text=True).stdout.splitlines()
    lean = [r.strip() for r in rows if len(r.split(None,3)) == 4 and r.split(None,3)[1] == 'lean']
    mem = int(next(r for r in Path('/proc/meminfo').read_text().splitlines() if r.startswith('MemAvailable:')).split()[1])
    return {'time_ns':time.time_ns(), 'lean':lean, 'mem_available_kib':mem}
attempt = os.environ.get('ATTEMPT','unweighted-attempt01')
need(re.fullmatch(r'unweighted-attempt[0-9]{2,}', attempt) is not None, 'attempt')
out = H / 'observations' / attempt
need(not out.exists(), 'observation exists')
for p, x in pins.items(): need(sha(p) == x, 'input drift: '+str(p))
pre = resources(); need(pre['mem_available_kib'] >= 8*1024**2 and len(pre['lean']) < 2, 'resource preflight')
out.mkdir(parents=True)
root = Path(tempfile.mkdtemp(prefix='trace75-unweighted-'))
overlay = root/'DiophantineConsistency'; overlay.mkdir()
for target in (LIB/'DiophantineConsistency').iterdir():
    (overlay/target.name).symlink_to(target, target_is_directory=target.is_dir())
(overlay/'TenPositiveTrace75.olean').symlink_to(PROVIDER)
src = root/'Trace75GraphUnweighted.lean'
shutil.copyfile(SRC, src); shutil.copyfile(SRC, out/'source.txt')
obj = root/'Trace75GraphUnweighted.olean'
cmd = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={root}', str(src), '-o', str(obj)]
env = {'PATH':'/usr/bin:/bin','LEAN_PATH':str(GRAPHPOWER.parent)+':'+str(UNWEIGHTED.parent)+':'+str(HEIGHT.parent)+':'+str(GRAPHPROD.parent)+':'+str(PRODPOWER.parent)+':'+str(PRODHEIGHT.parent)+':'+str(VARIABLE.parent)+':'+str(PROJ.parent)+':'+str(PRODUCT.parent)+':'+str(ALIGNMENT.parent)+':'+str(GROWTH.parent)+':'+str(FIRSTRES.parent)+':'+str(EXACT.parent)+':'+str(CONGRUENCE.parent)+':'+str(PELL.parent)+':'+str(OFFDIV.parent)+':'+str(RINDEX.parent)+':'+str(MAININDEX.parent)+':'+str(REDUCTION.parent)+':'+str(RANK.parent)+':'+str(JOINED.parent)+':'+str(SIGNED.parent)+':'+str(TRANSPORT.parent)+':'+str(CARRIER.parent)+':'+str(OFFGRAPH.parent)+':'+str(KPOS.parent)+':/tmp/tenpositive-80carrierestimate-nuzwvv82:/tmp/tenpositive-80carriersizes-fx4pgnk0:'+str(SIZE.parent)+':/tmp/trace75-adjacent-4nlbt6ev:/tmp/trace75-index-ri6h6wbv:/tmp/trace75-pell-79kzmzfi:/tmp/absorb89-chain-76k5jp49/lib:/tmp/trace75-fold-b2hmelpc:/tmp/trace75-joined-ketw_770:/tmp/pell-generic-fold-1n_2g52k:'+str(RESIDUE.parent)+':'+str(OFFSET.parent)+':'+str(TRANS.parent)+':'+str(ORDER.parent)+':'+str(FACTORS.parent)+':'+str(ADJ.parent)+':/tmp/tenpositive-adjacent-complete-w9h57aeb:/tmp/tenpositive-adjacent-step-r3dpq5z3:/tmp/tenpositive-adjacent-bounds-tceau5u7:/tmp/tenpositive-adjacent-nk5miisb:/tmp/tenpositive-adjacent-preserve-9uy_qhmf:'+str(NONZERO.parent)+':'+str(ROOTOBJ.parent)+':'+str(MASK.parent)+':'+str(DOUBLE.parent)+':'+str(SCALED.parent)+':'+str(root)+':'+str(LIB)+':'+str(PACK),'LEAN_NUM_THREADS':'1'}
samples = []; reason = None; start = time.monotonic()
with (out/'stdout').open('x') as stdout, (out/'stderr').open('x') as stderr:
    proc = subprocess.Popen(cmd, env=env, stdout=stdout, stderr=stderr)
    while proc.poll() is None:
        sample = resources(); samples.append(sample)
        if sample['mem_available_kib'] < 8*1024**2 or len(sample['lean']) > 2:
            reason='resource guard'; proc.terminate(); break
        if time.monotonic()-start > 300:
            reason='timeout'; proc.terminate(); break
        time.sleep(2)
    try: proc.wait(timeout=10)
    except subprocess.TimeoutExpired: proc.kill(); proc.wait()
for p, x in pins.items(): need(sha(p) == x, 'input changed: '+str(p))
need(sha(src) == pins[SRC], 'copied source changed')
log = (out/'stdout').read_text() + (out/'stderr').read_text()
result = {'command':cmd, 'lean_path':env['LEAN_PATH'], 'exit':proc.returncode, 'reason':reason,
          'output_root':str(root), 'inputs':{str(p):x for p,x in pins.items()},
          'runner_sha256':sha(__file__), 'preflight':pre, 'samples':samples, 'postflight':resources(),
          'stdout_sha256':sha(out/'stdout'), 'stderr_sha256':sha(out/'stderr'),
          'object_sha256':sha(obj) if obj.is_file() else None,
          'scope':'conditional model root extraction; selected direct imports pinned; package/transitive ancestry and external graph binding inherited'}
(out/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'exit':proc.returncode, 'reason':reason, 'root':str(root), 'object_sha256':result['object_sha256']}))
need(proc.returncode == 0 and reason is None and obj.is_file() and not re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)',log), 'Lean check failed')
