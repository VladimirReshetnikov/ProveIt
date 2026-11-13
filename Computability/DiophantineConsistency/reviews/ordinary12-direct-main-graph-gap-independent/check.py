#!/usr/bin/env python3
"""Read-only review of the direct graph's positive-witness gap theorem."""
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys

if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
D = Path(__file__).resolve().parents[2]
P = D / 'research/ordinary12-direct-main-probe'
B = D / 'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'

def need(x, msg):
    if not x: raise SystemExit(msg)
def sha(path):
    return sha256(Path(path).read_bytes()).hexdigest()

pins = {
    P/'GAP.md':'ef71e58b60960ccdf17e08698b3f4959808e47d129b362daee40d51699057f40',
    P/'DirectMainGap.lean':'572fe23b01dcfc4205ca105a7816bdeec572b57f9c97a8800847df376bd0729a',
    P/'run-gap.py':'bb5bdc15d837c33f50ea40f320bad670e3bbc7c93c220a6ea5a41e4cb67def0f',
    B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f',
}
receipt_pins = {
 'comparison-attempt01':'45f0c78941872748fd8ae3afe869673dcdcc10846776e6150755bc8f0598d6bf',
 'gapbalance-attempt03':'e8d204fd2f7f5a25ab9a457c2260a439775af114e44a3da0b61149c387f98b0c',
 'growthalgebra-attempt02':'2d209e2a348c48a57d32857393aaf2155cf2dbfe4959a1a5f408bee4c33c48b1',
 'pellgrowth-attempt01':'bac0a639d8099dd4eee2ea68c2b1d5e7a6da9b363de271195cd474c3412b43c4',
 'window-attempt02':'35da03939095fb4289c1a1c1bed5cdaf0d36eb452590f5c3693f4a92277cb461',
 'early-attempt01':'0507db7193667baf529fc62bf1f80063530296516e668f61e68670e0b305d357',
 'rank-attempt01':'b9f38de8fdd47de67be0bab98728ce434be51865ecb645bce326caf73a438148',
 'indices-attempt03':'d03cf9f90629a488bc08fff66d75eed0165d0a79d444192f790d0a0491bd0ad6',
 'oriented-attempt02':'03b3137c0763f25f59edcb375c7f01f795c1ad9f35ac8512dfd8c4e6156b308e',
 'pell-attempt01':'58b40dd17a5f18c81c018442afeebc9aa3d2f673d77953cecaee5987aaa23b33',
 'norm-attempt01':'e6303bca05e8304068a8efda87c9ec2ab763bc558a1476158faeb5267aabaf12',
 'attempt01':'2bf0934017209ddb4fab587740a9e680e80ce0f878f490856f5928e9fb66c81e',
 'main-attempt01':'49a283a031049f02befb5ac76745b35fbb39b5c61a02544014c414526d829e56',
 'transport-attempt02':'7b59b6fce70f490c9fc698117210371cc1e8551f30f065c1e48ab91c847678f7',
 'quotient-attempt01':'252b400e069deef01bdd7bcabd647606493817c90c9f376752fb92cb873fc5d4',
 'first-attempt03':'9896d230d5f06bf64c090567ed380b387d55f7f472430cd2a0a5b0d66c886264',
 'graph-attempt01':'6b1d05e8b34b8f5f701ad424b897bb996a9b2e519d08bd451ff1935b0e8e2c68',
 'gap-attempt01':'be826a9875f67196fd9beb7d7f8c7e0598cb3c2cc49c1d66a9f1b626452d7af2',
 'gap-attempt02':'49eb8ec66b51700455705f57eb51cf201e353ad00ca805c8aa47264e8509212a',
}
for name, digest in receipt_pins.items(): pins[P/'observations'/name/'terminal.json'] = digest

def verify_pins():
    for path, digest in pins.items(): need(sha(path) == digest, 'input mismatch: ' + str(path))
verify_pins()
source = (P/'DirectMainGap.lean').read_text()
for fragment in (
 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]',
 'theorem graph_gap (p : Fin 4 → ℕ) (v : Fin 12 → V)',
 '(hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))',
 '(hv : ∀j,0<v j) (hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v)',
 'v 5<v 11 := by',
 'DirectMainComparison.comparison p v hb hl hh hv hz',
 'DirectMainPellGrowth.square_bound Q n k hQ hn3 hny',
 'DirectMainGrowthAlgebra.growth_of_square_bound X Y (v 5) k (v 8) hX1 hY hwX hk',
 'DirectMainIndices.graph_indices p v hb hv hz',
 'exact x_gt a m\'',
 'DirectMainGapBalance.gap_of_balance U X a c H (v 11) R k main\' (v 5)',
 'hU hRk hbalance hmainbound hgrowth',
): need(fragment in source, 'missing statement or proof step: ' + fragment)
need('set_option linter.' not in source, 'unexpected local lint suppression')
growth=(P/'DirectMainGrowthAlgebra.lean').read_text()
pellgrowth=(P/'DirectMainPellGrowth.lean').read_text()
for fragment in ('(hX : 1≤X) (hY : 8≤Y) (hw : w≤X)',
                 '(hk : (X*Y*Y)*(X*Y*Y)≤k)',
                 'X+(3+4*(X*Y+Y))*w < eta+Y*k'):
    need(fragment in growth, 'growth lemma mismatch: '+fragment)
for fragment in ('theorem square_bound (Q n k : V) (hQ : 0<Q) (hn : 3≤n)',
                 '(hk : 2*ycoord n (2*(Q-1)+1)=k) : Q*Q≤k'):
    need(fragment in pellgrowth, 'Pell growth lemma mismatch: '+fragment)

old = json.loads((P/'observations/gap-attempt01/terminal.json').read_text())
ok = json.loads((P/'observations/gap-attempt02/terminal.json').read_text())
for attempt, receipt in [('gap-attempt01',old),('gap-attempt02',ok)]:
    folder=P/'observations'/attempt
    need(receipt['reason'] is None and receipt['union_count']==1291 and receipt['union_unchanged'], 'gap receipt guard')
    need(sha(folder/'source.txt') == receipt['source_sha256'] == receipt['source_after'], 'gap source mismatch')
    need(sha(P/'run-gap.py') == receipt['runner_sha256'] == receipt['runner_after'], 'gap runner mismatch')
    need(sha(receipt['command'][0]) == receipt['lean_sha256'] == receipt['lean_after'], 'Lean binary mismatch')
    need(sha(folder/'stdout') == receipt['stdout_sha256'] and sha(folder/'stderr') == receipt['stderr_sha256'], 'gap logs mismatch')
    need(not (folder/'stderr').read_bytes(), 'unexpected gap stderr')
    need(receipt['base_receipt_sha256'] == sha(B), 'base receipt mismatch')
need(old['exit']!=0 and 'error:' in (P/'observations/gap-attempt01/stdout').read_text() and
     'sorryAx' in (P/'observations/gap-attempt01/stdout').read_text(), 'failed attempt not preserved')
expected="'DirectMainGap.graph_gap' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
need(ok['exit']==0 and (P/'observations/gap-attempt02/stdout').read_text()==expected and
     ok['source_sha256']==sha(P/'DirectMainGap.lean'), 'accepted output mismatch')
out=Path(ok['output_root'])/'DirectMainGap.olean'
need(sha(out)==ok['object_sha256']=='29c88e1946a3939de1ea8b4745594f77000a806a6a3bad4930056ac485649409','gap object mismatch')

# All added producer objects must be the first matching paths in the accepted
# LEAN_PATH, and must agree with the producer's own source/receipt. This is
# point-in-time path resolution, not a complete serialized-import audit.
producers=[
 ('comparison','DirectMainComparison','comparison-attempt01'),
 ('gapbalance','DirectMainGapBalance','gapbalance-attempt03'),
 ('growth','DirectMainGrowthAlgebra','growthalgebra-attempt02'),
 ('pellgrowth','DirectMainPellGrowth','pellgrowth-attempt01'),
 ('window','DirectMainWindow','window-attempt02'),('early','DirectMainEarly','early-attempt01'),
 ('rank','DirectMainRank','rank-attempt01'),('indices','DirectMainIndices','indices-attempt03'),
 ('oriented','DirectMainOriented','oriented-attempt02'),('pell','DirectMainPell','pell-attempt01'),
 ('norm','DirectMainNorm','norm-attempt01'),('projection','DirectMainProjection','attempt01'),
 ('main','DirectMainMain','main-attempt01'),('transport','DirectMainTransport','transport-attempt02'),
 ('quotient','DirectMainFirstQuotient','quotient-attempt01'),('first','DirectMainFirst','first-attempt03'),
 ('graph','DirectMainGraph','graph-attempt01'),
]
paths=[Path(x) for x in ok['lean_path'].split(':')]
def find_first(module):
    found = [root/(module+'.olean') for root in paths if (root/(module+'.olean')).is_file()]
    need(bool(found), 'missing producer: '+module)
    return found[0]
for key,module,attempt in producers:
    folder=P/'observations'/attempt
    receipt=json.loads((folder/'terminal.json').read_text())
    path=find_first(module)
    need(receipt['exit']==0 and receipt['reason'] is None and receipt['union_unchanged'] and
         receipt['object_sha256']==ok[key+'_producer_sha256']==sha(path), 'producer object mismatch: '+module)
    need(sha(folder/'source.txt')==receipt['source_sha256']==receipt['source_after']==sha(P/(module+'.lean')),
         'producer source mismatch: '+module)
    need(sha(folder/'stdout')==receipt['stdout_sha256'] and sha(folder/'stderr')==receipt['stderr_sha256'],
         'producer log mismatch: '+module)
xq=find_first('XQ91')
need(sha(xq)==ok['xq91_producer_sha256']=='747df97728f8c8125c205a752a6a2cbe205ce243cf2612ac57614025050be17d', 'XQ91 mismatch')
base=json.loads(B.read_text());lib=paths[-2]
def verify_union():
    actual={x.relative_to(lib).as_posix():x for x in lib.rglob('*') if x.is_file()}
    need(len(actual)==1291 and set(actual)==set(base['union']), 'union membership mismatch')
    for name,path in actual.items():
        rec=base['union'][name]
        need(path.is_symlink() and os.readlink(path)==rec['link'] and
             str(path.resolve(strict=True))==rec['resolved'] and sha(path)==rec['sha256'], 'union mismatch: '+name)
verify_union()
for review in ('ordinary12-direct-main-comparison-independent','ordinary12-direct-main-gap-independent'):
    proc=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews'/review/'check.py')],capture_output=True,timeout=120)
    need(proc.returncode==0 and not proc.stderr and json.loads(proc.stdout)['status']=='PASS','prior review failed: '+review)
verify_union();verify_pins()
need(sha(out)==ok['object_sha256'], 'gap output changed')
print(json.dumps({'status':'PASS','assumptions':['beta positive','MC<beta','MF<2*beta','all witnesses positive','draft zero'],
                  'conclusion':'w<G in every IΣ₁ model', 'producer_objects':len(producers)+1,
                  'selected_union_objects':1291,'failed_attempt_preserved':True,
                  'preexisting_lean_processes':len(ok['preflight']['lean']),
                  'maximum_sampled_lean_processes':max(len(x['lean']) for x in ok['samples']),
                  'scope':'model theorem; no machine-halt or iPRA derivation'}, indent=2))
