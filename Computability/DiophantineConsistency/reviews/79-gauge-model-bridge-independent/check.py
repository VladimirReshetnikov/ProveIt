from pathlib import Path
from hashlib import sha256
import json,re
root=Path('research/ten-positive-79-gauge-model-bridge');o=root/'observations/attempt02'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='ea42078bc3a5473b5cf3b48fc10ff307db522d5c7556d224fe85bebb02858384';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run-v2.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='dedc9afdec2c751cada167b722f89bed102da9efde0bc05541b4aba5d224ce88'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().strip()=="'Mask79ModelBridge.zero_preserved_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound]" and not (o/'stderr').read_text()
code=(root/'Mask79ModelBridgeV2.lean').read_text();imports=re.findall(r'^import\s+(\S+)',code,re.M);assert imports==['Mask79ActualOutput','DiophantineConsistency.ModelDifferenceRing','Foundation.FirstOrder.Arithmetic.IOpen.Basic']
paths=['/tmp/mask79-output-cqfif459','/tmp/mask79-actual-f441d356','/tmp/mask79-ring-92upnp8s','/tmp/mask79-carrier-w290b5ah','/tmp/tenpositive-80graph-d2v79zbc','/tmp/direct90-ipra-join-b66u_qqo/lib','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']
for n in imports:
 rel=n.replace('.','/')+'.olean';p=next((Path(x)/rel for x in paths if (Path(x)/rel).is_file()),None);assert p and str(p) in r['pins'];print(n,str(p),sha(p))
assert 'move vv s t = fun j => ι (w j)' in code and '(hz : InternalZero (output79 (integerPorts p)) v)' in code and 'InternalZero (output79 (integerPorts p)) w := by' in code
assert 'rw [← hcast, output_move]' in code and 'apply (internalZero_iff _ _).mpr' in code and '(internalZero_iff _ _).mp hz' in code and not re.search(r'\b(sorry|admit)\b',code)
a=root/'observations/attempt01';f=json.loads((a/'terminal.json').read_text());assert f['status']=='FAILED' and sha(a/'stdout')==f['stdout_sha256'] and 'error' in (a/'stdout').read_text()
print('PASS: same lifted tuple and explicit move equality, source/target InternalZero, three direct first-selected pinned providers, accepted and failed receipts rechecked; no witness/positivity existence.')
