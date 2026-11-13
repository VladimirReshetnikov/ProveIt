#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-ipra-bridge-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='bcb4d93dbf9c62ab5b45c25bf05d4d864e1c0f1b04faa62bfdf0c59c63141cdc' and sha(p/'source-manifest.json')=='09ae04254157b92b0ac0e167cb8d9be6b6ced14e528c2e2c65acfe233f23bbcb'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74IPRABridge';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();imports=['DiophantineConsistency.Sign14Positive74Model','DiophantineConsistency.GenericPolynomialBridgeTransport','DiophantineConsistency.Sign14Optimized86Bridge'];assert e['module']=='DiophantineConsistency.'+n and e['imports']==imports and sha(q)==sha(repo/e['source'])==e['source_sha256']=='a70a1b608b72b704f356a576c99005161235f36a51767c6ee2813ed8d33b4b9c' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==imports and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('HAExpressionAssembly.PolynomialBridge','positiveShift (Sign14Positive74.expression CurrentWindowCarry2011.ports)','GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign14Optimized86IPRA.polynomialBridge','Sign14Positive74Model.zero_exists_iff (V := V) CurrentWindowCarry2011.ports'):assert z in s
t=(root/'research/nine-sharing-generic-polynomial-bridge-transport-check/src/DiophantineConsistency/GenericPolynomialBridgeTransport.lean').read_text();assert '(∃ w : Fin m → V, InternalZero e w) ↔ ∃ w : Fin n → V, InternalZero f w' in t and '(hb : HAExpressionAssembly.PolynomialBridge f) : HAExpressionAssembly.PolynomialBridge e' in t
for f in ('nine-sharing-sign14-positive74-model-terminal-independent','nine-sharing-sign14-86gate-bridge-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider-survey.py')],capture_output=True,text=True,check=True,timeout=180);sv=json.loads(x.stdout);assert sv['status']=='PASS' and sv['overlap_count']==1125 and len(sv['extra'])==639
old=json.loads((root/'research/nine-sharing-sign14-86gate-bridge-check/attempt01/state.json').read_text());base=Path('/tmp/nine-sharing-sign14-positive74-model-check-20261110/lib')
for mod,d in old['rows'][0]['dependencies'].items():
 if mod=='Init':continue
 rel=mod.replace('.','/')+'.olean';target=base/rel
 if target.is_file():assert str(target.resolve())==d['realpath'] and sha(target)==d['sha256']
 else:assert sv['extra'][rel]=={'realpath':d['realpath'],'sha256':d['sha256']}
assert 'DiophantineConsistency/GenericPolynomialBridgeTransport.olean' in sv['extra'] and sv['object_sha256']==old['rows'][0]['object_sha256']
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','overlap':1125,'extra':639,'scope':'proposed shifted Positive74 polynomial bridge, explicit positive-witness and external file separate'},indent=2))
