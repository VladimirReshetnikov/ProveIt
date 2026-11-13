#!/usr/bin/env python3
"""Independent source mapping and pinned-provider prelaunch review; no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-forward-gates-draft';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for n,h in [('generate.py','6123734528f03997597694249b9eb9c65b026c9496f9234b810d442e173ee272'),('source-manifest.json','d082f8c60a49753e20990045d41e2809487c8c27983eb0d06c410af261086e21'),('run.py','5ce2337f6624bcd03295116c28beffe4c59a0d596ad7c0c9a55b8d89477bee89')]:assert sha(q/n)==h
assign=D/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean';forward=D/'research/nine-sharing-forward38-draft/ForwardWitness38.lean';assert sha(assign)=='c66694acbba431aa20f4be03a85c0210d24f1b3a51378e0bbeb40452b611817a' and sha(forward)=='559de61d5eeeb17ef2f6c449f4d594e242ab1c784ce4b34ba58753898209ad14'
gates=[(int(a),int(b),int(c),op) for a,b,c,op in re.findall(r'    ⟨(\d+), (\d+), (\d+), GateOp\.(add|sub|mul)⟩',assign.read_text())];assert len(gates)==60 and [x[0] for x in gates]==list(range(21,81))
manifest=json.loads((q/'source-manifest.json').read_text())['rows'];names=[f'Norm38ForwardGates{i:02d}' for i in range(12)]+['Norm38ForwardGatesAssembly'];assert len(manifest)==13 and [r['module'].split('.')[-1] for r in manifest]==names
base=D/'research/nine-sharing-norm38-gates-assembly-retry/attempt01/state.json';assert sha(base)=='1ca0968a7e2acfbd398302581e30f3c02caebcf2a4c81081ba73e0b913ea8b72';s=json.loads(base.read_text());assert s['status']=='PASS';seen=set();lib=Path('/tmp/nine-sharing-norm38-gates-assembly-retry-20261105/lib/DiophantineConsistency')
for row in manifest:
 n=row['module'].split('.')[-1];p=q/'src/DiophantineConsistency'/(n+'.lean');assert sha(p)==row['source_sha256'];imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',p.read_text(),re.M);assert imports==row['imports'];assert all(i in seen for i in imports if i in {x['module'] for x in manifest});seen.add(row['module']);assert str(lib/(n+'.olean')) not in s['overlay_links'] and all(x['module']!=n for x in s['rows'])
for t,l,r,op in gates:
 text=(q/'src/DiophantineConsistency'/f'Norm38ForwardGates{(t-21)//5:02d}.lean').read_text();body=re.search(r'^theorem forwardGate'+str(t)+r'\b.*?(?=^/-- Proposed natural-constructor|^end )',text,re.M|re.S).group()
 assert '(embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S)' in body and 'NormAssignment38.assignment ports (SharingForward38.witnessCoordinates ports u)' in body
 for kind in ('positive','negative'):assert f'{kind}Residual embed GateOp.{op} (v {l}) (v {r}) (v {t}) = 0' in body
 assert 'InternalZero' not in body and 'map_ofNat' in body
assembly=(q/'src/DiophantineConsistency/Norm38ForwardGatesAssembly.lean').read_text();assert 'NormAssignment38.gatesHold embed ports (SharingForward38.witnessCoordinates ports u)' in assembly
assert list(map(int,re.findall(r'forwardGate(\d+) embed ports u',assembly)))==list(range(21,81)) and 'forwardGate80 embed ports u, by simp⟩' in assembly
for dirname in ('nine-sharing-forward38-draft-independent','nine-sharing-norm38-model-bridge-draft-independent'):
 p=D/'reviews'/dirname;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True);assert r.returncode==0 and not r.stderr and r.stdout==(p/'result.json').read_bytes()
print(json.dumps({'status':'PASS_FORWARD_GATE_SOURCE_REVIEW_ONLY','gates':len(gates),'stages':len(manifest),'runner_sha256':sha(q/'run.py'),'manifest_sha256':sha(q/'source-manifest.json'),'scope':'Source gate mapping, prior symbolic checks and provider-point preflight; no Lean compile or source-norm bridge.'},indent=2,sort_keys=True))
