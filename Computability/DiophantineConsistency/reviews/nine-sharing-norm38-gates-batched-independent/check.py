#!/usr/bin/env python3
"""Independently check gate/source bindings and prelaunch provider pins."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-gates-batched-draft';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(q/'generate.py')=='95c7cb090d549776693d9878236fa91ef7101fe28530f444a77f29923ba4ddfe' and sha(q/'source-manifest.json')=='16e050df729fa9fbb82c3811ef4c23460bf68814662006739c8ea105a3c0cc21' and sha(q/'run.py')=='8f9d4a21fea6003ef53187dd9331cf90c582c328df22b0586da0bcbe494f85e9'
source=D/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean';slots=D/'research/nine-sharing-norm38-slot-extraction-draft/slots.json';seed=D/'research/nine-sharing-quartic65-norm38-candidate/seed.json'
assert sha(source)=='c66694acbba431aa20f4be03a85c0210d24f1b3a51378e0bbeb40452b611817a' and sha(slots)=='f3b2a0ea47962596d8753533c363a6b3e0b4121cd3150722181581d9085326a4' and sha(seed)=='312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23'
gates=[(int(a),int(b),int(c),op) for a,b,c,op in re.findall(r'    ⟨(\d+), (\d+), (\d+), GateOp\.(add|sub|mul)⟩',source.read_text())];assert len(gates)==60 and [x[0] for x in gates]==list(range(21,81))
slotdata=json.loads(slots.read_text())['slots'];bygate={}
for e in slotdata:
 if e['kind']=='norm':continue
 m=re.fullmatch(r'(positive|negative)Residual ι GateOp\.(add|sub|mul) \(v (\d+)\) \(v (\d+)\) \(v (\d+)\)',e['rhs']);assert m
 kind,op,left,right,target=m.groups();target=int(target);assert (target,int(left),int(right),op) in gates and kind not in bygate.setdefault(target,{})
 bygate[target][kind]=e['slot']
assert len(bygate)==19 and sum(len(x) for x in bygate.values())==24
seeddata=json.loads(seed.read_text());assert len(seeddata['residuals'])==29
for t,items in bygate.items():
 assert 'positive' in items
 for kind,i in items.items():assert seeddata['residuals'][i]['kind']==kind
manifest=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(manifest)==13
names=[f'Norm38Gates{i:02d}' for i in range(12)]+['Norm38GatesAssembly'];assert [r['module'].split('.')[-1] for r in manifest]==names
basepath=Path('/tmp/nine-sharing-norm38-five-norms-check-v2-20261105');bs=D/'research/nine-sharing-norm38-five-norms-check-v2/attempt01/state.json';assert sha(bs)=='a16e6c80cd1f713b0ec2e863b800847a80265e86643f757ae146c1f1c9656140';base=json.loads(bs.read_text());assert base['status']=='PASS'
seen=set()
for row in manifest:
 n=row['module'].split('.')[-1];p=q/'src/DiophantineConsistency'/(n+'.lean');assert sha(p)==row['source_sha256'];imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',p.read_text(),re.M);assert imports==row['imports'];assert all(i in seen for i in imports if i in {x['module'] for x in manifest});seen.add(row['module']);assert str(basepath/'lib/DiophantineConsistency'/(n+'.olean')) not in base['overlay_links'] and all(x['module']!=n for x in base['rows'])
used=[]
for t,l,r,op in gates:
 text=(q/'src/DiophantineConsistency'/f'Norm38Gates{(t-21)//5:02d}.lean').read_text();body=re.search(r'^theorem gate'+str(t)+r'\b.*?(?=^/-- Proposed component|^end )',text,re.M|re.S).group()
 assert 'let v := NormAssignment38.assignment ports w' in body
 for kind in ('positive','negative'):assert f'{kind}Residual ι GateOp.{op} (v {l}) (v {r}) (v {t}) = 0' in body
 assert '(hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))' in body and '(hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w))' in body
 actual=list(map(int,re.findall(r'have h(\d\d) := each_slot_zero p w hz \d+',body)));assert set(actual)==set(bygate.get(t,{}).values());used.extend(actual)
 for kind,i in bygate.get(t,{}).items():assert f'rw [slot{i:02d} p ports w hp] at h{i:02d}' in body
 if not bygate.get(t):assert 'simp [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute, map_ofNat]' in body
 elif 'negative' not in bygate[t]:assert 'negativeResidual, pairCompute, map_ofNat]' in body
assert len(used)==24 and len(set(used))==24
assembly=(q/'src/DiophantineConsistency/Norm38GatesAssembly.lean').read_text();assert 'NormAssignment38.gatesHold ι ports w' in assembly
assert list(map(int,re.findall(r'gate(\d+) p ports w hp hz',assembly)))==list(range(21,81))
assert all('import DiophantineConsistency.Norm38Gates'+f'{i:02d}' in assembly for i in range(12))
independent=D/'reviews/nine-sharing-norm38-model-bridge-draft-independent';r=subprocess.run([sys.executable,'-I','-S','-B',str(independent/'check.py')],capture_output=True);assert r.returncode==0 and not r.stderr and r.stdout==(independent/'result.json').read_bytes()
print(json.dumps({'status':'PASS_GATE_SOURCE_RUNNER_REVIEW_ONLY','gates':len(gates),'materialized_gates':len(bygate),'component_slots':len(used),'computed_gates':60-len(bygate),'stages':len(manifest),'runner_sha256':sha(q/'run.py'),'manifest_sha256':sha(q/'source-manifest.json'),'scope':'Independent source/indices and provider-point review; no Lean compile, complete ancestry or graph/source theorem.'},indent=2,sort_keys=True))
