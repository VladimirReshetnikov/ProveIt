#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-strong-retry01';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'9036a951587b6ab7f353e96f4292f0c9e74b2adb3bb4603d625a50f10572dbb6','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'fe74898310b13baf9837b60be3b2793bd2ffbbcf1eb0dc6b3c90505bbf0d9169'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33ForwardNormStrong38','81d87dfe099c67f1977994ff3aef6ff7e98e90e0b340d89d34c83ba08cfec7c2',['Norm38ReferenceTerminals','Norm38ReferenceFieldsAll','Norm38ForwardGatesAssembly','Norm38ForwardPrefix'],'strong_terminal'),('Sign33ForwardNormStrong','ce4b07edd66e1ef9c9545513f25b7d8753908f987d7909aeb5f8bb8c326fdede',['Sign33ForwardNormStrong38','SharingForward33'],'norm_strong_of_core')];assert len(rows)==2
for row,(n,h,imports,t) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports] and re.findall(r'^theorem (\w+)',s,re.M)==[t] and s.count('#print axioms ')==1
a=(p/'src/DiophantineConsistency/Sign33ForwardNormStrong38.lean').read_text();b=(p/'src/DiophantineConsistency/Sign33ForwardNormStrong.lean').read_text()
for x in ['Carrier65.strong d = 1','witnessCoordinates ports u) 80','witnessCoordinates ports u) 36','forward_gatesHold ι ports u','static_terminals_agree','reference_terminal_fields_combined','Carrier65.strong_scale','rw [hscale,hs,mul_one]','htz.trans (hcz.trans (hz.trans (hcd.symm.trans htd.symm)))']:assert x in a
for x in ['Carrier65.strong d = 1','ι (v 22)*ι (v 28)-ι (v 32) = ι (v 22)','strong_terminal ports u hs','witnessCoordinates ports u 21','witnessCoordinates ports u 29','witnessCoordinates ports u 35']:assert x in b
fields=(d/'research/nine-sharing-norm38-reference-fields-combine-check/src/DiophantineConsistency/Norm38ReferenceFieldsAll.lean').read_text();term=(d/'research/nine-sharing-norm38-reference-terminals-check/src/DiophantineConsistency/Norm38ReferenceTerminals.lean').read_text();assert 'reference p x 80 = d.Z ∧ reference p x 36 = d.delta' in fields and 'pairValue ι (v 80)=ref 80 ∧ pairValue ι (v 36)=ref 36' in term
nodes=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for x in ['let a36 : SignedPair S := ⟨w 21, 0⟩','let a67 : SignedPair S := ⟨w 29, 0⟩','let a73 : SignedPair S := ⟨w 35, 0⟩','let a79 : SignedPair S := pairCompute GateOp.mul a36 a67','let a80 : SignedPair S := pairCompute GateOp.sub a79 a73']:assert x in nodes
f=(d/'research/nine-sharing-sign33-forward-constructor-check/src/DiophantineConsistency/SharingForward33.lean').read_text();part=f.split('def witnessCoordinates',1)[1].split('theorem witness_inputs',1)[0];vec=[x.strip() for x in re.search(r'!\[(.*?)\]',part,re.S).group(1).split(',')];assert (vec[21],vec[27],vec[31])==('w 21','w 29','w 35')
c=(d/'Lean/DiophantineConsistency/Carrier65.lean').read_text();assert '(core p v).Z = (core p v).delta * strong (core p v)' in c

old=d/'research/nine-sharing-sign33-forward-norm-strong-check'
old_a=(old/'src/DiophantineConsistency/Sign33ForwardNormStrong38.lean').read_text();old_b=(old/'src/DiophantineConsistency/Sign33ForwardNormStrong.lean').read_text()
assert old_a==a and old_b.split(':= by',1)[0]==b.split(':= by',1)[0]
for x in ['(21 : Fin 33).succ = (22 : Fin 34)','(27 : Fin 33).succ = (28 : Fin 34)','(31 : Fin 33).succ = (32 : Fin 34)','rw [h22, h28, h32]']:assert x in b
assert b.count('Fin.cons_succ')==3
old_run=(old/'run.py').read_text().replace('nine-sharing-sign33-forward-norm-strong-check-20261106','nine-sharing-sign33-forward-norm-strong-retry01-20261106').replace('dfbc7deecd70d75148e291a6278d5494dcd43507ef8f3fe7b8bfc2230492a72d','fe74898310b13baf9837b60be3b2793bd2ffbbcf1eb0dc6b3c90505bbf0d9169')
assert old_run==(p/'run.py').read_text()
assert sha(old/'attempt01/state.json')=='70c9dc5e1c2555579ad2f6a9e3518eed4d3e3154540fe777a4492496cea6c337' and 'maximum recursion depth has been reached' in (old/'attempt01/Sign33ForwardNormStrong-compile.txt').read_text()

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional strong core norm to constructor cut; no Lean replay'},indent=2,sort_keys=True))
