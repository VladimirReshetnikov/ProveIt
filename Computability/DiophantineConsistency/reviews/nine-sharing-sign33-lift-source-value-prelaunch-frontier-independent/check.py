#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-lift-source-value-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'9600e678518aea6da7a557571238948fdc8b8e3af04f95cd8749fa8fbd0aa6a0','provider_survey.py':'41fdf0cbe7397f730ee0ede940fb78a247088a56b1df2082bd3e22208f2fd5da','source-manifest.json':'06edb69bb300e830d4dfbf4bcd6cad2a850be965b8b93ee06032974c0acfc299'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33LiftTerminals','f02d6ff58e6a497edff6f9d21790991a80c51067a5374226d4c81755720679e9',['Sign33RingTopology','Sign33RingGatesAssembly','Norm38ReferenceTerminals']),('Sign33LiftSourceValue','55b31f9f9fefccf9135209baae2cae6e6e5894f6dd48d6da600ea658900d2cac',['Sign33LiftTerminals','Sign33LiftFiveNorms','Norm38StaticCarrierConditional'])];assert len(rows)==2
for row,(n,h,imports) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==h==row['source_sha256'] and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports]
t=(p/'src/DiophantineConsistency/Sign33LiftTerminals.lean').read_text();v=(p/'src/DiophantineConsistency/Sign33LiftSourceValue.lean').read_text();assert 'Sign33ResidualAssembly.AllCuts ports v' in t and 'Sign33ResidualAssembly.AllCuts ports v' in v
assert 'Sign33RingTopology.static_agrees_of_topological' in t and '(Norm38Reference.initial_agreement ports (Sign33Lift38.lift v))' in t and '(Norm38Reference.reference_gate_equations_batched _ _)' in t and '(Sign33RingGatesAssembly.all_ring_gates ports v hc)' in t
assert re.findall(r'heq (\d+) \(by decide\)',t)==['61','44','78','66','80','36'];assert 'Sign33LiftTerminals.terminals ports v hc' in v and 'Sign33LiftFiveNorms.five_norms ports v hc' in v and 'Norm38Reference.static_terminals_norms_imply_value' in v and 'simpa only [Sign33Lift38.lift_inputs]' in v
assert 'Carrier65.value (fun j => ι (ports j))' in v and '(Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)) + 1' in v
lift=(d/'research/nine-sharing-sign33-lift38-check/src/DiophantineConsistency/Sign33Lift38.lean').read_text();assert 'lift v (Fin.castLE (by decide : 14 ≤ 38) i) = v (Fin.castLE (by decide : 15 ≤ 34) (Fin.succ i))' in lift
runner=(p/'run.py').read_text();survey=(p/'provider_survey.py').read_text();assert 'selected direct dependency' in runner and 'local producer binding' in runner
for n in ['Sign33RingTopology','Sign33RingGatesAssembly','Norm38ReferenceTerminals','Sign33LiftFiveNorms','Norm38StaticCarrierConditional']:assert "'"+n+"'" in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'AllCuts to Carrier65 ring-value source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
