#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates-assembly-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'7902f4b70ae999d9999c981cd7a2d048d57b536c153ed43661ec93492f23b576','provider_survey.py':'201cfdb348249feba878ddd9422d39eaf3307bee4b7a9c0093e1e8d4353d9912','source-manifest.json':'6679af42190b2b50dcf67563ad6cb86627656419ebf1131cb3f7fe85e187f9a1','src/DiophantineConsistency/Sign33RingGatesAssembly.lean':'b56a55e1e9759f0b0e2bf1f0119d5a272b54bfb2a35fb0a1761e5d391fe115c6'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33RingGatesAssembly.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='b56a55e1e9759f0b0e2bf1f0119d5a272b54bfb2a35fb0a1761e5d391fe115c6';imports=['DiophantineConsistency.Sign33RingGates%02d'%i for i in range(12)];assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==imports
assert re.findall(r'^theorem (\w+)',s,re.M)==['all_ring_gates'] and 'Sign33ResidualAssembly.AllCuts ports v' in s and 'NormAssignment38.assignment ports (Sign33Lift38.lift v) i' in s
applications=re.findall(r'Sign33RingGates(\d\d)\.gate(\d+) ports v( hc)?',s);assert len(applications)==60 and [int(x[1]) for x in applications]==list(range(21,81))
graph=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text();assert [int(x) for x in re.findall(r'⟨(\d+), \d+, \d+, GateOp\.(?:add|sub|mul)⟩',graph)]==list(range(21,81))
for batch,target,hc in applications:
 source=(d/f'research/nine-sharing-sign33-ring-gates{batch}-check/src/DiophantineConsistency/Sign33RingGates{batch}.lean').read_text();m=re.search(r'theorem gate'+target+r'\b(.*?) := by',source,re.S);assert m and bool(hc)==('(hc : Sign33ResidualAssembly.AllCuts ports v)' in m.group(1));assert 'ports : Fin 4 → V' in m.group(1) and 'v : Fin 34 → V' in m.group(1)
runner=(p/'run.py').read_text();survey=(p/'provider_survey.py').read_text();assert "for mod in imports:" in runner and "expected=survey['selected'][mod]" in runner
for i in range(12):assert f"('ringgates{i:02d}'," in survey and f"'Sign33RingGates{i:02d}'" in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'60 individual gate applications and point-provider review; no Lean replay'},indent=2,sort_keys=True))
