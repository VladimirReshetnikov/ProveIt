#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-static-node30-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'59c7b1d9831f7f4d1d1534d25e9b481323e4eba08c8345ba22493d1d6e59ae0e','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'c954d67fb255eb4c53de46ccebc68cad6923ca2ead8f5364968869afc73cbf43'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33StaticNode30';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='67a323664b3090f05212d9b2fe9842de4371bdd9dee8883e0cf9a9c088f09f2f' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Norm38ReferenceTerminals']
for x in ['[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(hg : NormAssignment38.gatesHold ι ports w)','NormAssignment38.assignment ports w 30','Norm38Reference.reference','Fin.castLE (by decide : 14 ≤ 38)','static_assignment_fixed ι ports w hg','ringRun_agrees_of_topological','Norm38Reference.graph_topological','Norm38Reference.initial_agreement ports w','Norm38Reference.reference_gate_equations_batched','(congrFun hfixed 30).trans (hrun 30 (by decide))']:assert x in s
old=(d/'research/nine-sharing-norm38-reference-terminals-check/src/DiophantineConsistency/Norm38ReferenceTerminals.lean').read_text();assert 'static_assignment_fixed ι ports w hg' in old and 'ringRun_agrees_of_topological' in old
run=(p/'run.py').read_text();assert "if mod in survey['selected']" in run and "need(guard(deps)==row['direct_guard']" in run
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional same-valuation node 30 topology; no Lean replay'},indent=2,sort_keys=True))
