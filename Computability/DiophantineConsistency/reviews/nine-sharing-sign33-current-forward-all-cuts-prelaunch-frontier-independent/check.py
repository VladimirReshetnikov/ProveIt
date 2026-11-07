#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-forward-all-cuts-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'82e57789c794ab97dad0ae97d51a484523d643f5ddddcef07ca4c6859dfdfdc6','provider_survey.py':'b36f581823250b18a9bf1d93944c3947849a745b84d3dcf38a39e827055a54c1','source-manifest.json':'ff3534cfc4825f3fe149332832266cee4955dba1efd10b1c5b3223ceeb8d0b6f'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33CurrentForwardAllCuts';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='d8442a76e62ff2f2e2b8f806577d5b9f01a976da155971d27772c717ad5700c7' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+x for x in ['Sign33ForwardAllCuts','Sign33CurrentCoreCuts','Sign33CurrentNaturalCoreNorms']]
for x in ['(hp : ∀ j, ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (ports j))','InternalZero ObjectCurrentEquation2011.naturalExpression u','∃ gap tau inner value negative : V','five_core_representatives_of_current_zero u hz','natural_source_core_norms u hz','(hp j).symm','Sign33ForwardAllCuts.all_cuts_of_core ports u gap tau inner value negative','rw [hports]; exact hgap','rw [hports]; exact htau','rw [hports]; exact hinner','rw [hports]; exact hvalue','rw [hports]; exact hnegative','rw [hports2]; exact hnorms']:assert x in s
for file in ['research/nine-sharing-norm38-fixed-port-norms/src/DiophantineConsistency/Norm38FixedPortNorms.lean','research/thirteen-current2011-carrier-model-prelude-diagnostic/ModelThirteenCarrierPrelude.lean']:
 assert 'abbrev ringPorts : Fin 4 → DiffRing V := fun j => ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V)' in (d/file).read_text()
survey=(p/'provider_survey.py').read_text()
for h in ['9df2673dfbe6180174f1768b1fafea8b2b8400e6f509ba2ab648947854b7f0f9','f0d666474d850def450411c2007eb2d8d57329709b5450aee08a501004fef086']:assert h in survey
run=(p/'run.py').read_text();assert "if mod in survey['selected']" in run and "need(guard(deps)==row['direct_guard']" in run
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'current natural zero and explicit port casts to existential AllCuts; no Lean replay'},indent=2,sort_keys=True))
