#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-natural-core-norms-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'e6d76f3ffcf4feac85f420395e79c7dfa7c997122baf49e5f8a2035465b66c70','provider_survey.py':'25f625d2d1d374aea67ab006c4c97131c7f004f1cbd8028697361568e8d23d37','source-manifest.json':'537e84afef215a338fc30d8b5c02816e01945af40bec3e1bff752a44052764da'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1
row=rows[0];n='Sign33CurrentNaturalCoreNorms';src=p/'src/DiophantineConsistency'/f'{n}.lean';s=src.read_text();assert row['module']=='DiophantineConsistency.'+n and row['source_sha256']==sha(src)=='d977d8b81971154b27f58da6f61fd0ccb2795aff0f273504a7f94aed66a87b35' and row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33CurrentCoreNorms']
for x in ['InternalZero ObjectCurrentEquation2011.naturalExpression u','fun j => ι (u j+1)','d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1','Sign33CurrentCoreNorms.source_core_norms u','internalZero_positiveShift ObjectCurrentEquation2011.expression u).mp hz']:assert x in s
prior=(d/'research/nine-sharing-sign33-current-core-norms-check/src/DiophantineConsistency/Sign33CurrentCoreNorms.lean').read_text();assert 'InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)' in prior and '(fun j => u j+1)' in prior and 'd.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1' in prior
survey=(p/'provider_survey.py').read_text();assert "'research/nine-sharing-sign33-current-core-norms-check/attempt01/state.json','c3fd69521bec9a0b77c673c8c69ed03653c1fa60b6fd3d54b6c48963d1842ac7'" in survey and "'corenorms'" in survey
run=(p/'run.py').read_text();assert "if mod in survey['selected']" in run and "need(guard(deps)==row['direct_guard']" in run
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'natural zero to five shifted core unit assumptions, source/provider checks only'},indent=2,sort_keys=True))
