#!/usr/bin/env python3
"""Three phase-unlocked degree1 action deletions; external scratch only."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import importlib.util
import hashlib,json,time
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
if not __debug__:parser.error('Keep assertions enabled')
ROOT=args.repo.resolve();OUT=args.output.resolve()
if OUT==ROOT or ROOT in OUT.parents:parser.error('External scratch output required')
OUT.mkdir(parents=True,exist_ok=True)
SOURCE=ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/50-terms-machine_experiments-entry_resynthesis.py'
spec=importlib.util.spec_from_file_location('phase_entry_source50',SOURCE)
M=importlib.util.module_from_spec(spec);spec.loader.exec_module(M)
EXCLUDED={8202,8203,8204,8358,8359,8360}
start=time.monotonic();h=M.Harness(ROOT,1000)
assert hashlib.sha256(h.source.read_bytes()).hexdigest()=='939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
selected=json.loads((OUT/'journal-filter.json').read_text())['phase_unlocked_recipes']
records=[]
for recipe in selected:
 dead=str(recipe['deleted_state']);action=tuple(recipe['assigned_actions']['0'])
 incoming=[k for k,v in h.table.items() if v[2]==dead and k[0]!=dead]
 assert incoming==[('172',1)]
 table={k:v for k,v in h.table.items() if k[0]!=dead};table[incoming[0]]=action
 assert len(table)==502 and len({q for q,_ in table})==251
 assert all(table[k]==h.table[k] for k in h.protected)
 assert not any(t==dead for _,_,t in table.values())
 assert table['64',0]==h.table['64',0] and table['64',1]==h.table['64',1]
 tested=[];failure=None
 affected=h.usage[incoming[0]]
 order=sorted((i for i in range(8391) if i not in EXCLUDED),key=lambda i:(i not in affected,h.cost[i],i))
 for i in order:
  ok,cost,reason=h.check(M.PartialTable(table),i)
  tested.append(i)
  if not ok:
   path,op,reg,zero,branch,target=h.cases[i]
   failure={'case':i,'path':path,'op':op,'register':reg,'zero':zero,'reason':reason}
   break
 entry={'deleted':int(dead),'incoming':list(incoming[0]),'before':list(h.table[incoming[0]]),
        'after':list(action),'prior_failure':recipe['first_failure_case'],
        'phase_checks':len(tested),'tested_case_indices':tested,'failure':failure,
        'status':'retained_guard_checker_stop' if failure else 'all8385_phase_contracts_pass',
        'table_sha256':hashlib.sha256(h.audit.encode({(int(q),b):(w,d,int(t)) for (q,b),(w,d,t) in table.items()})).hexdigest(),
        'new_vs503_target_only_family':action[1]!=h.table[incoming[0]][1] or action[0]!=h.table[incoming[0]][0]}
 if failure is None:entry['blank']=h.blank(table,1000000)
 records.append(entry)
result={'status':'bounded selected family complete','baseline_all8391_affine':'PASS','baseline_whole82552_blank':'PASS',
        'table_source':str(h.source),'table_sha256':hashlib.sha256(h.source.read_bytes()).hexdigest(),
        'table_rows':504,'baseline_states':252,'candidate_states':251,'fuel':1000,
        'excluded_source_guards':sorted(EXCLUDED),'selected_recipes':3,'records':records,
        'seconds':time.monotonic()-start,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'source50_harness_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'functional_source_identities':h.hashes,
        'scope':'Conditional affine screen under an ordinary phase invariant, not a Lean proof. Fuel/unsupported stops are not semantic refutations. No frozen source was edited.'}
(OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
