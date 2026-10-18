#!/usr/bin/env python3
"""Collect retained experiment records; optionally gzip large recipe ledgers."""
from pathlib import Path
from collections import Counter
import argparse,gzip,hashlib,json,shutil

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PIN='43026ff42f0939f09b9e95495248cfadcad38e38'

def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
 return h.hexdigest()

def evidence(relative):
 path=HERE/relative
 compressed=path.with_suffix(path.suffix+'.gz')
 if compressed.exists():
  h=hashlib.sha256();length=0
  with gzip.open(compressed,'rb') as stream:
   for block in iter(lambda:stream.read(1024*1024),b''):h.update(block);length+=len(block)
  if path.exists():assert h.hexdigest()==digest(path) and length==path.stat().st_size
  return {'path':'compression/'+relative+'.gz','sha256':digest(compressed),'bytes':compressed.stat().st_size,'uncompressed':{'logical_path':'compression/'+relative,'sha256':h.hexdigest(),'bytes':length}}
 if not path.exists():raise FileNotFoundError(path)
 return {'path':'compression/'+relative,'sha256':digest(path),'bytes':path.stat().st_size}

def read(relative):return json.loads((HERE/relative).read_text())

def json_safe(value):
 if isinstance(value,int) and not isinstance(value,bool) and abs(value)>2**53-1:return str(value)
 if isinstance(value,dict):return {k:json_safe(v) for k,v in value.items()}
 if isinstance(value,list):return [json_safe(v) for v in value]
 return value

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--compress-ledgers',action='store_true')
 args=parser.parse_args()
 if args.compress_ledgers:
  for path in sorted(HERE.rglob('*.jsonl')):
   if 'two_entry_run' in path.parts or path.stat().st_size<3_000_000:continue
   with path.open('rb') as src,path.with_suffix('.jsonl.gz').open('wb') as raw:
    with gzip.GzipFile(filename='',mode='wb',compresslevel=9,fileobj=raw,mtime=0) as dst:shutil.copyfileobj(src,dst)

 result={
  'scope':'Additional compression diagnostics. No verified machine below252 states was found; no minimality or semantic-inequivalence theorem is claimed.',
  'pinned_ProveIt_commit':PIN,
  'machine_below_252_found':False,
  'large_integer_encoding':'Integers exceeding2^53-1 are decimal strings in this aggregate; original records retain their native JSON encoding.',
  'diagnostic_limits':{'strict_symbolic_rule_fuel':1000,'prefix_route_literal_fuel':10000,'prefix_route_literal_window_cells':2048,'new_proof_assistant_build':False},
  'completed_experiments':[],
  'partial_experiments':[],
 }
 def add(identifier,path,scope,recipes=None,ledgers=(),status='completed'):
  record={'id':identifier,'scope':scope,'status':status,'record':read(path),'evidence':[evidence(path)]}
  if recipes is not None:record['full_recipes_in_declared_family']=recipes
  for ledger in ledgers:record['evidence'].append(evidence(ledger))
  result['completed_experiments' if status=='completed' else 'partial_experiments'].append(record)
  return record

 add('original_degree2','native_summary.json','Original program; six explicitly source-excluded guards omitted; unchanged original box contracts;46 eligible deletions and arbitrary actions at both incoming rows.',46*1008**2,('native_groups.jsonl',))
 add('mp_old_permutation_degree2','mp_native/native_summary.json','MP source edit under old permutation; all8366 guards;47 eligible deletions and arbitrary incoming actions.',47*1008**2,('mp_native/native_groups.jsonl',))
 add('selected_fold_one_row_repairs','repair_results.json','Original folds204->252,113->23,34->68, followed by one arbitrary action repair in a complete failed-trace lookup hitting set; original six-guard phase exclusion.',128896,('repair_results.jsonl',))

 locals=[
  ('mp_gap40_full','mp_newperm_native',8366,'Old positive-decrement box contract; rebased MP permutation; gap n+40.'),
  ('mp_gap40_source_phase','mp_newperm_phase_native',8363,'Same table and gap; modified-program phase excludes8202,8203,8204.'),
  ('mp_gap43_full','mp_newperm_gap43_native',8366,'Old positive-decrement contract; rebased MP; gap n+43.'),
  ('mp_gap43_source_phase','mp_newperm_gap43_phase_native',8363,'Same table and gap n+43; three source-excluded guards omitted.'),
  ('mp_source_invariant_net_effect_box','mp_invariant_box_native',8363,'Gap n+43 and source phase; nine net register offsets and source-proved interval/constant guard facts; extra zero spare blocks ignored under all-zero-suffix invariant.'),
  ('prefix_old_mp_permutation','prefix_decrement_native',8366,'Prefix-right positive decrement under permutation0,2,6,8,7,5,3,1,4; explicit left-phase premise; changed support frozen.'),
  ('prefix_clean_best_permutation','prefix_best_native',8366,'Prefix-right decrement under permutation7,8,4,2,5,6,0,3,1; explicit left-phase premise; changed support frozen.'),
 ]
 for identifier,directory,guards,scope in locals:
  data=read(directory+'/local_search_summary.json')
  assert data['baseline_cases']==guards and data['tested']==153736 and data['survivors']==0
  add(identifier,directory+'/local_search_summary.json',scope+' Recipes are55471 uniform and98265 directed mixed rows, not unique machines.',153736,(directory+'/local_search.jsonl',))

 add('prefix_scanner_incoming_actions','prefix_route_native/summary.json','Deletion of85,97,112,131 with arbitrary incoming actions. A concrete17,325-sample continuation screen only, not an unbounded contract proof.',2*1008+2*1008**2,('prefix_route_native/search.jsonl',))
 add('prefix_state2_takeover_targets','prefix_best_native/context_reuse_targets_summary.json','Fixed takeover85->2 plus0/1->4 and42/1->6; target-only repair of20/0,20/1,143/1; modified mark macro returns6 for physical0.',252**3)
 add('prefix_state2_takeover_full_actions','prefix_best_native/context_reuse_adaptive_summary.json','Same fixed takeover; all write/move/target actions at the three decoder rows; adaptive failing-guard order; explicit prefix-phase premise and modified mark macro.',1008**3)
 add('shared250_existing_zero_entry_repair','prefix_zero_repair.json','Unsafe250-state shared scanner; one arbitrary action at0/read0;81 concrete zero-CD samples with permitted gap growth0/1/2. Every action fails the first sample.',1004)

 for identifier,directory in [('mp_old_learned_higher','mp_native'),('mp_rebased_learned_all','mp_newperm_native')]:
  record=add(identifier,directory+'/learned_summary.json','Arbitrary incoming actions with a1000000-node cap per deleted state. Only individually completed families are exhausted; aggregate remains partial.',ledgers=(directory+'/learned_groups.jsonl',),status='partial')
  groups=[json.loads(line) for line in (HERE/directory/'learned_groups.jsonl').read_text().splitlines()]
  completed=[g for g in groups if g['remaining']==0]
  record['families_observed']=len(groups)
  record['completed_families']=len(completed)
  record['completed_degree_counts']={str(k):v for k,v in sorted(Counter(g['degree'] for g in completed).items())}
  record['incomplete_deleted_states']=[g['deleted'] for g in groups if g['remaining']!=0]
 add('prefix_state2_takeover_initial_capped','prefix_best_native/context_reuse_summary.json','Historical fixed-order2million-node attempt, superseded by the completed adaptive run.',status='partial')

 result['source_invariants']=[{'id':name,'record':read(name+'.json'),'evidence':evidence(name+'.json')} for name in ('mp_phase','mp_dirty_phase','mp_affine_invariants','mp_affine_nonnegative')]
 result['tables']=[evidence(p) for p in ('mp_newperm_native/newperm252.tm','prefix_decrement_native/table.tm','prefix_best_native/table.tm','prefix_zero250.tm')]
 result['independent_prefix_review']='logic_audit/prefix-phase-verification.json'
 result['archive_policy']={'omit':['compression/two_entry_run/lazy-nodes.jsonl','native executables','Python cache directories'],'large_ledgers':'Include matching.jsonl.gz; raw ledger may then be omitted. Summaries and generators remain mandatory.','search_overlap':'Recipe families overlap and directed mixed rows include isomorphic duplicates; do not sum them as distinct machines.'}
 result['unmeasured_direction']='Inventory alternative PC return operators and recompile source leaves with wrappers, such as(CD_brk2,CB0), rather than requiring the original brk1 interface. No emitted machine or wrapper cost was established.'
 (HERE/'final_summary.json').write_text(json.dumps(json_safe(result),indent=2)+'\n')
 print('Wrote compression/final_summary.json with',len(result['completed_experiments']),'completed and',len(result['partial_experiments']),'partial experiment records.')

if __name__=='__main__':main()
