#!/usr/bin/env python3
"""Independently audit complete fresh K218 evidence; do not rerun generic proofs."""
from pathlib import Path
import argparse,json
from independent_facts import table,read,sha,dump,TABLE,SOURCE

def blockproof(t,records):
 # bit^(c+v*n), n arbitrary natural. Only exact self-loops accelerate n cells.
 specs=[(73,1,'B','B',[(0,1,0),(1,1,0),(1,0,1)],[(0,1,0),(1,1,1)]),
 (95,1,'B','C',[(0,1,0),(1,1,0),(1,0,1)],[(1,1,0),(0,1,0),(1,0,1)]),
 (48,-1,'B','B',[(1,1,0),(1,0,1),(0,1,0)],[(1,1,1),(0,1,0)]),
 (112,-1,'C','B',[(1,0,1),(0,1,0),(1,1,0)],[(1,1,1),(0,1,0)])]
 def compact(tokens):
  out=[]
  for b,c,v in tokens:
   if out and b==out[-1][0]:out[-1]=(b,out[-1][1]+c,out[-1][2]+v)
   else:out.append((b,c,v))
  return out
 assert len(records)==len(specs)==4;proofs=[]
 for rec,(entry,direction,before,after,word,target)in zip(records,specs):
  q=entry;actual=[];proof=[]
  for b,c,v in word:
   w,d,z=t[q,b];assert d==direction
   if v:assert c==0 and v==1 and q==z
   else:assert c==1
   proof.append(['unary',[q,b,w,d,z],[0,0,1]+[0]*10]if v else['literal',[q,b,w,d,z]])
   actual.append((w,c,v));q=z
  assert q==entry and compact(actual)==target
  assert(rec['entry'],rec['direction'],rec['before'],rec['after'])==(entry,direction,before,after)
  assert rec['steps']=='v+2'and rec['arbitrary_contexts']is True and rec['trace']==proof
  assert(sum(c for b,c,v in word),sum(v for b,c,v in word))==(2,1)
  proofs.append(dict(entry=entry,direction=direction,before=before,after=after,duration=[2,1],trace=proof,arbitrary_n_including_zero=True,arbitrary_exterior_untouched=True))
 return proofs

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[2]);a=p.parse_args();r=a.root;out=Path(__file__).resolve().parent
 folder=r/'research_sub219/decoder/reuse12_focused_bfs/candidate_4dd4ca3893a80b99';d=r/'research_sub218/runtime_audit/candidate218';script=d.parent/'runtime_check.py';vendor=r/'research_sub219/intake/replay219/parent_replay/baseline/K221_Construction_2026-10-20/verification'
 # The actual pinned vendor files are in the inherited baseline verification directory.
 if not(vendor/'symbolic_runtime.py').exists():
  candidates=list((r/'research_sub219/intake/replay219/parent_replay/baseline/K221_Construction_2026-10-20').rglob('symbolic_runtime.py'));assert len(candidates)==1;vendor=candidates[0].parent
 t=table(folder/'candidate.tm');s=read(folder/'sites.json');rec=read(d/'runtime.json');cases=read(d/'cases.json');integrity=read(d/'integrity.json');start=read(d/'startup.json');ours=read(out/'whole_blank_startup.json');facts=read(out/'independent_facts.json')
 assert sha(folder/'candidate.tm')==TABLE and sha(folder/'sites.json')==SOURCE
 for name,h in integrity['hashes'].items():assert sha(d/name)==h
 assert integrity['checker_sha256']==sha(script)=='d7f1aee7fd671d8e8677d557bb3ae6d5a64e8385490f3e8b9a5cbcc4d9dceb61'
 assert rec['engine_sha256']==sha(vendor/'symbolic_runtime.py')=='c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145'
 assert rec['helper_sha256']==sha(vendor/'independent_runtime.py')=='0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'
 for x in(rec,integrity,start):assert(x['table_sha256'],x['source_sha256'])==(TABLE,SOURCE)
 assert rec['status']=='ALL_GENERIC_PRIMITIVE_INTERFACES_PROVED'and rec['failures']==[]and rec['generic_cases_excluded']==0
 required=[(i,b)for i,(_,op,v)in enumerate(s)for b in((False,True)if op=='CD'else(False,))]
 assert len(required)==len(cases)==rec['cases']==rec['expected_cases']==integrity['generic_cases']==6167
 assert[(x['index'],x['positive'])for x in cases]==required
 for x in cases:
  assert type(x['index'])is int and type(x['positive'])is bool
  assert len(x['duration'])==13 and all(type(v)is int and v>=0 for v in x['duration'])and x['duration'][0]>0
  assert len(x['motion'])==13 and all(type(v)is int for v in x['motion'])
  assert type(x['symbolic_steps'])is int and 0<x['symbolic_steps']<4000
  assert x['symbolic_steps']==sum(x['kinds'].values())and set(x['kinds'])<={'literal','unary','list'}and all(type(v)is int and v>0 for v in x['kinds'].values())
 assert rec['symbolic_steps']==sum(x['symbolic_steps']for x in cases)==integrity['symbolic_steps']==1514325
 assert min(x['duration'][0]for x in cases)==integrity['minimum_duration_constant']==13
 assert rec['directly_used_rows']==[list(k)for k in sorted(t)]and len(t)==integrity['directly_used_rows']==436
 mp={int(k):v for k,v in rec['mapping'].items()};assert set(mp)=={q for q,b in t}|{254}and len(set(mp.values()))==len(mp)
 assert(mp[0],mp[84],mp[254],mp[79],mp[102],mp[120])==(95,96,254,1079,1301,1302)and not{96,190}&mp.keys()
 # A table renaming is checked forward and inverse at every row and target.
 remap={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()};inv={v:k for k,v in mp.items()}
 assert{(inv[q],b):(w,d,inv[z])for(q,b),(w,d,z)in remap.items()}==t
 blocks=blockproof(remap,rec['block_schemas'])
 assert sha(d/'canonical.tm')==sha(out/'k218.canonical.tm')==facts['canonical_sha256']==start['canonical_sha256']
 assert start['normalized_to_canonical']==facts['search_to_canonical']
 for key in('steps','state','head','ones','logical_registers','physical_registers','spares','extra_gap'):assert start['startup'][key]==ours[key]
 assert start['startup']['all_other_cells']==0 and ours['all_other_cells_zero']and start['startup']['sparse_and_dense_agree']and ours['two_distinct_interpreters_agree']
 assert start['startup_row_counts']==ours['row_counts']
 result=dict(status='INDEPENDENT_K218_COMPLETE_FRESH_EVIDENCE_AUDIT_PASS',table_sha256=TABLE,source_sha256=SOURCE,canonical_sha256=sha(d/'canonical.tm'),working_states=218,transition_rows=436,complete_ordered_guarded_cases=len(cases),generic_cases_excluded=0,symbolic_steps=rec['symbolic_steps'],minimum_duration_constant=13,complete_literal_row_coverage=436,startup_steps=312701,startup_entire_tape_and_all_row_counts_match_our_two_interpreters=True,block_proofs=blocks,complete_runtime_label_bijection=True,exact_fresh_run_receipt_hashes={name:sha(d/name)for name in('cases.json','runtime.json','startup.json','canonical.tm','integrity.json')},runtime_checker_sha256=sha(script),audit_checker_sha256=sha(Path(__file__)),facts_receipt_sha256=sha(out/'independent_facts.json'),trust_boundary='This independently checks the already completed fresh generic proof evidence and rederives four universal block identities. It does not reexecute all 6,167 generic symbolic derivations. The isolated release default must reexecute those derivations. Executable mathematical checking, not an exact-byte proof-assistant kernel endpoint.')
 dump(out/'runtime_evidence_audit.json',result);print(json.dumps({k:v for k,v in result.items()if k!='block_proofs'},indent=2))
if __name__=='__main__':
 if not __debug__:raise RuntimeError('Run without -O, -OO or PYTHONOPTIMIZE')
 main()
