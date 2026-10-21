#!/usr/bin/env python3
"""Own bounded exact source composition; no new submitted code import/allocation/runtime."""
from pathlib import Path
import json,hashlib
import source_language as s
import source_splice as sp
O=Path(__file__).resolve().parent
K=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC')
P=Path('/tmp/zfc-intake197/extracted/K216_Permuted_Commands_2026-10-21')
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(p,pin):
 raw=p.read_bytes();assert sha(raw)==pin;return s.tree(json.loads(raw))
def save(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
old=load(K/'candidate-k217/sites217.json','9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655')
partial=load(K/'candidate-k216/sites216.json','c865047ce7283521199e93ce74307821f3b3231742213329b7ac5e8a7ec0b6d2')
base=load(P/'source/frozen202.json','abb7229877759170b61dfcfe21ca0889b3df2f91f4215383817a125eb0f8996c')
read=sp.serial(sp.closed_forest(old,23,37));load_d=sp.serial(sp.closed_forest(old,228,254))
assert sp.size(read)==14 and sp.size(load_d)==26
walk,transfer=read;assert(sp.size(walk),sp.size(transfer))==(11,3)
assert all(s.boundary(n)==(0,0,False)for n in(walk,transfer,load_d))
read_load=(walk,(transfer,load_d))
edits={(23,37):None,(187,201):None,(228,254):read_load,(4659,4685):read_load}
control=sp.apply_closed_splices(old,edits);assert control==base,'own recipe exact frozen202 identity control'
newbase=sp.apply_closed_splices(partial,edits)
paths=('111','110101','110100101')
def permute(t,order):
 bodies=[s.subtree(t,p)for p in paths]
 assert[sp.size(x)for x in bodies]==[106,26,26]
 assert all(s.boundary(x)[:2]==(0,0)for x in bodies)
 def go(n,p=''):
  if p in paths:return bodies[order[paths.index(p)]]
  if s.leaf(n):return n
  return go(n[0],p+'0'),go(n[1],p+'1')
 return go(t)
def intervals(t):
 out={}
 def go(n,p='',lo=0):
  hi=lo+sp.size(n);out[lo,hi]=(p,n)
  if not s.leaf(n):go(n[0],p+'0',lo);go(n[1],p+'1',lo+sp.size(n[0]))
 go(t);return out
before=intervals(partial); H=before[412,4586][1];A=before[412,466][1];B=before[4574,4584][1]
report=[]
for tag,perm,path,pin in [('unpermuted',(0,1,2),'source/frozen202.json','abb7229877759170b61dfcfe21ca0889b3df2f91f4215383817a125eb0f8996c'),('210',(2,1,0),'machine/sites216.json','8b5dc46f10d927b2db5e4bcb522d482779ec61c72c82717d7bf12fca3550a3bc'),('120',(1,2,0),'secondary/sites120.json','ee1f7c7cb216a80315449371b040ee094728a655439954225ed4be4635296680')]:
 target=load(P/path,pin);assert permute(control,perm)==target
 trial=permute(newbase,perm);rows=s.sites(trial);targetrows=s.sites(target)
 assert[r[1:]for r in rows]==[r[1:]for r in targetrows]
 g=s.graph_intervals(rows);assert g==s.graph_arithmetic(rows)[0]==s.graph_intervals(targetrows)==s.graph_arithmetic(targetrows)[0]
 iv=intervals(trial)
 assert any(n==H for p,n in iv.values()),'complete partial selector including contextual repair retained'
 assert iv[398,452][1]==A and iv[4560,4570][1]==B
 raw=s.compact(rows);(O/f'sites-{tag}.json').write_bytes(raw)
 report.append({'tag':tag,'source_sha256':sha(raw),'metrics':s.metrics(trial),'full_word_and_both_CFGs_match_permuted_reference':True,'guarded_edges':sum(len(x[1])for x in g),'partial_selector':{'span':[398,4572],'path':iv[398,4572][0],'whole_subtree_unchanged':iv[398,4572][1]==H},'source_file':f'sites-{tag}.json'})
result={'status':'EXACT_SOURCE_COMPOSITION_PASS','source_control':'Own four-splice recipe reproduces supplied202 source exactly before composing it with partial216 source. Exact command permutations separately reproduce both submitted sources.','products':report,'edits':[[*rg,'delete'if n is None else'closed read_then_load40']for rg,n in edits.items()],'scope':'Source only. Exact unchanged ordered primitives and full guarded CFG against each independently calibrated command-permuted reference. The complete partial selector and its contextual172 source repair remain as a subtree. Physical allocator, old69/400 helper compatibility, binary runtime and blank startup remain unproved for these new sources.','inputs':{str(p):sha(p.read_bytes())for p in[Path(__file__),O/'source_language.py',O/'source_splice.py',K/'candidate-k217/sites217.json',K/'candidate-k216/sites216.json',P/'code/build_sources.py',P/'code/audit_command_permutation.py']}}
save(O/'result.json',result);print(json.dumps(result,indent=2))
