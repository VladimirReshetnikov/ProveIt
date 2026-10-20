#!/usr/bin/env python3
"""Transport all decoder roles through logical register2/8 exchange.

The first literal entry proposal swaps the five leaf-selector rows. It is
explicitly provisional: row123/0 also has an arithmetic CI5 role.
"""
from pathlib import Path
from collections import defaultdict
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source_work'));import rotation_search as r
OUT=ROOT/'source218/rename28';OUT.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def rename(x):return 8 if x==2 else 2 if x==8 else x
results=[]
for label,tp,sp in[
 ('published',ROOT/'baseline219/K219_Construction_2026-10-20/machine/k219.native.tm',ROOT/'baseline219/K219_Construction_2026-10-20/machine/sites219.json'),
 ('alternative',ROOT/'source218/alternative219/candidate.tm',ROOT/'source218/alternative219/sites.json')]:
 T=r.b.read_table(tp.read_bytes());oldrows=json.loads(sp.read_text());old=r.s.tree(oldrows)
 rows=[[pc,op,rename(arg)if op in('CI','CD')else arg]for pc,op,arg in oldrows]
 tree=r.s.tree(rows);ng=r.s.graph_arithmetic(rows)[0];og=r.s.graph_arithmetic(oldrows)[0]
 assert ng==r.s.graph_intervals(rows)
 assert ng==[[[effect[0],rename(effect[1])]if len(effect)==2 else effect,targets]for effect,targets in og]
 groups,paths,node_states=r.mapping(T,old);pq={p:q for q,ps in paths.items()for p in ps}
 changedkeys={(pq[pc[:-1]],int(pc[-1]))for pc,op,arg in oldrows if op in('CI','CD')and arg in(2,8)}
 U=dict(T);changes=[]
 for key in sorted(changedkeys):
  w,d,z=U[key];assert z in(39,56)
  assert all(r.s.leaf(n[key[1]])for n in groups[key[0]])
  U[key]=(w,d,56 if z==39 else 39);changes.append([*key,*U[key]])
 folder=OUT/label;folder.mkdir(exist_ok=True);(folder/'sites.json').write_bytes(r.s.compact(rows))
 for count in(219,218):
  V=dict(U)
  if count==218:
   V={(q,b):(w,d,88 if z==301 else z)for(q,b),(w,d,z)in V.items()if q!=301}
   V[88,0]=(0,-1,51);V[88,1]=(1,1,103);V[51,0]=(0,1,122);V[51,1]=(1,1,51)
  (folder/f'candidate{count}.tm').write_bytes(r.b.table_bytes(V))
  with(folder/f'start{count}.txt').open('w')as of,(folder/f'start{count}.log').open('w')as ef:
   subprocess.run([str(ROOT/'source218/search_start_permuted'),str(folder/f'candidate{count}.tm'),'3000000','6','3','0'],stdout=of,stderr=ef,check=True)
  starts=(folder/f'start{count}.txt').read_text().splitlines()
  rec={'status':'TRANSPORTED_REGISTER_RENAMING_PROPOSAL','layout':label,'working_states':count,
       'source_metrics':r.s.metrics(tree),'source_sha256':sha(folder/'sites.json'),'table_sha256':sha(folder/f'candidate{count}.tm'),
       'register_permutation':{i:rename(i)for i in range(9)},'changed_leaf_rows':changes,
       'source_effects_conjugate_by_register_permutation':True,'new_internal_decoder_edges':0,
       'startup_hits':len(starts),'startup_output':starts,
       'known_obligation':'Row123/0 is also an arithmetic CI5 helper; all primitive interfaces and prefix binding remain to be checked.'}
  (folder/f'receipt{count}.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec)
  print(json.dumps({k:v for k,v in rec.items()if k!='startup_output'}),flush=True)
(OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
