#!/usr/bin/env python3
"""Homomorphic source-register transport with literal leaf selector changes.

This is a candidate generator, not a compiler-correctness certificate.  It
keeps every internal decoder edge and transports all logical roles of each
physical state together.  Shared primitive rows must agree on their direct
selector; internal/primitive mixed rows are immutable.  Fresh symbolic
primitive checking and a complete blank startup are separate obligations.
"""
from pathlib import Path
from collections import defaultdict,Counter
from itertools import permutations
import argparse,hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source_work'));import rotation_search as r
SELECT={
 'CI':{0:14,1:61,2:56,3:161,4:71,5:63,6:13,7:82,8:39},
 'CD':{0:14,1:41,2:56,3:17,4:144,5:45,6:21,7:62,8:39}}
PHY=(6,2,0,4,3,7,8,5,1)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def prepare(T,rows):
 groups,paths,ns=r.mapping(T,r.s.tree(rows))
 pq={p:q for q,ps in paths.items()for p in ps}
 leafroles=defaultdict(set)
 for pc,op,arg in rows:leafroles[pq[pc[:-1]],int(pc[-1])].add((op,arg))
 internal={(q,b)for q,nn in groups.items()for n in nn for b in(0,1)if not r.s.leaf(n[b])}
 return leafroles,internal

def transport(T,meta,perm):
 leafroles,internal=meta;U=dict(T);changes=[]
 for key,roles in leafroles.items():
  if all(op not in SELECT or perm[arg]==arg for op,arg in roles):continue
  if key in internal:return None,'SHARED_INTERNAL_ROW'
  acts=set()
  for op,arg in roles:
   if op not in SELECT or perm[arg]==arg:acts.add(T[key])
   else:acts.add((key[1],1,SELECT[op][perm[arg]]))
  if len(acts)!=1:return None,'SHARED_PRIMITIVE_ROW'
  act=next(iter(acts));U[key]=act
  if act!=T[key]:changes.append([*key,*act])
 return U,changes

def merge218(T):
 # This exact fold assumes the left-child selector of old301 remains CD5.
 if T[301,0]!=(0,1,45)or T[88,0]!=(0,1,122)or T[88,1]!=(1,1,103):return None
 U={(q,b):(w,d,88 if z==301 else z)for(q,b),(w,d,z)in T.items()if q!=301}
 U[88,0]=(0,-1,51);U[88,1]=(1,1,103);U[51,0]=(0,1,122);U[51,1]=(1,1,51)
 return U

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'source218/register_transport')
 ap.add_argument('--bound',type=int,default=3000000);ap.add_argument('--all-starts',action='store_true')
 ap.add_argument('--phases',type=Path);a=ap.parse_args();out=a.output;out.mkdir(parents=True,exist_ok=True)
 results=[];start=time.monotonic();census=Counter()
 for label,tp,sp in[
 ('published',ROOT/'baseline219/K219_Construction_2026-10-20/machine/k219.native.tm',ROOT/'baseline219/K219_Construction_2026-10-20/machine/sites219.json'),
 ('alternative',ROOT/'source218/alternative219/candidate.tm',ROOT/'source218/alternative219/sites.json')]:
  T=r.b.read_table(tp.read_bytes());rows=json.loads(sp.read_text());meta=prepare(T,rows)
  survivors=[]
  for perm in permutations(range(9)):
   U,info=transport(T,meta,perm)
   if U is None:census[label+':'+info]+=1;continue
   V=merge218(U)
   if V is None:census[label+':FOLD_ROLE_CHANGED']+=1;continue
   survivors.append((perm,U,V,info))
  print('CENSUS',label,len(survivors),dict(census),flush=True)
  for j,(perm,U,V,changes)in enumerate(survivors):
   name=''.join(map(str,perm));folder=out/label/name;folder.mkdir(parents=True,exist_ok=True)
   if (folder/'receipt.json').exists():
    rec=json.loads((folder/'receipt.json').read_text());results.append(rec);continue
   path=folder/'candidate218.tm';path.write_bytes(r.b.table_bytes(V))
   args=[str(ROOT/'source218/search_start_permuted_select'),str(path),str(a.bound),str(PHY[perm[0]]),str(PHY[perm[4]]),str(PHY[perm[8]])]
   if not a.all_starts:args.append('0')
   with(folder/'startup.txt').open('w')as of,(folder/'startup.log').open('w')as ef:
    ans=subprocess.run(args,stdout=of,stderr=ef)
   hits=(folder/'startup.txt').read_text().splitlines()
   rec={'layout':label,'permutation':perm,'table_sha256':sha(path),'changed_leaf_rows':changes,'returncode':ans.returncode,'startup_hits':len(hits),'startup_output':hits,'directory':str(folder.relative_to(ROOT))}
   if hits:
    newrows=[[pc,op,perm[arg]if op in SELECT else arg]for pc,op,arg in rows]
    (folder/'sites.json').write_bytes(r.s.compact(newrows));(folder/'candidate219.tm').write_bytes(r.b.table_bytes(U))
    print('HIT',json.dumps(rec),flush=True)
   (folder/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');results.append(rec)
   if j%20==0:print('PROGRESS',label,j+1,'/',len(survivors),'hits',sum(x['startup_hits']for x in results),'seconds',round(time.monotonic()-start,2),flush=True)
   summary={'status':'PARTIAL','census':dict(census),'results':results,'bound':a.bound,'all_starts':a.all_starts,'seconds':time.monotonic()-start}
   if j%20==0:(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 summary['status']='COMPLETE_TRANSPORT_CATALOGUE_SCREEN';summary['scope']='Candidate generation and finite blank checks only; primitive interfaces remain unproved for any new table.'
 (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 print('FINAL',len(results),'tables','hits',sum(x['startup_hits']for x in results),'seconds',time.monotonic()-start,flush=True)

if __name__=='__main__':main()
