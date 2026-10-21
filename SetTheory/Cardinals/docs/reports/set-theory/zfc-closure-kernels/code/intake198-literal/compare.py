#!/usr/bin/env python3
"""Literal all-row rooted isomorphisms and source identity; no machine execution."""
from pathlib import Path
import argparse,json,hashlib,gzip

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(gzip.decompress(p.read_bytes())if p.suffix=='.gz'else p.read_bytes())
def table(p,halt=254):
 T={};starts=[]
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):starts.append(int(line[9:]));continue
  if not line.strip()or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R');T[q,b]=(w,d,z)
 Q={q for q,b in T};assert starts==[0]and len(Q)==215 and len(T)==430 and set(T)=={(q,b)for q in Q for b in(0,1)}and{z for w,d,z in T.values()}-Q=={halt};return T

def isomorphism(A,B):
 m={0:0,254:254};todo=[0];seen=set()
 while todo:
  q=todo.pop()
  if q in seen:continue
  seen.add(q)
  for b in(0,1):
   w,d,z=A[q,b];v,e,y=B[m[q],b];assert(w,d)==(v,e),(q,b,'write/motion')
   if z in m:assert m[z]==y,(q,b,'inconsistent mapping')
   else:assert y not in m.values();m[z]=y
   if z!=254:todo.append(z)
 assert len(seen)==215 and len(m)==len(set(m.values()))==216
 assert {(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in A.items()}==B
 return m

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--accepted',type=Path,required=True);ap.add_argument('--source160',type=Path,required=True);ap.add_argument('--source161',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 C=a.accepted;A=table(C/'k215.native.tm');src=read(C/'sites215.json');case0=read(C/'verification/root-run1/runtime/runtime_cases.json.gz');start0=read(C/'verification/root-run1/runtime/startup.json.gz')
 old={int(q):z for q,z in read(C/'code/runtime-inputs/inputs/legacy_mapping.json').items()}
 for q in{q for q,b in A}|{254}:
  if q not in old:old[q]=q+1000
 inv={v:k for k,v in old.items()};out=[]
 for number,P in[(160,a.source160),(161,a.source161)]:
  B=table(P/'machine/k215.native.tm');m=isomorphism(A,B);assert read(P/'source/sites215.json')==src
  dense=table(P/'machine/k215.tm',215);can={int(q):v for q,v in read(P/'machine/canonicalization.json')['native_to_canonical'].items()};assert can[0]==0 and can[254]==215 and len(can)==len(set(can.values()))==216
  assert {(can[q],b):(w,d,can[z])for(q,b),(w,d,z)in B.items()}==dense
  legacy={int(q):z for q,z in read(P/'code/inputs/legacy_mapping.json').items()}
  for q in{q for q,b in B}|{254}:
   if q not in legacy:legacy[q]=q+1000
  cases=read(P/'evidence/runtime_cases.json.gz');assert len(cases)==len(case0)==6176
  for i,(x,y)in enumerate(zip(case0,cases)):
   z=dict(x);z['rows']=sorted([[legacy[m[inv[q]]],b]for q,b in x['rows']]);assert z==y,('case',number,i)
  st=read(P/'evidence/startup.json.gz');t=dict(start0);t['state']=m[t['state']];t['trace']=[[m[q],h,b,w,d,m[z]]for q,h,b,w,d,z in t['trace']];assert t==st
  out.append({'source':number,'native_sha256':sha(P/'machine/k215.native.tm'),'canonical_sha256':sha(P/'machine/k215.tm'),'source_raw_sha256':sha(P/'source/sites215.json'),'all430_rows_match':True,'all215_states_reachable':True,'source_ordered_sites_equal':True,'all6176_delivered_cases_equal_after_label_map':True,'complete_delivered95714step_startup_equal_after_label_map':True,'canonical_map_exact':True,'native_state_map':{str(q):z for q,z in sorted(m.items())},'changed_labels':[[q,z]for q,z in sorted(m.items())if q!=z]})
 r={'status':'EXACT_LITERAL_ISOMORPHISM_SOURCE_AND_DELIVERED_RECORD_TRANSFER_PASS','accepted_native_sha256':sha(C/'k215.native.tm'),'accepted_source_sha256':sha(C/'sites215.json'),'sources':out,'scope':'Every literal row and starting/halt state correspond under a bijection. This proves all-initial-tape step-for-step isomorphism and transfers the accepted215 theorem. Delivered runtime/blank records independently compare after exact label translation; no supplied or candidate execution.'}
 a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2)+'\n');print(r['status'])
if __name__=='__main__':main()
