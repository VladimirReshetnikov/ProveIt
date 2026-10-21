#!/usr/bin/env python3
"""Own literal-source/table comparison, no candidate execution."""
import argparse,hashlib,json
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();k=int(q),int(b);assert k not in t;t[k]=(int(w),d,int(z))
 assert len(t)==430;return t

def compare(A,B):
 m={0:0,84:84,254:254};todo=[0,84];issues=[]
 for q in todo:
  if q==254:continue
  for bit in (0,1):
   a,b=A[q,bit],B[m[q],bit]
   if a[:2]!=b[:2]:issues.append(['write/move',q,bit,m[q],a,b]);continue
   if a[2]in m:
    if m[a[2]]!=b[2]:issues.append(['target',q,bit,m[q],a,b,m[a[2]]])
   elif b[2]in m.values():issues.append(['injection',q,bit,m[q],a,b])
   else:m[a[2]]=b[2];todo.append(a[2])
 if not issues:assert len(m)==216 and {(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in A.items()}==B
 return {'exact_bijection':not issues,'mapped_states_including_halt':len(m),'mapping':m,'conflicts':issues}

def main():
 p=argparse.ArgumentParser();p.add_argument('--a',type=Path,required=True);p.add_argument('--b',type=Path,required=True);p.add_argument('--accepted',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 A=a.a/'machine/k215.native.tm';B=a.b/'candidate215/k215.native.tm';C=a.accepted/'k215.native.tm';same=compare(table(A),table(B));prior=compare(table(C),table(B))
 sa=a.a/'source/sites215.json'
 if not sa.exists():sa=a.a/'machine/sites215.json'
 sb=a.b/'candidate215/sites215.json';sc=a.accepted/'sites215.json';assert sa.read_bytes()==sb.read_bytes()==sc.read_bytes()
 r={'status':'SOURCE162_164_LITERAL_COMPARISON_COMPLETE','source162_native_sha256':sha(A),'source164_native_sha256':sha(B),'accepted_native_sha256':sha(C),'exact_source_sha256':sha(sb),'source162_to164':same,'accepted_to164':prior,'scope':'Own all-row structural comparison seeded by fixed0/84/254, exact source bytes. No execution or runtime acceptance claim; a proven bijection permits transfer once one representative is actually checked.','script_sha256':sha(Path(__file__))};a.output.write_text(json.dumps(r,indent=2)+'\n');print(r['status'],same['exact_bijection'],len(same['conflicts']),prior['exact_bijection'])
if __name__=='__main__':main()
