#!/usr/bin/env python3
"""Literal blank-run rejection of a tempting 215-state command-order variant.
No imported runtime checker and no finite approximation to nonhalting.
"""
from pathlib import Path
import hashlib,json,argparse
HERE=Path(__file__).resolve().parent

def load(path):
 rows={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R');rows[q,b]=(w,1 if d=='R'else-1,z)
 qs={q for q,b in rows};assert set(rows)=={(q,b)for q in qs for b in(0,1)}and{z for w,d,z in rows.values()}-qs=={254}
 return rows

def encoded_frame(head,regs,spares,gap):
 phy=(6,2,0,4,3,7,8,5,1);values=[None]*9
 for i,j in enumerate(phy):values[j]=regs[i]
 ones={head-1,head+64+gap};p=head+64+gap+1
 for v in values+spares:p+=1;ones.update(range(p,p+v+1));p+=v+1
 return ones

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'replay-result.json');args=ap.parse_args()
 parent=load(HERE/'k215-parent.tm');T=load(HERE/'rejected-permutation.tm');N=dict(parent)
 assert N[134,1]==(1,1,12)and N[174,1]==(1,1,135)
 N[134,1]=(1,1,135);N[174,1]=(1,1,12)
 assert N==T and len(T)==430
 q=h=0;ones=set();root_checked=False
 for tick in range(646554):
  if tick==494760:
   assert q==84 and h==-4
   assert ones==encoded_frame(-4,[2,0,4,0,1,0,0,0,0],[1]*172,128)
   root_checked=True
  if q==254:break
  w,d,q=T[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 assert root_checked and(q,tick,h,len(ones))==(254,646553,1,409)
 result={'status':'EXACT_BLANK_HALT_REPRODUCED','states':215,'rows':430,'root_step':494760,'root_registers':[2,0,4,0,1,0,0,0,0],'root_spares':172,'root_gap':128,'halt_step':tick,'halt_head':h,'halt_one_cells':len(ones),'table_sha256':hashlib.sha256((HERE/'rejected-permutation.tm').read_bytes()).hexdigest(),'finite_support_sha256':hashlib.sha256(json.dumps(sorted(ones),separators=(',',':')).encode()).hexdigest(),'scope':'Exact execution, complete finite tape support and zero exterior. This machine is rejected, not proposed as a consistency candidate.'}
 args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
