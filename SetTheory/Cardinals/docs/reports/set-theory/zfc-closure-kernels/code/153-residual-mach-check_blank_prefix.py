#!/usr/bin/env python3
"""Exact sparse/dense blank prefix to a clean dispatch frame (finite evidence only)."""
import argparse,hashlib,json
from pathlib import Path
PHY=(6,2,0,4,3,7,8,5,1)

def decode_frame(q,h,ones):
 if q!=84 or h-1 not in ones:return None
 if any(x<h-1 for x in ones):return None
 cand=[x for x in ones if x>=h+64]
 if not cand:return None
 header=min(cand)
 if {x for x in ones if x<header}!={h-1}:return None
 values=[];p=header+1;last=max(ones)
 while p<=last:
  if p in ones or p+1 not in ones:return None
  start=p+1;p=start
  while p in ones:p+=1
  values.append(p-start-1)
 if p!=last+1 or len(values)<10:return None
 physical=values[:9];logical=[physical[j]for j in PHY]
 if any(logical[i] for i in [1,2,3,5,6,7,8]):return None
 reconstructed={h-1,header};p=header+1
 for value in values:
  p+=1;reconstructed.update(range(p,p+value+1));p+=value+1
 assert reconstructed==ones
 return {'head':h,'header':header,'gap':header-h-64,'logical_registers':logical,'physical_registers':physical,'spares':values[9:]}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('out',type=Path);ap.add_argument('--limit',type=int,default=5000000);a=ap.parse_args();raw=a.table.read_bytes();T={}
 for line in raw.decode().splitlines():
  if not line.strip() or line.startswith('#'):continue
  q,bit,w,d,z=line.split();T[int(q),int(bit)]=int(w),(-1 if d=='L'else 1),int(z)
 ones=set();q=h=0;used=set();result=None
 for tick in range(a.limit+1):
  if tick and q==84:
   result=decode_frame(q,h,ones)
   if result is not None:break
  if tick==a.limit or q==254:break
  bit=int(h in ones);used.add((q,bit));w,d,q=T[q,bit]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 if result is None:
  out={'status':'NOT_REACHED_WITHIN_FINITE_LIMIT','steps':tick,'state':q,'head':h,'table_sha256':hashlib.sha256(raw).hexdigest()}
 else:
  # Independently parse the bytes and execute the exact same step count with two dense arrays.
  dense={}
  for line in raw.decode('ascii').splitlines():
   if not line or line.startswith('#'):continue
   fields=line.split();state=int(fields[0]);read=int(fields[1]);write=int(fields[2]);delta={'L':-1,'R':1}[fields[3]];dest=int(fields[4]);assert (state,read)not in dense;dense[state,read]=(write,delta,dest)
  positive=bytearray(1);negative=bytearray();dq=dh=0
  for _ in range(tick):
   arr,ix=(positive,dh)if dh>=0 else(negative,-dh-1)
   if ix>=len(arr):arr.extend(bytes(ix+1-len(arr)))
   write,delta,dq=dense[dq,arr[ix]];arr[ix]=write;dh+=delta
  support={i for i,v in enumerate(positive)if v}|{-i-1 for i,v in enumerate(negative)if v}
  assert(dq,dh,support)==(q,h,ones)
  out={'status':'SPARSE_DENSE_COMPLETE_BLANK_PREFIX_PASS','steps':tick,'state':q,'working_states':len(T)//2,'transition_rows':len(T),'table_sha256':hashlib.sha256(raw).hexdigest(),'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),**result,'one_cells':sorted(ones),'all_other_cells':0,'used_rows':sorted(used),'scope':'Exact finite blank prefix to empty-PC dispatch, with control3, registers1/2/5/6/7/8 allzero and arbitrary natural0/4. Infinite source correctness and arithmetic refinement are separate obligations.'}
 a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items()if k not in ['one_cells','spares','used_rows']},flush=True)
if __name__=='__main__':main()
