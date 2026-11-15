#!/usr/bin/env python3
"""Transfer a sound radius-six parent envelope through marker separation.

Every unknown newly exposed boundary bit is included in both possibilities.
The input envelope itself is supplied, not inferred by a bounded execution.
"""
from pathlib import Path
import sys,json,hashlib,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
import build as b
ap=argparse.ArgumentParser()
ap.add_argument('input',type=Path)
ap.add_argument('output',type=Path)
args=ap.parse_args()
old=b.read(HERE/'input/machine.native.tm');new,proof=b.construct(old)
K=6;W=2*K+1;MASK=(1<<W)-1
out=set();inputs=0;filtered=0
for ln in args.input.read_text().splitlines():
 q,m=map(int,ln.split());inputs+=1
 if q in(301,88)and ((m>>(K-1))&1)!=(0 if q==301 else 1):filtered+=1;continue
 out.add((b.rename(q),m))
 if q not in (301,88):continue
 nq,p,mm=88,0,m
 w,d,n=old[q,(m>>K)&1];goal=(b.rename(n),1 if d else-1,(m&~(1<<K))|(w<<K))
 for step in range(5):
  a=new[nq,(mm>>(K+p))&1];w,d,nq=a;mm=(mm&~(1<<(K+p)))|(w<<(K+p));p+=1 if d else-1
  if(nq,p,mm)==goal:break
  assert p in(-1,0)
  if p==0:out.add((nq,mm))
  else:
   z=(mm<<1)&MASK
   out.add((nq,z));out.add((nq,z|1))
 else:raise AssertionError(q)
args.output.parent.mkdir(parents=True,exist_ok=True)
text=''.join(f'{q} {m}\n'for q,m in sorted(out));args.output.write_text(text)
receipt=dict(radius=6,input_windows=inputs,history_impossible_windows_removed=filtered,output_windows=len(out),
 inherited_source_context_sha256=hashlib.sha256(args.input.read_bytes()).hexdigest(),
 output_sha256=hashlib.sha256(text.encode()).hexdigest(),scope='Sound relative envelope transfer assuming the supplied parent envelope; used for bounded reduction search only')
args.output.with_suffix('.transfer.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
