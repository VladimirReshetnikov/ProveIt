#!/usr/bin/env python3
"""Exact abstract-rank checks of parallel-copy padding and zero-variable restriction."""
if not __debug__:raise SystemExit('Run without -O.')
from pathlib import Path
from itertools import combinations
from functools import reduce
import argparse,hashlib,json,time
p=argparse.ArgumentParser();p.add_argument('--source-note',type=Path,default=Path('/workspace/shared/full-selected-tail-lorentzian/OLD_SPANNING_REMOVAL.md'));p.add_argument('--output-dir',type=Path,default=Path(__file__).parent);args=p.parse_args();start=time.monotonic()
def masks(n,k):return []if k<0 else [sum(1<<i for i in I)for I in combinations(range(n),k)]
examples=[(f'U{q}_{n}',n,q,set(masks(n,q)))for q,n in [(0,2),(1,2),(1,4),(2,2),(2,4),(3,4),(4,4)]]
examples.append(('partition_with_loop',5,2,{(1<<i)|(1<<j)for i in [0,1]for j in [2,3]}))
examples.append(('Fano',7,3,{mask for mask in masks(7,3)if reduce(int.__xor__,[i+1 for i in range(7)if mask>>i&1])!=0}))
pairs=[3,12,48,192];forbidden={pairs[i]|pairs[j]for i,j in combinations(range(4),2)if(i,j)!=(2,3)}
examples.append(('rank4_sparse_paving',8,4,set(masks(8,4))-forbidden))
checks=nonspanning=loops=0
for label,n,q,bases in examples:
 rank0=[max((B&S).bit_count()for B in bases)for S in range(1<<n)]
 for a,b in combinations(range(n),2):
  order=[i for i in range(n)if i not in(a,b)]+[a,b];m=n-2
  rank=[rank0[sum(1<<order[i]for i in range(n)if S>>i&1)]for S in range(1<<n)]
  targets=[i for i in [m,m+1]if rank[1<<i]>0];loops+=2-len(targets)
  def extended(S):
   original=S&((1<<n)-1)
   for j,target in enumerate(targets):
    if S>>(n+j)&1:original|=1<<target
   return rank[original]
  old=list(range(m));newold=old+list(range(n,n+len(targets)))
  assert extended(sum(1<<i for i in newold))==q
  if rank[(1<<m)-1]<q:nonspanning+=1
  f=[];ff=[]
  for size,extra in [(q,0),(q-1,1<<m),(q-1,1<<(m+1)),(q-2,3<<m)]:
   orig=set(I for I in masks(m,size)if rank[I|extra]==q);f.append(orig)
   padded=set()
   for positions in masks(len(newold),size):
    chosen=sum(1<<newold[i]for i in range(len(newold))if positions>>i&1)
    if extended(chosen|extra)==q and not positions>>m:padded.add(positions)
   ff.append(padded)
  assert f==ff and f[1]|f[2]==ff[1]|ff[2]
  # The no-Y polynomial is exactly the original full basis polynomial.
  recovered=f[0]|{I|(1<<m)for I in f[1]}|{I|(1<<(m+1))for I in f[2]}|{I|(3<<m)for I in f[3]}
  assert recovered=={S for S in masks(n,q)if rank[S]==q} and recovered
  checks+=1
r={'verdict':'PASS','source_sha256':hashlib.sha256(args.source_note.read_bytes()).hexdigest(),'abstract_matroid_examples':len(examples),'distinguished_pair_padding_checks':checks,'original_nonspanning_old_sets':nonspanning,'distinguished_loop_occurrences':loops,'all_five_families_restrict_exactly':True,'nonzero_full_basis_no_Y_layer':True,'finite_checks_are_supplementary':True,'elapsed_seconds':round(time.monotonic()-start,3)}
args.output_dir.mkdir(parents=True,exist_ok=True);(args.output_dir/'padding_receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
