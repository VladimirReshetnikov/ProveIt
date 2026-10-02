#!/usr/bin/env python3
"""Independent rank-oracle principal-extension and matroid-union support checks."""
if not __debug__:raise SystemExit('Run without -O.')
from itertools import combinations
from fractions import Fraction
from collections import defaultdict,Counter
from pathlib import Path
import argparse,hashlib,json,time
p=argparse.ArgumentParser();p.add_argument('--source-note',type=Path,default=Path('/workspace/shared/full-selected-tail-lorentzian/ALL_MATROIDS_EXTENSION.md'));p.add_argument('--output-dir',type=Path,default=Path(__file__).parent);args=p.parse_args();start=time.monotonic()
def masks(n,k):return []if k<0 else [sum(1<<i for i in I)for I in combinations(range(n),k)]
def bititems(mask):
 while mask:
  b=mask&-mask;mask-=b;yield b
matroids=[]
for rank,n in [(0,2),(1,4),(2,5),(3,5)]:matroids.append((f'uniform_U{rank}_{n}',n,rank,set(masks(n,rank))))
matroids.append(('partition_rank2_with_loop',5,2,{(1<<i)|(1<<j)for i in [0,1]for j in [2,3]}))
fano={mask for mask in masks(7,3)if __import__('functools').reduce(int.__xor__,[i+1 for i in range(7)if mask>>i&1])!=0}
matroids.append(('Fano_binary_rank3',7,3,fano))
pairs=[3,12,48,192];forbidden={pairs[i]|pairs[j]for i,j in combinations(range(4),2)if (i,j)!=(2,3)}
matroids.append(('rank4_sparse_paving_five_pair_hyperplanes',8,4,set(masks(8,4))-forbidden))
base_exchange_checks=0
for label,n,q,bases in matroids:
 assert bases and all(B.bit_count()==q for B in bases)
 for B in bases:
  for C in bases:
   for i in bititems(B&~C):
    assert any((B^i^j)in bases and (C^j^i)in bases for j in bititems(C&~B));base_exchange_checks+=1

def families(ranks,n,q):
 m=n-2;ab=3<<m
 return [set(mask for mask in masks(m,k)if ranks[mask|extra]==q)for k,extra in [(q,0),(q-1,1<<m),(q-1,2<<m),(q-2,ab)]]
def clean(poly):return {k:v for k,v in poly.items()if v}
def target_f(fam,m,pops):
 u0,ua,ub,vv=fam;uu=ua|ub;l0=sum(w for typ,w in pops if typ==1);l1=sum(w for typ,w in pops if typ==2);common=[w for typ,w in pops if typ==3];H=sum(common);S=sum(x*y for x,y in combinations(common,2));M=l0*l1+H*(l0+l1)+S;poly=defaultdict(int)
 def add(family,aa,bb,zz,weight):
  for I in family:poly[(aa,bb,zz,I)]+=weight
 add(u0,0,0,2,1);add(u0,1,0,1,l0+H);add(u0,0,1,1,l1+H);add(u0,1,1,0,M);add(ua,1,0,2,1);add(ub,0,1,2,1);add(ua,1,1,1,l1);add(ub,1,1,1,l0);add(uu,1,1,1,H);add(vv,1,1,2,1)
 return clean(poly)
def transversal_ranks(types):
 ny=len(types);rows=[sum(1<<i for i,t in enumerate(types)if t&1),sum(1<<i for i,t in enumerate(types)if t&2)]+[1<<i for i in range(ny)];out=[]
 for subset in range(1<<(ny+2)):
  possible={0}
  for i,neighbors in enumerate(rows):
   if not subset>>i&1:continue
   new=set(possible)
   for used in possible:
    for b in bititems(neighbors&~used):new.add(used|b)
   possible=new
  out.append(max(mask.bit_count()for mask in possible))
 return out
populations=[[],[(1,2)],[(2,3)],[(3,1)],[(1,2),(2,3)],[(1,2),(3,1)],[(2,3),(3,1)],[(3,1),(3,2)],[(1,2),(2,3),(3,1)],[(3,0),(3,1)]]
principal_checks=union_checks=union_candidates=contractions=0;labels=Counter();spanning_choices=0
for label,n,q,bases in matroids:
 original=[max((B&mask).bit_count()for B in bases)for mask in range(1<<n)]
 for aa,bb in combinations(range(n),2):
  perm=[i for i in range(n)if i not in (aa,bb)]+[aa,bb];m=n-2
  ranks=[original[sum(1<<perm[i]for i in range(n)if mask>>i&1)]for mask in range(1<<n)]
  if ranks[(1<<m)-1]!=q:continue
  spanning_choices+=1;fam=families(ranks,n,q);u0,ua,ub,vv=fam;uu=ua|ub;ab=3<<m
  # Direct free-on-flat rank formula, with three newly adjoined elements.
  clones=3;actual=defaultdict(Fraction)
  for chosen in masks(n+clones,q):
   old=chosen&((1<<n)-1);k=(chosen>>n).bit_count();rankplus=min(ranks[old|ab],ranks[old]+k)
   if rankplus==q:actual[(int(old>>m&1),int(old>>(m+1)&1),k,old&((1<<m)-1))]+=Fraction(1,clones**k)
  expected=defaultdict(Fraction)
  for family,a,b,y,w in [(u0,0,0,0,1),(ua,1,0,0,1),(ub,0,1,0,1),(uu,0,0,1,1),(vv,1,1,0,1),(vv,1,0,1,1),(vv,0,1,1,1),(vv,0,0,2,Fraction(1,3))]:
   for I in family:expected[(a,b,y,I)]+=w
  assert clean(actual)==clean(expected);principal_checks+=1
  for pops in populations:
   ny=len(pops);N=n+ny;rt=transversal_ranks([t for t,w in pops]);cost=[]
   for mask in range(1<<N):
    r1=ranks[mask&((1<<n)-1)];local=((mask>>m)&3)|((mask>>n)<<2);r2=rt[local]
    cost.append(r1+r2-mask.bit_count())
   best=cost[:]
   for i in range(N):
    for mask in range(1<<N):
     if mask>>i&1:best[mask]=min(best[mask],best[mask^(1<<i)])
   rank_union=lambda mask:mask.bit_count()+best[mask]
   assert rank_union((1<<N)-1)==q+ny
   actual=defaultdict(int)
   for chosen in masks(N,q+ny):
    union_candidates+=1
    if rank_union(chosen)!=q+ny:continue
    missing=[j for j in range(ny)if not chosen>>(n+j)&1];assert len(missing)<=2
    value=1
    for j in missing:value*=pops[j][1]
    key=(int(chosen>>m&1),int(chosen>>(m+1)&1),2-len(missing),chosen&((1<<m)-1));actual[key]+=value
   assert clean(actual)==target_f(fam,m,pops);union_checks+=1;labels[label]+=1
  # The five Boolean families commute with every old nonloop contraction.
  for e in range(m):
   if ranks[1<<e]==0:continue
   perm2=[i for i in range(n)if i!=e];cr=[ranks[(1<<e)|sum(1<<perm2[i]for i in range(n-1)if mask>>i&1)]-1 for mask in range(1<<(n-1))]
   cf=families(cr,n-1,q-1)
   def remove(I):return (I&((1<<e)-1))|((I>>(e+1))<<e)
   for before,after in zip(fam,cf):assert {remove(I)for I in before if I>>e&1}==after
   assert {remove(I)for I in (ua|ub)if I>>e&1}==cf[1]|cf[2];contractions+=1
receipt={'verdict':'PASS','source_sha256':hashlib.sha256(args.source_note.read_bytes()).hexdigest(),'abstract_matroid_examples':len(matroids),'base_symmetric_exchange_checks':base_exchange_checks,'distinguished_pairs_with_spanning_old_set':spanning_choices,'principal_line_rank_formula_basis_identities':principal_checks,'matroid_union_rank_formula_polynomial_identities':union_checks,'union_candidate_bases_tested':union_candidates,'old_nonloop_contraction_checks':contractions,'checks_by_example':dict(labels),'zero_population_weights_included':True,'matroid_union_and_principal_extension_theorems':'primary Bonin-Kung inputs; finite examples are corroboration only','finite_checks_are_supplementary':True,'elapsed_seconds':round(time.monotonic()-start,3)}
args.output_dir.mkdir(parents=True,exist_ok=True);(args.output_dir/'independent_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
