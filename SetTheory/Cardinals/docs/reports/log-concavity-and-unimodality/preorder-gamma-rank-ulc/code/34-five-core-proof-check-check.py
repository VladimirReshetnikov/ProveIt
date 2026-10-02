#!/usr/bin/env python3
"""Independent exact certificate checker. Python standard library only.

Usage: python check.py [producer-directory] [output-receipt.json] [workers]
No producer module is imported. Endpoint support uses explicit injections.
Polynomial exponents are packed in base 16, a collision-free representation
because this checker also bounds total polynomial degree by eight.
"""
from pathlib import Path
from itertools import combinations, permutations
from collections import defaultdict, Counter
from fractions import Fraction
from math import factorial
from concurrent.futures import ProcessPoolExecutor
import sys, json, hashlib, time

N=5
DIM=12
SHIFTS=[1 << (4*i) for i in range(DIM)]
VERTICES=tuple(range(N))
ARCS=tuple((i,j) for i in VERTICES for j in VERTICES if i!=j)
ARC_INDEX={p:i for i,p in enumerate(ARCS)}
SUBSETS={k:tuple(combinations(VERTICES,k)) for k in range(N+1)}
# Factorial-scaled elementary sink moments after the boundary substitution.
# E0=1, E1=A+B, E2=AB+B²/2, E3=AB²/2+B³/6.
SINKS={0:((0,1),),1:((SHIFTS[10],1),(SHIFTS[11],1)),
       2:((SHIFTS[10]+SHIFTS[11],2),(2*SHIFTS[11],1)),
       3:((SHIFTS[10]+2*SHIFTS[11],3),(3*SHIFTS[11],1))}

# Independent complete candidate endpoint support pairs; each has all possible
# injections from the head set into distinct tail vertices (matching witnesses).
CANDIDATES=[]
for k in range(1,4):
 for S in SUBSETS[k]:
  outside=tuple(j for j in VERTICES if j not in S)
  for r in range(min(k,N-k)+1):
   for J in combinations(outside,r):
    witnesses=tuple(tuple(zip(tails,J)) for tails in permutations(S,r))
    exponent=sum(SHIFTS[i] for i in S)+sum(SHIFTS[5+j] for j in J)
    CANDIDATES.append((k,r,exponent,witnesses))

def encode(e):
 assert len(e)==DIM and all(type(v) is int and 0<=v<=8 for v in e), ('bad exponent',e)
 assert sum(e)<=8, ('degree overflow',e)
 return sum(v*s for v,s in zip(e,SHIFTS))

def kernels_and_scaled_gammas(rows):
 G=[None,defaultdict(int),defaultdict(int),defaultdict(int)]
 C=defaultdict(dict)
 for k,r,e,witnesses in CANDIDATES:
  # Boolean inclusion: one term iff at least one matching witness exists.
  present=any(all(rows[i] & (1<<j) for i,j in witness) for witness in witnesses)
  if present:
   C[k,r][e]=1
   multiplier=factorial(k)//factorial(k-r)
   for sinkexp,sinkcoef in SINKS[k-r]:
    G[k][e+sinkexp]+=multiplier*sinkcoef
 return C,G

def product_add(out,P,Q,weight):
 for e,c in P.items():
  for f,d in Q.items():out[e+f]+=weight*c*d

def check_one(args):
 base,ident,expected_rows=args
 path=Path(base)/'cubic-two'/f'certificate_{ident}.json'
 raw=path.read_bytes();certificate=json.loads(raw)
 assert certificate['rows']==list(expected_rows), ('wrong graph',ident)
 assert certificate['target']=='3G2^2-4G1G3', ('wrong target',ident)
 C,G=kernels_and_scaled_gammas(expected_rows)
 P=defaultdict(int)
 product_add(P,G[2],G[2],3)
 product_add(P,G[1],G[3],-4)
 P={e:c for e,c in P.items() if c}
 negative=sum(c<0 for c in P.values())
 R=dict(P)
 terms=certificate['terms']
 for item in terms:
  weight,meta=item
  weight=Fraction(weight)
  assert weight>0, ('nonpositive square multiplier',ident)
  outer,inner=meta
  outer_degree=sum(outer);outer=encode(outer)
  assert len(inner)==2, ('not binomial',ident)
  powers=[]
  for e,c in inner:
   assert outer_degree+2*sum(e)==8, ('wrong homogeneous square degree',ident)
   powers.append((encode(e),Fraction(c)))
  for e,c in powers:
   for f,d in powers:
    key=outer+e+f
    R[key]=R.get(key,0)-weight*c*d
 assert all(c>=0 for c in R.values()), ('negative exact remainder',ident,min(R.values()))
 return {'id':ident,'squares':len(terms),'empty':not terms,'coefficient_positive':negative==0,
         'target_terms':len(P),'negative_target_terms':negative,
         'positive_remainder_terms':sum(c>0 for c in R.values()),
         'certificate_sha256':hashlib.sha256(raw).hexdigest()}

def coverage(cores):
 maps=[]
 for perm in permutations(VERTICES):
  maps.append(tuple(1<<ARC_INDEX[(perm[i],perm[j])] for i,j in ARCS))
 seen=bytearray(1<<len(ARCS));sizes=[]
 for ident,(code,rows) in enumerate(cores):
  actual=sum(1<<a for a,(i,j) in enumerate(ARCS) if rows[i]>>j&1)
  assert actual==code, ('code/rows mismatch',ident)
  assert len(rows)==N and all(0<=rows[i]<(1<<N) and not (rows[i]>>i&1) for i in VERTICES)
  edge_indices=[i for i in range(len(ARCS)) if code>>i&1]
  orbit={sum(mapping[i] for i in edge_indices) for mapping in maps}
  assert min(orbit)==code, ('representative not minimum',ident)
  assert all(not seen[c] for c in orbit), ('duplicate isomorphism class',ident)
  for c in orbit:seen[c]=1
  sizes.append(len(orbit))
 assert all(seen), ('uncovered graphs',len(seen)-sum(seen))
 return {'labeled_graphs':sum(seen),'expected_labeled_graphs':2**20,
         'disjoint_isomorphism_classes':len(sizes),
         'orbit_size_histogram':dict(sorted(Counter(sizes).items()))}

def verify_symbolic_scaling():
 # Generic gamma coefficients, recorded in a separate two-variable moment ring.
 E=[{(0,0):Fraction(1)}, {(1,0):Fraction(1),(0,1):Fraction(1)},
    {(1,1):Fraction(1),(0,2):Fraction(1,2)},
    {(1,2):Fraction(1,2),(0,3):Fraction(1,6)}]
 for q in range(4):
  converted={a*SHIFTS[10]+b*SHIFTS[11]:factorial(q)*v for (a,b),v in E[q].items()}
  assert converted==dict(SINKS[q])
 for k in range(1,4):
  for r in range(min(k,N-k)+1):
   for coefficient in E[k-r].values():
    assert factorial(k)*coefficient == (factorial(k)//factorial(k-r))*(factorial(k-r)*coefficient)
 assert 3*factorial(2)**2==12
 assert 4*factorial(1)*factorial(3)==24
 return {'G1':'gamma1','G2':'2 gamma2','G3':'6 gamma3',
         'identity':'3 G2^2 - 4 G1 G3 = 12 (gamma2^2 - 2 gamma1 gamma3)',
         'moments':['E1=A+B','E2=AB+B^2/2','E3=AB^2/2+B^3/6']}

if __name__=='__main__':
 start=time.time()
 if len(sys.argv)>1:
  base=Path(sys.argv[1])
 else:
  base=Path(__file__).resolve().parent.parent/'certificate-data'
  if not (base/'cores.txt').is_file() or not (base/'cubic-two').is_dir():
   raise SystemExit('Provide the certificate-data directory as the first argument; no package-relative data was found.')
 destination=Path(sys.argv[2] if len(sys.argv)>2 else Path(__file__).with_name('receipt.json'))
 workers=int(sys.argv[3]) if len(sys.argv)>3 else 4
 cores=[]
 for line in (base/'cores.txt').read_text().splitlines():
  code,*rows=map(int,line.split());cores.append((code,tuple(rows)))
 assert len(cores)==9608, len(cores)
 # Direct transitivity test of the reflexive closure, independent of producer.
 def is_preorder(rows):
  relation={(i,j) for i in VERTICES for j in VERTICES if i==j or rows[i]>>j&1}
  return all((i,k) in relation for i in VERTICES for j in VERTICES for k in VERTICES if (i,j) in relation and (j,k) in relation)
 preorder_count=sum(is_preorder(rows) for code,rows in cores)
 assert preorder_count==139, ('preorder count',preorder_count)
 files=list((base/'cubic-two').glob('certificate_*.json'))
 assert len(files)==len(cores)
 expected={f'certificate_{i}.json' for i in range(len(cores))}
 assert {f.name for f in files}==expected
 print('Checking exact certificate expansions for',len(cores),'core representatives',flush=True)
 results=[]
 with ProcessPoolExecutor(max_workers=workers) as pool:
  jobs=((str(base),i,rows) for i,(code,rows) in enumerate(cores))
  for result in pool.map(check_one,jobs,chunksize=32):
   results.append(result)
   if len(results)%1000==0:print('Verified',len(results),'certificates;',round(time.time()-start,2),'seconds',flush=True)
 print('Checking complete labeled graph coverage',flush=True)
 cov=coverage(cores)
 scaling=verify_symbolic_scaling()
 count=sum(r['squares'] for r in results)
 empty=sum(r['empty'] for r in results)
 pos=sum(r['coefficient_positive'] for r in results)
 digest=hashlib.sha256('\n'.join(f"{r['id']}:{r['certificate_sha256']}" for r in results).encode()).hexdigest()
 receipt={'pass':True,'verifier':'standalone Python standard library; no producer imports',
          'certificate_count':len(results),'preorder_representative_count':preorder_count,
          'rational_binomial_square_count':count,
          'empty_certificate_count':empty,'coefficientwise_nonnegative_target_count':pos,
          'all_exact_remainders_coefficientwise_nonnegative':True,
          'positive_remainder_term_count':sum(r['positive_remainder_terms'] for r in results),
          'zero_remainder_count':sum(r['positive_remainder_terms']==0 for r in results),
          'coverage':cov,'scaling':scaling,
          'file_manifest_sha256':digest,
          'cores_sha256':hashlib.sha256((base/'cores.txt').read_bytes()).hexdigest(),
          'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'seconds':round(time.time()-start,3)}
 destination.write_text(json.dumps(receipt,indent=2)+'\n')
 destination.with_name('certificate-manifest.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps(receipt,indent=2),flush=True)
