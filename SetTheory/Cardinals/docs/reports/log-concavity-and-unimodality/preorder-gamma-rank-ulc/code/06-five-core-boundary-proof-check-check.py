#!/usr/bin/env python3
"""Independent exact degree-four first-gap checker; standard library only.
Usage: python check.py FAMILY [SOURCE] [RECEIPT] [WORKERS]
FAMILY is four-active or four-sink. Default SOURCE is ../certificate-data,
relative to this script; absent package-relative data requires explicit SOURCE.
No discovery module or producer kernel is imported.
"""
from pathlib import Path
from itertools import combinations, permutations
from collections import defaultdict, Counter
from fractions import Fraction
from math import factorial
from concurrent.futures import ProcessPoolExecutor
import sys,json,hashlib,time
V=tuple(range(5));DIM=12;RADIX=16
UNITS=tuple(RADIX**i for i in range(DIM))
CONFIG={
 'four-active':{'tail_vertices':tuple(range(4)),'catalog':'four_active_cores.txt','directory':'four-active-cubic','classes':3044,'target':'2G2^2-3G1G3','expected_squares':212319,'expected_empty':158},
 'four-sink':{'tail_vertices':V,'catalog':'cores.txt','directory':'four-sink-moment-cubic','classes':9608,'target':'2G2^2-3G1G3 under A=B+C'},
}
# Moment polynomials are represented as dictionaries on the two last variables.
MOMENTS={
 'four-active':[{(0,0):Fraction(1)}, {(1,0):Fraction(1),(0,1):Fraction(1)},
                {(1,1):Fraction(1),(0,2):Fraction(1,2)},
                {(1,2):Fraction(1,2),(0,3):Fraction(1,6)}],
 'four-sink':[{(0,0):Fraction(1)}, {(1,0):Fraction(1),(0,1):Fraction(2)},
              {(1,1):Fraction(1),(0,2):Fraction(3,2)},
              {(1,2):Fraction(1,2),(0,3):Fraction(2,3)}],
}
CANDIDATES={}
for family,cfg in CONFIG.items():
 candidates=[]
 for k in range(1,4):
  for S in combinations(cfg['tail_vertices'],k):
   for r in range(min(k,5-k)+1):
    for J in combinations(tuple(j for j in V if j not in S),r):
     witnesses=tuple(tuple(zip(sources,J)) for sources in permutations(S,r))
     exponent=sum(UNITS[i] for i in S)+sum(UNITS[5+j] for j in J)
     candidates.append((k,r,exponent,witnesses))
 CANDIDATES[family]=candidates

def encode(e,family):
 assert len(e)==DIM and all(type(z) is int and 0<=z<=8 for z in e), ('bad exponent',e)
 assert sum(e)<=8, ('overflow degree',e)
 if family=='four-active':assert e[4]==0,('forbidden inactive tail exponent',e)
 return sum(z*t for z,t in zip(e,UNITS))

def gammas(rows,family):
 G=[None,defaultdict(int),defaultdict(int),defaultdict(int)]
 for k,r,exponent,witnesses in CANDIDATES[family]:
  if not any(all(rows[i]>>j&1 for i,j in witness) for witness in witnesses):continue
  # Direct gamma construction with the independently stated rational moments,
  # then factorial scaling; all coefficients here must become integers.
  for (a,b),coefficient in MOMENTS[family][k-r].items():
   scaled=factorial(k)*coefficient
   assert scaled.denominator==1
   G[k][exponent+a*UNITS[10]+b*UNITS[11]]+=scaled.numerator
 return G

def product_add(out,P,Q,scale):
 for e,c in P.items():
  for f,d in Q.items():out[e+f]+=scale*c*d

def check_one(job):
 source,family,index,rows=job;cfg=CONFIG[family]
 raw=(Path(source)/cfg['directory']/f'certificate_{index}.json').read_bytes()
 cert=json.loads(raw)
 assert cert['rows']==list(rows),('row mismatch',family,index)
 assert cert['target']==cfg['target'],('target mismatch',family,index)
 if family=='four-active':assert cert['zero_tail_indices']==[4],('wrong specialization',index)
 G=gammas(rows,family);P=defaultdict(int)
 product_add(P,G[2],G[2],2);product_add(P,G[1],G[3],-3)
 P={e:c for e,c in P.items() if c}
 if family=='four-active':assert all((e//UNITS[4])%RADIX==0 for e in P)
 R=dict(P);squares=cert['terms'];lengths=Counter()
 for weight,meta in squares:
  weight=Fraction(weight);assert weight>0,('nonpositive multiplier',family,index)
  multiplier,inside=meta
  outer_degree=sum(multiplier);m=encode(multiplier,family)
  assert len(inside)>0,('empty square',family,index)
  terms=[]
  for e,c in inside:
   assert outer_degree+2*sum(e)==8,('nonhomogeneous square',family,index)
   terms.append((encode(e,family),Fraction(c)))
  lengths[len(inside)]+=1
  for e,c in terms:
   for f,d in terms:
    key=m+e+f;R[key]=R.get(key,0)-weight*c*d
 assert all(c>=0 for c in R.values()),('negative remainder',family,index,min(R.values()))
 return {'id':index,'squares':len(squares),'empty':not squares,
         'coefficient_positive':all(c>=0 for c in P.values()),
         'target_terms':len(P),'negative_target_terms':sum(c<0 for c in P.values()),
         'positive_remainder_terms':sum(c>0 for c in R.values()),
         'square_length_histogram':dict(lengths),'certificate_sha256':hashlib.sha256(raw).hexdigest()}

def check_coverage(cores,family):
 tails=CONFIG[family]['tail_vertices'];arcs=tuple((i,j) for i in tails for j in V if i!=j)
 index={e:i for i,e in enumerate(arcs)}
 perms=tuple(tuple(p)+(4,) for p in permutations(range(4))) if family=='four-active' else tuple(permutations(V))
 maps=[tuple(1<<index[p[i],p[j]] for i,j in arcs) for p in perms]
 seen=bytearray(1<<len(arcs));sizes=[];preorders=0
 for ident,(code,rows) in enumerate(cores):
  assert len(rows)==5 and all(0<=rows[i]<32 and not rows[i]>>i&1 for i in V)
  if family=='four-active':assert rows[4]==0
  actual=sum(1<<a for a,(i,j) in enumerate(arcs) if rows[i]>>j&1)
  assert actual==code,('bad graph code',ident)
  edges=[i for i in range(len(arcs)) if code>>i&1]
  orbit={sum(mapping[i] for i in edges) for mapping in maps}
  assert min(orbit)==code,('not least orbit representative',ident)
  assert all(not seen[c] for c in orbit),('intersecting listed orbits',ident)
  for c in orbit:seen[c]=1
  sizes.append(len(orbit))
  relation={(i,j) for i in V for j in V if i==j or rows[i]>>j&1}
  preorders+=all((i,k) in relation for i in V for j in V for k in V if (i,j) in relation and (j,k) in relation)
 assert all(seen),('incomplete coverage',len(seen)-sum(seen))
 return {'relevant_arcs':len(arcs),'permutations_per_representative':len(perms),
         'labeled_graphs':sum(seen),'disjoint_isomorphism_classes':len(cores),
         'preorder_representative_count':preorders,'orbit_size_histogram':dict(sorted(Counter(sizes).items()))}

def scaling_and_moments(family):
 assert 2*factorial(2)**2==8 and 3*factorial(1)*factorial(3)==18
 # Independently substitute A=B+C in each universal-cloud moment.
 transformed=[]
 for p in MOMENTS['four-active']:
  q=defaultdict(Fraction)
  for (a,b),c in p.items():
   assert a in (0,1)
   if a==0:q[0,b]+=c
   else:q[1,b]+=c;q[0,b+1]+=c
  transformed.append(dict(q))
 assert transformed==MOMENTS['four-sink']
 return {'Gk':'k! gamma_k for k=1,2,3',
         'identity':'2G2^2 - 3G1G3 = 8(gamma2^2 - (9/4)gamma1 gamma3)',
         'moment_variable_at_index_10':'A' if family=='four-active' else 'C',
         'moment_variable_at_index_11':'B',
         'moment_substitution':'E1=A+B; 2E2=2AB+B^2; 6E3=3AB^2+B^3' if family=='four-active' else 'A=B+C; E1=C+2B; 2E2=2BC+3B^2; 6E3=3CB^2+4B^3',
         'scope':'all-cloud upper E3 boundary' if family=='four-active' else 'sufficient enlarged upper-E3 cone for at most four positive sinks; no sharpness or equivalence claim'}

if __name__=='__main__':
 start=time.time()
 if len(sys.argv)<2 or sys.argv[1] not in CONFIG:raise SystemExit(__doc__)
 family=sys.argv[1];cfg=CONFIG[family]
 source=Path(sys.argv[2]) if len(sys.argv)>2 else Path(__file__).resolve().parent.parent/'certificate-data'
 if not (source/cfg['catalog']).is_file() or not (source/cfg['directory']).is_dir():raise SystemExit('Provide an explicit source containing '+cfg['catalog']+' and '+cfg['directory'])
 destination=Path(sys.argv[3]) if len(sys.argv)>3 else Path(__file__).with_name(family+'-receipt.json')
 workers=int(sys.argv[4]) if len(sys.argv)>4 else 4
 assert workers>=1
 cores=[]
 for line in (source/cfg['catalog']).read_text().splitlines():
  code,*rows=map(int,line.split());cores.append((code,tuple(rows)))
 assert len(cores)==cfg['classes']
 files=list((source/cfg['directory']).glob('certificate_*.json'))
 assert {p.name for p in files}=={f'certificate_{i}.json' for i in range(len(cores))}
 print('Checking',family,':',len(cores),'exact certificates',flush=True)
 records=[]
 with ProcessPoolExecutor(max_workers=workers) as pool:
  jobs=((str(source),family,i,rows) for i,(_,rows) in enumerate(cores))
  for record in pool.map(check_one,jobs,chunksize=16):
   records.append(record)
   if len(records)%1000==0:print('Verified',len(records),'in',round(time.time()-start,3),'seconds',flush=True)
 print('Checking exhaustive disjoint permutation coverage',flush=True)
 coverage=check_coverage(cores,family)
 squares=sum(r['squares'] for r in records);empty=sum(r['empty'] for r in records)
 if 'expected_squares' in cfg:assert squares==cfg['expected_squares']
 if 'expected_empty' in cfg:assert empty==cfg['expected_empty']
 lengths=Counter()
 for r in records:
  lengths.update(r['square_length_histogram'])
 manifest_digest=hashlib.sha256('\n'.join(f"{r['id']}:{r['certificate_sha256']}" for r in records).encode()).hexdigest()
 receipt={'pass':True,'family':family,'verifier':'standalone Python standard library, independent matching witnesses, exact Fraction arithmetic, no producer imports',
          'certificate_count':len(records),'positive_rational_square_count':squares,
          'square_length_histogram':dict(sorted(lengths.items())),
          'empty_certificate_count':empty,'coefficientwise_nonnegative_target_count':sum(r['coefficient_positive'] for r in records),
          'all_exact_remainders_coefficientwise_nonnegative':True,
          'positive_remainder_term_count':sum(r['positive_remainder_terms'] for r in records),
          'zero_remainder_count':sum(r['positive_remainder_terms']==0 for r in records),
          'coverage':coverage,'scaling':scaling_and_moments(family),
          'inactive_tail_exponents_absent_from_targets_and_certificates':True if family=='four-active' else None,
          'certificate_manifest_sha256':manifest_digest,
          'catalog_sha256':hashlib.sha256((source/cfg['catalog']).read_bytes()).hexdigest(),
          'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'seconds':round(time.time()-start,3)}
 destination.write_text(json.dumps(receipt,indent=2)+'\n')
 destination.with_name(family+'-certificate-manifest.json').write_text(json.dumps(records,indent=2)+'\n')
 print(json.dumps(receipt,indent=2),flush=True)
