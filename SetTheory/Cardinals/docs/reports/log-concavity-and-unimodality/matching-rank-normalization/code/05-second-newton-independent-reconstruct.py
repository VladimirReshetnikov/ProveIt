"""Independent Hall-support reconstruction of the rooted-core Schur certificate.

No producer code is imported. Hall's subset criterion supplies endpoint counts;
q is reconstructed by counting unordered row-type triples, not by the author's
inclusion-exclusion formula. The supplied inverse is checked by multiplication.
"""
from pathlib import Path
from itertools import combinations,combinations_with_replacement,permutations,product
from functools import lru_cache
from collections import Counter
from math import comb
import sympy as s
import hashlib,json,time,sys
ROOT=Path(__file__).resolve().parent.parent
OUT=Path(__file__).resolve().parent
n=s.Symbol('n',positive=True)
Ns=s.symbols('N1:8')
p1,p2,m1,m2,t1,t2,q=s.symbols('p1 p2 m1 m2 t1 t2 q')

def need(condition,message):
 if not condition:raise RuntimeError(message)

@lru_cache(None)
def hall(rows):
 """Rows have equal size to the selected column set; masks label its columns."""
 for size in range(1,len(rows)+1):
  for chosen in combinations(rows,size):
   union=0
   for mask in chosen:union|=mask
   if union.bit_count()<size:return False
 return True

@lru_cache(None)
def minor_count(columns):
 return sum(hall(tuple(sum((1<<j) for j,c in enumerate(columns) if c>>i&1) for i in aset)) for aset in combinations(range(3),len(columns)))

BASES=tuple(ms for ms in combinations_with_replacement(range(1,8),3) if hall(ms))
need(len(BASES)==51,'Hall basis count')

@lru_cache(None)
def falling_choose(x,j):
 v=s.Integer(1)
 for i in range(j):v*=x-i
 return s.expand(v/s.factorial(j))

@lru_cache(None)
def endpoint(core,columns):
 """Polynomial weighted count of row supports for fixed selected columns."""
 degree=len(columns);answer=0
 for ca in range(min(3,degree)+1):
  for aset in combinations(range(3),ca):
   arows=tuple(sum(1<<j for j,(kind,v) in enumerate(columns) if ((core[v] if kind=='B' else v)>>i)&1) for i in aset)
   for ls in combinations_with_replacement(range(1,8),degree-ca):
    lrows=tuple(sum(1<<j for j,(kind,v) in enumerate(columns) if kind=='B' and mask>>v&1) for mask in ls)
    if not hall(arows+lrows):continue
    weight=s.Integer(1)
    for mask,mult in Counter(ls).items():weight*=falling_choose(Ns[mask-1],mult)
    answer+=weight
 return s.expand(answer)

def profiles():
 # Orbit partition by full S3 x S2 action on triples with distinguished first column.
 allcores=set(product(range(8),repeat=3)); reps=set()
 while allcores:
  core=min(allcores); orbit=set()
  for perm in permutations(range(3)):
   mapped=tuple(sum(((v>>i)&1)<<perm[i] for i in range(3)) for v in core)
   orbit.add(mapped);orbit.add((mapped[0],mapped[2],mapped[1]))
  allcores-=orbit
  nonzero=[v for v in orbit if v[0] in (1,3,7)]
  if nonzero:reps.add(min(nonzero))
 out=sorted(reps)
 need(Counter(v[0] for v in out)=={1:24,3:24,7:13},'rooted orbit counts')
 return out

RDATA=json.loads((ROOT/'core_R_block_inverses.json').read_text())
@lru_cache(None)
def rblock(J):
 data=RDATA[str(J)];masks=[p+1 for p in data['pivots']];E=n+J.bit_count()
 rv=s.Matrix([n*S.bit_count()+minor_count((J,S)) for S in masks])
 ar=s.Matrix(len(masks),len(masks),lambda i,j:4*rv[i]*rv[j]-5*E*(n*minor_count((masks[i],masks[j]))+minor_count((J,masks[i],masks[j]))))
 inv=s.Matrix([[s.sympify(v,locals={'n':n}) for v in row] for row in data['inverse']])
 for v in ar*inv-s.eye(len(masks)):need(s.cancel(v)==0,('inverse failed',J))
 det=s.factor(ar.det(method='domain-ge'))
 expected={1:6250*n**4*(n+1)**8,3:15625*n**4*(n+2)**7*(2*n*n+4*n+3),7:31250*n**3*(n+2)**2*(n+3)**6*(2*n*n+7*n+9)}[J]
 need(s.expand(det-expected)==0,('determinant failed',J))
 return masks,E,rv,inv

@lru_cache(None)
def compressed_column(J,C,which):
 pp,mm,tt=(p1,m1,t1) if which==1 else (p2,m2,t2)
 masks,E,rv,inv=rblock(J)
 x=pp+n*C.bit_count()+mm*J.bit_count()-tt*(J&C).bit_count()+minor_count((J,C))
 yy=s.Matrix([pp*S.bit_count()+n*minor_count((C,S))+mm*minor_count((J,S))-tt*(minor_count((J,S))+minor_count((C,S))-minor_count((J|C,S)))+minor_count((J,C,S)) for S in masks])
 return x,4*x*rv-5*E*yy

NV=sum(Ns[i-1] for i in range(1,8) if i&1)
M1=sum(Ns[i-1] for i in range(1,8) if i&2)
M2=sum(Ns[i-1] for i in range(1,8) if i&4)
T1=Ns[2]+Ns[6];T2=Ns[4]+Ns[6]
SUB={n:NV,m1:M1,m2:M2,t1:T1,t2:T2,p1:NV*M1-T1*(T1+1)/2,p2:NV*M2-T2*(T2+1)/2}

def check_endpoints():
 checked=0
 for J in (1,3,7):
  rblock(J)
  for C in range(8):
   core=(J,C,0);masks,E,rv,inv=rblock(J);x,u=compressed_column(J,C,1)
   need(s.expand(x.subs(SUB)-endpoint(core,(('B',0),('B',1))))==0,('pair formula',J,C));checked+=1
   for S in range(1,8):
    rr=n*S.bit_count()+minor_count((J,S))
    need(s.expand(rr.subs(SUB)-endpoint(core,(('B',0),('R',S))))==0,('R pair',J,S));checked+=1
    yy=p1*S.bit_count()+n*minor_count((C,S))+m1*minor_count((J,S))-t1*(minor_count((J,S))+minor_count((C,S))-minor_count((J|C,S)))+minor_count((J,C,S))
    need(s.expand(yy.subs(SUB)-endpoint(core,(('B',0),('B',1),('R',S))))==0,('triple formula',J,C,S));checked+=1
    for T in range(S,8):
     zz=n*minor_count((S,T))+minor_count((J,S,T))
     need(s.expand(zz.subs(SUB)-endpoint(core,(('B',0),('R',S),('R',T))))==0,('R triple',J,S,T));checked+=1
   if J==1:
    # The seventh feature column is the claimed combination of the first six.
    coeff=[-1,-1,1,-1,1,1]
    rr7=n*3+minor_count((J,7))
    need(s.expand(rr7-sum(c*r for c,r in zip(coeff,rv)))==0,'r feature relation')
    yy7=p1*3+n*minor_count((C,7))+m1*minor_count((J,7))-t1*(minor_count((J,7))+minor_count((C,7))-minor_count((J|C,7)))+minor_count((J,C,7))
    yy=(4*x*rv-u)/(5*E)
    need(s.cancel(yy7-sum(c*y for c,y in zip(coeff,yy)))==0,'cross feature relation')
 return checked

@lru_cache(None)
def diagonal(J,C,which):
 x,u=compressed_column(J,C,which);_,E,_,inv=rblock(J)
 return s.cancel((4*x*x-(u.T*inv*u)[0])/(5*E))

def rebuild(core,metadata):
 J,C1,C2=core;_,E,_,inv=rblock(J)
 need(isinstance(metadata['integer_multiplier'],int) and metadata['integer_multiplier']>0,'nonpositive scalar multiplier')
 x,u=compressed_column(J,C1,1);xx,v=compressed_column(J,C2,2)
 aa=diagonal(J,C1,1);bb=diagonal(J,C2,2)
 cc=s.cancel((4*x*xx-5*E*q-(u.T*inv*v)[0])/(5*E))
 den=s.sympify(metadata['clearing_denominator'],locals={'n':n})
 need(all(c>=0 for c in s.Poly(den,n).all_coeffs()) and den.subs(n,1)>0,'denominator positive')
 cleared=[]
 for value in (aa,bb,cc):
  num=s.cancel(value*den)
  need(s.denom(num)==1,'denominator not cleared')
  sub=dict(SUB);sub[q]=endpoint(core,(('B',0),('B',1),('B',2)))
  cleared.append(s.Poly(s.expand(num.subs(sub)),Ns))
 poly=(cleared[0]*cleared[1]-cleared[2]**2)*metadata['integer_multiplier']
 need(poly.total_degree()==metadata['degree'],'degree mismatch')
 need(len(poly.terms())==metadata['base_terms'],'base term mismatch')
 out={e:int(c) for e,c in poly.terms()}
 need(all(s.Integer(out[e])==c for e,c in poly.terms()),'noninteger normalization')
 return out

def translate(poly,basis):
 # Translate each distinct coordinate by its full multiplicity, in descending
 # coordinate order; this differs from the producer's repeated +1 prefix cache.
 out=poly
 for i,b in sorted(Counter(x-1 for x in basis).items(),reverse=True):
  new={}
  for ex,c in out.items():
   for j in range(ex[i]+1):
    ee=list(ex);ee[i]=j;ee=tuple(ee)
    new[ee]=new.get(ee,0)+c*comb(ex[i],j)*b**(ex[i]-j)
  out={e:c for e,c in new.items() if c}
 return out

def verify_profile(core):
 path=ROOT/('core_schur_%s_%s_%s.json'%core)
 if not path.exists():return None
 data=json.loads(path.read_text());need(data['core_columns']==list(core),'profile mismatch')
 need(data['basis_profiles_checked']==51 and data['negative'] is None,'incomplete producer profile')
 records={tuple(v['basis']):v for v in data['records']}
 need(set(records)==set(BASES),'basis list differs')
 start=time.time();poly=rebuild(core,data);entries=0
 for basis in BASES:
  shifted=translate(poly,basis);record=records[basis]
  need(all(c>=0 for c in shifted.values()),('negative certificate',core,basis))
  need(len(shifted)==record['terms'],'term count mismatch')
  need(min(shifted.values(),default=0)==record['minimum'],'minimum mismatch')
  text=json.dumps([[list(e),c] for e,c in sorted(shifted.items())],separators=(',',':'))
  need(hashlib.sha256(text.encode()).hexdigest()==record['sha256'],('hash mismatch',core,basis))
  entries+=len(shifted)
 out={'core':list(core),'all_pass':True,'basis_instances':51,'coefficient_entries':entries,'producer_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'seconds':time.time()-start}
 (OUT/('replay_%s_%s_%s.json'%core)).write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out),flush=True);return out

if __name__=='__main__':
 if len(sys.argv)>1 and sys.argv[1]=='endpoints':
  start=time.time();count=check_endpoints();out={'all_pass':True,'endpoint_polynomial_checks':count,'R_inverses_checked':3,'basis_count':len(BASES),'rooted_core_counts':dict(Counter(v[0] for v in profiles())),'seconds':time.time()-start}
  (OUT/'endpoint_audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));sys.exit(0)
 cores=profiles()
 if len(sys.argv)==4:cores=[tuple(map(int,sys.argv[1:]))]
 for core in cores:
  target=OUT/('replay_%s_%s_%s.json'%core)
  if '--resume' not in sys.argv or not target.exists():verify_profile(core)
 allreplays=[]
 for core in profiles():
  p=OUT/('replay_%s_%s_%s.json'%core)
  if p.exists():allreplays.append(json.loads(p.read_text()))
 out={'all_pass':len(allreplays)==61,'profiles':len(allreplays),'basis_instances':sum(v['basis_instances'] for v in allreplays),'coefficient_entries':sum(v['coefficient_entries'] for v in allreplays),'records':allreplays}
 (OUT/'independent_manifest.json').write_text(json.dumps(out,indent=2)+'\n')
