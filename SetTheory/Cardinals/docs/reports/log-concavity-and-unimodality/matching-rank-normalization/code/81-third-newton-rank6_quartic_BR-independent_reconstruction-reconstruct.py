"""Independent BR replay: assignment supports, pair-profile q_BR, rational
Gauss-Jordan Schur reduction and ascending repeated-unit translations.
No producer module or precomputed inverse is imported.
"""
from pathlib import Path
from itertools import product,permutations,combinations,combinations_with_replacement
from functools import lru_cache
from collections import Counter
from math import comb
import hashlib,json,time,sys
import sympy as s
ROOT=Path(__file__).resolve().parent.parent;OUT=Path(__file__).resolve().parent
n=s.Symbol('n',positive=True);p1,p2,m1,m2,t1,t2,q=s.symbols('p1 p2 m1 m2 t1 t2 q');Ns=s.symbols('N1:8')
def need(b,msg):
 if not b:raise ArithmeticError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
@lru_cache(None)
def matches(rows):
 return any(all(rows[i]&(1<<v[i]) for i in range(len(rows))) for v in permutations(range(len(rows))))
@lru_cache(None)
def cnt(columns):
 # Count sets of A endpoints, not their distinct assignments.
 return len({tuple(sorted(rows)) for rows in permutations(range(3),len(columns)) if all(c&(1<<i) for c,i in zip(columns,rows))})
BASES=tuple(z for z in combinations_with_replacement(range(1,8),3) if matches(z));need(len(BASES)==51,'basis count')
@lru_cache(None)
def weight(types):
 z=s.Integer(1)
 for mask,mult in Counter(types).items():
  v=s.Integer(1)
  for j in range(mult):v*=Ns[mask-1]-j
  z*=v/s.factorial(mult)
 return s.expand(z)
QL=s.expand(sum(weight(z) for z in BASES));PAIRS={}
for a,b in combinations_with_replacement(range(1,8),2):
 profile=0
 for leave in range(3):
  j,k=[i for i in range(3) if i!=leave]
  if (a&(1<<j) and b&(1<<k)) or (a&(1<<k) and b&(1<<j)):profile|=1<<leave
 if profile:PAIRS[profile]=PAIRS.get(profile,0)+weight((a,b))
PAIRS={k:s.expand(v) for k,v in PAIRS.items()}
@lru_cache(None)
def qpair(U,J,C1,C2):
 core=(J,C1,C2);v=U.bit_count()*QL
 for mask,w in PAIRS.items():
  union=0
  for i in range(3):
   if mask&(1<<i):union|=core[i]
  v+=w*cnt((U,union))
 D=sum(1<<i for i in range(3) if cnt((U,*(core[j] for j in range(3) if j!=i))))
 return s.expand(v+sum(Ns[a-1] for a in range(1,8) if a&D))
@lru_cache(None)
def endpoint(core,columns):
 degree=len(columns);v=0
 for ac in range(min(3,degree)+1):
  for aset in combinations(range(3),ac):
   arows=tuple(sum(1<<j for j,(kind,z) in enumerate(columns) if (core[z] if kind=='B' else z)&(1<<i)) for i in aset)
   for ls in combinations_with_replacement(range(1,8),degree-ac):
    lrows=tuple(sum(1<<j for j,(kind,z) in enumerate(columns) if kind=='B' and a&(1<<z)) for a in ls)
    if matches(arows+lrows):v+=weight(ls)
 return s.expand(v)
def image(a,p):return sum(1<<p[i] for i in range(3) if a&(1<<i))
def profiles():
 out=[]
 for U,cats in [(1,(0,2,4,6)),(3,(0,1,4,5)),(7,(0,1,2,3,4))]:
  group=[(0,1,2)] if U==3 else ([(0,1,2),(0,2,1)] if U==1 else list(permutations(range(3))))
  domain=set(product(cats,repeat=3));remaining=set(domain)
  while remaining:
   core=min(remaining);orbit=set()
   for p in group:
    z=tuple(image(a,p) for a in core)
    if U==7:z=tuple(3 if a.bit_count()>=2 else a for a in z)
    orbit.add(z);orbit.add((z[0],z[2],z[1]))
   need(orbit<=domain,'orbit closure');remaining-=orbit;out.append((U,*min(orbit)))
 need(Counter(v[0] for v in out)=={1:24,3:40,7:25},'orbit counts')
 return sorted(out)
@lru_cache(None)
def rblock(U,J):
 types={1:(2,4,6),3:(1,4,5),7:(1,2,3,4)}[U]
 E=n*U.bit_count()+cnt((J,U));rr=s.Matrix([n*cnt((U,a))+cnt((J,U,a)) for a in types]);k=len(types)
 A=s.Matrix(k,k,lambda i,j:3*rr[i]*rr[j]-4*E*n*cnt((U,types[i],types[j])))
 M=[list(A.row(i))+[s.Integer(i==j) for j in range(k)] for i in range(k)];det=s.Integer(1)
 for col in range(k):
  pivot=next((i for i in range(col,k) if s.cancel(M[i][col])!=0),None);need(pivot is not None,'R singular')
  if pivot!=col:M[pivot],M[col]=M[col],M[pivot];det=-det
  z=s.cancel(M[col][col]);det=s.cancel(det*z);M[col]=[s.cancel(v/z) for v in M[col]]
  for i in range(k):
   if i!=col and M[i][col]!=0:
    c=M[i][col];M[i]=[s.cancel(M[i][j]-c*M[col][j]) for j in range(2*k)]
 inv=s.Matrix([row[k:] for row in M])
 for z in A*inv-s.eye(k):need(s.cancel(z)==0,'inverse identity')
 return types,E,rr,inv,s.factor(det)
@lru_cache(None)
def column(U,J,C,i):
 pp,mm,tt=(p1,m1,t1) if i==1 else (p2,m2,t2);types,E,rr,inv,det=rblock(U,J)
 x=pp*U.bit_count()+n*cnt((C,U))+mm*cnt((J,U))-tt*(cnt((J,U))+cnt((C,U))-cnt((J|C,U)))+cnt((J,C,U))
 z=s.Matrix([pp*cnt((U,a))+n*cnt((C,U,a))+mm*cnt((J,U,a))-tt*(cnt((J,U,a))+cnt((C,U,a))-cnt((J|C,U,a))) for a in types])
 return x,z
NV=sum(Ns[a-1] for a in range(1,8) if a&1);M1=sum(Ns[a-1] for a in range(1,8) if a&2);M2=sum(Ns[a-1] for a in range(1,8) if a&4);T1=Ns[2]+Ns[6];T2=Ns[4]+Ns[6]
SUB={n:NV,m1:M1,m2:M2,t1:T1,t2:T2,p1:NV*M1-T1*(T1+1)/2,p2:NV*M2-T2*(T2+1)/2}
@lru_cache(None)
def diagonal(U,J,C,i):
 _,E,rr,inv,_=rblock(U,J);x,z=column(U,J,C,i);v=3*x*rr/(4*E)-z
 return s.cancel(3*x*x/(4*E)-(v.T*(4*E*inv)*v)[0])
def rebuild(core,record):
 U,J,C1,C2=core;_,E,rr,inv,det=rblock(U,J)
 need(s.expand(det-s.sympify(record['R_determinant'],locals={'n':n}))==0,'R determinant')
 x,z=column(U,J,C1,1);y,w=column(U,J,C2,2);v=3*x*rr/(4*E)-z;vv=3*y*rr/(4*E)-w
 off=s.cancel(3*x*y/(4*E)-q-(v.T*(4*E*inv)*vv)[0]);den=s.sympify(record['denominator'],locals={'n':n})
 need(all(c>=0 for c in s.Poly(den,n).all_coeffs()) and den.subs(n,1)>0,'positive clearing denominator')
 sub=dict(SUB);sub[q]=qpair(*core);arr=[]
 for f in (diagonal(U,J,C1,1),diagonal(U,J,C2,2),off):
  raw=s.Poly(s.cancel(f*den),n,p1,p2,m1,m2,t1,t2,q,domain=s.QQ)
  arr.append(s.Poly(s.expand(raw.as_expr().subs(sub)),Ns,domain=s.QQ))
 factor=record['multiplier'];need(type(factor) is int and factor>0,'positive scalar')
 target=(arr[0]*arr[1]-arr[2]**2)*factor
 need(target.total_degree()==record['degree'] and len(target.terms())==record['base_terms'],'polynomial metadata')
 out={e:int(c) for e,c in target.terms()};need(all(s.Integer(out[e])==c for e,c in target.terms()),'integer coefficients')
 return out
def unit_shift(poly,i):
 out={}
 for e,c in poly.items():
  for j in range(e[i]+1):
   z=list(e);z[i]=j;z=tuple(z);out[z]=out.get(z,0)+c*comb(e[i],j)
 return {e:c for e,c in out.items() if c}
def verify_profile(core):
 path=ROOT/('br_%s_%s_%s_%s.json'%core);r=json.loads(path.read_text());need(r['core']==list(core),'core identity')
 need(r['basis_count']==51 and r['negative'] is None,'complete profile')
 expected={tuple(v['basis']):v for v in r['records']};need(set(expected)==set(BASES),'basis coverage')
 start=time.time();cache={():rebuild(core,r)};records=[];total=0
 for basis in BASES:
  for j in range(1,4):
   prefix=basis[:j]
   if prefix not in cache:cache[prefix]=unit_shift(cache[prefix[:-1]],prefix[-1]-1)
  p=cache[basis];e=expected[basis];need(all(c>=0 for c in p.values()),('negative',core,basis))
  need(len(p)==e['terms'] and min(p.values(),default=0)==e['minimum'],'translated statistics')
  text=json.dumps([[list(ex),c] for ex,c in sorted(p.items())],separators=(',',':'));h=hashlib.sha256(text.encode()).hexdigest();need(h==e['sha256'],('hash',core,basis))
  records.append({'basis':list(basis),'terms':len(p),'sha256':h});total+=len(p)
 out={'core':list(core),'all_pass':True,'basis_instances':51,'coefficient_entries':total,'producer_record_sha256':digest(path),'q_BR_method':'pair-profile formula','records':records,'seconds':time.time()-start}
 (OUT/('replay_%s_%s_%s_%s.json'%core)).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'}),flush=True);return out
def check_endpoints():
 checks=0
 for core in profiles():
  U,J,C1,C2=core;cc=(J,C1,C2)
  need(qpair(*core)==endpoint(cc,(('B',0),('B',1),('B',2),('R',U))),('qBR',core));checks+=1
  types,E,rr,_,_=rblock(U,J)
  need(s.expand(E.subs(SUB)-endpoint(cc,(('B',0),('R',U))))==0,'E');checks+=1
  for i,C in [(1,C1),(2,C2)]:
   x,z=column(U,J,C,i);need(s.expand(x.subs(SUB)-endpoint(cc,(('B',0),('R',U),('B',i))))==0,'x');checks+=1
   for j,S in enumerate(types):
    need(s.expand(z[j].subs(SUB)-endpoint(cc,(('B',0),('R',U),('B',i),('R',S))))==0,'z');checks+=1
  for i,S in enumerate(types):
   need(s.expand(rr[i].subs(SUB)-endpoint(cc,(('B',0),('R',U),('R',S))))==0,'r');checks+=1
   for T in types:
    need(s.expand((n*cnt((U,S,T))).subs(SUB)-endpoint(cc,(('B',0),('R',U),('R',S),('R',T))))==0,'R pair');checks+=1
 out={'all_pass':True,'endpoint_polynomial_checks':checks,'q_BR_pair_profile_checks':89,'basis_count':51,'profile_counts':dict(Counter(p[0] for p in profiles()))};(OUT/'endpoint_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
if __name__=='__main__':
 if sys.argv[1:] and sys.argv[1]=='endpoints':check_endpoints()
 elif len(sys.argv)==5:verify_profile(tuple(map(int,sys.argv[1:])))
 else:
  for core in profiles():
   if len(sys.argv)==2 and core[0]!=int(sys.argv[1]):continue
   verify_profile(core)
