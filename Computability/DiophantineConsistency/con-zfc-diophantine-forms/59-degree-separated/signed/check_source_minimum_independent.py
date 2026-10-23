#!/usr/bin/env python3
"""Independent signed-source identities and bounded stress diagnostics.
Uses inert kernel/circuit metadata, never imports the construction program.
"""
import collections,fractions,hashlib,json,math
from pathlib import Path
R=Path(__file__).resolve().parent

def require(v,s):
 if not v:raise ValueError(s)
def add(a,b,k=1):
 z=dict(a)
 for m,c in b.items():z[m]=z.get(m,0)+k*c
 return {m:c for m,c in z.items() if c}
def mul(a,b):
 z=collections.defaultdict(int)
 for m,c in a.items():
  for n,d in b.items():z[tuple(x+y for x,y in zip(m,n))]+=c*d
 return {m:c for m,c in z.items() if c}
def cn(c):return {(0,)*8:c}if c else {}
def va(i):m=[0]*8;m[i]=1;return {tuple(m):1}
def sc(a,k):return {m:c*k for m,c in a.items() if c*k}
def sq(a):return mul(a,a)
def identities():
 A,D,C,N,U,P,T,ell=[va(i) for i in range(8)]
 G=add(add(add(mul(A,sq(U)),mul(D,U)),C),P)
 left=add(sc(mul(A,G),2),mul(sq(A),sq(U)),-1)
 right=add(add(sq(add(mul(A,U),D)),sc(mul(A,add(C,P)),2)),sq(D),-1)
 require(left==right,'half-quadratic completion identity')
 S=add(add(U,ell,-1),mul(N,add(sc(G,2),T)))
 a=sc(mul(N,A),2);b=add(sc(mul(N,D),2),cn(1));c=add(add(sc(mul(N,add(C,P)),2),mul(N,T)),ell,-1)
 require(S==add(add(mul(a,sq(U)),mul(b,U)),c),'signed source quadratic expansion')
 require(add(sc(mul(a,S),4),sq(add(sc(mul(a,U),2),b)),-1)==add(sc(mul(a,c),4),sq(b),-1),'full source minimum identity')
 return 3

def coeff(row,ports):return sum(t['coefficient']*math.prod(p**e for p,e in zip(ports,t['powers'])) for t in row)
def main():
 identities_count=identities()
 data=json.loads((R/'split/split_code.json').read_text());kernels=json.loads((R/'split/split_kernels.json').read_text())
 circuits={}
 for compact in [False,True]:
  fn='generated/signed_coprime_'+('compact_' if compact else '')+'split_crt.json'
  doc=json.loads((R/fn).read_text())
  require(doc['compact_calibration']==compact,'wrong calibration branch')
  require((doc['W'],doc['Kh'],doc['E'],doc['Hpop'],doc['positivity_pad_exponent'])==(116,2161,2279,2418,2161 if compact else 2162),'source exponents changed')
  require((doc['base_scale_exponent'],doc['threshold_scale_exponent'],doc['threshold_b_power'],doc['threshold_epsilon_power'],doc['threshold_B_power'])==(2134940,17079510,int(not compact),int(compact),1201),'threshold calibration changed')
  require(hashlib.sha256((R/'split/split_code.json').read_bytes()).hexdigest()==kernels['code_sha256']==doc['split_code_sha256'],'code binding mismatch')
  counts=collections.Counter(n['kind']for n in doc['nodes']if n['kind']in ['mul','add','sub'])
  require(dict(counts)==doc['operation_counts']=={'mul':326 if compact else 328,'add':169,'sub':23},'binary operation ledger')
  require(sum(counts.values())==doc['operations']==(518 if compact else 520),'total operation ledger')
  ni=doc['named_nodes']['N'];uses=[]
  for i,n in enumerate(doc['nodes']):
   if n.get('left')==ni or n.get('right')==ni:uses.append(n)
   if n['kind']in ['mul','add','sub']:require(0<=n['left']<i and 0<=n['right']<i,'DAG topology')
  require(len(uses)==1 and uses[0]=={'kind':'mul','left':ni,'right':ni},'N must be consumed only by its square')
  circuits[fn]={'sha256':hashlib.sha256((R/fn).read_bytes()).hexdigest(),'operations':sum(counts.values()),'signed_threshold_only_squared':True}
 for k,a in enumerate([1719,2027,1929]):require(max(x['exponent'] for x in kernels['kernels'][k]['terms'])==a,'kernel degree')
 lead=max(kernels['kernels'][2]['terms'],key=lambda x:x['exponent']);require(lead['coefficient']==[{'powers':[0,0,0,0],'coefficient':1}],'positive leading term')
 F=fractions.Fraction
 require(F(4,8192**2)+F(2,8192)<F(1,2),'quadratic padding constants')
 require(F(24,8192)<F(1,256),'bounded-input source constants')
 require(F(994,8192)<F(1,8),'digit coefficient constant')
 require(2*2027-1929==2125,'quadratic loss exponent')
 for pad_exponent in [2161,2162]:require(pad_exponent-2125>=36 and pad_exponent-1719>=442,'minimum degree gaps')
 # Threshold identity in independent formal exponents kappa,k.
 left=(2279+139,2*(2279+139)-30,-20)
 right=(2*(8+1201),2*(1+2*1201),-20)
 require(left==right==(2418,4806,-20),'binary population threshold identity')
 compact_left=(2279+139,2*(2279+139)-31,-21)
 compact_right=(2*(8+1201),4*1201+1,-21)
 require(compact_left==compact_right==(2418,4805,-21),'compact odd-parity binary population threshold identity')
 require(F(1,256)+F(1,256)+F(2,256)==F(1,64),'compact block constant')
 require(2*1201+1==2403 and 2403+15==2418<2*2279,'N^2 and block exponents')
 stresses=0;negative_g=0
 for ports in [(3,5,2,4),(31,127,10,45)]:
  scalar=[[(r['exponent'],coeff(r['coefficient'],ports))for r in k['terms']]for k in kernels['kernels']]
  bound=1+max(abs(c)for k in scalar for e,c in k)
  for eps in [-3,-2,-1,1,2,3]:
   b=2*eps*eps;B=8192*bound*b*b;N0=B**117
   ell=sum(B**w for w in data['weights']);targets=sum(B**q for q in data['targets'])
   ks=[sum(c*B**e for e,c in k)for k in scalar]
   require(ks[2]>0,'evaluated quadratic coefficient')
   # Exact minimizer of S in the U coordinate, rounded down.
   a=2*N0*ks[2];lin=2*N0*ks[1]+1;vertex=(-lin)//(2*a)
   candidates=[-2*ell,-ell,-ell+vertex-1,-ell+vertex,-ell+vertex+1,0,1,b*B**116-1]
   mask=N0-1-(b-1)*ell;Tc=mask+N0*(B-2)*targets
   require(0<mask<N0 and Tc>0,'mask positivity diagnostic')
   for pad_exponent in [2161,2162]:
    pad=B**pad_exponent
    for g in candidates:
     U=ell+g;Gp=ks[2]*U*U+ks[1]*U+ks[0]+pad;J=2*Gp+targets;S=g+N0*J
     require(4*Gp>B**1929*U*U+2*pad,'uniform quadratic minorant diagnostic')
     require(S>0,'signed source positivity diagnostic');stresses+=1;negative_g+=int(g<0)
    g=b*B**116-1;U=ell+g;J=2*(ks[2]*U*U+ks[1]*U+ks[0]+pad)+targets;S=g+N0*J
    if pad_exponent==2161:
     require(64*J<B**2162 and 32*S<B**2279 and 64*Tc<B**2279 and S+Tc<B**2279,'compact block range diagnostic')
    else:require(S+Tc<4*B**2279<=2*b*B**2279,'sharp retained-block range diagnostic')
 result={'status':'PASS','formal_quadratic_identities':identities_count,'exact_majorant_and_exponent_checks':True,'signed_source_stress_cases':stresses,'negative_g_stress_cases':negative_g,'tested_near_exact_quadratic_minima':True,'code_sha256':kernels['code_sha256'],'circuits':circuits,'scope':'Universal symbolic square-completion identities and exact rational/exponent inequalities for both pad2162/scaled and pad2161/compact variants. Numeric source stress cases are diagnostics; the all-integer proof is INDEPENDENT_SOURCE_REVIEW.md. The final norm/ratio compiler is not re-proved by this checker.'}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
