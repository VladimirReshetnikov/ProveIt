#!/usr/bin/env python3
"""Freshly reconstructed own checker after reset; no upstream execution.

Large outer checks never form 2**p. Saved source rows are compared as data
only. Every integer actually materialized has explicitly bounded size.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PINS={
'FIXED_RAW_UNIVERSAL_76_PROOF.md':'75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
'HALF_PARAMETER_PELL_92_PROOF.md':'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
'complete82_auxiliary_square_product_chart.json':'7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a',
'complete82_auxiliary_square_product_chart.md':'10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9',
'complete82_auxiliary_square_product_chart.py':'5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc',
'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
'review_complete82_auxiliary_square_product_chart.md':'02a12fd0426ad57b7c2bc822bc93266ed6511334e98cfb712cdd9f893d75722c'}
# Literal expectation transcribed from the independently reviewed contract.
# This string is parsed for comparison ONLY. It is never evaluated.
ROWS='''
tau_square * tau_root tau_root
repunit * Bm1 Jrep
q + repunit 1
Lbig * q q
n2 * Lbig q
wn2 * w q
sn2 * s n2
UM * wn2 sn2
R10b + eta zeta
ksn2 * R10b sn2
first_root_base * UM ksn2
first_next + first_root_base R10b
first_product * first_root_base first_next
norm_first - tau_square first_product
R10a + ksn2 eta
R12 + UM sn2
cam2 * R10a R12
D1 + wn2 cam2
gamma_sum + rho sigma
a4 * 4 R12
a4m5 + a4 3
gam * gamma_sum a4m5
R14 + D1 gam
L15 * R14 R14
a_square * R12 R12
A + a_square a4m5
c2 * R10a R10a
Ac2 * A c2
norm_main - L15 Ac2
norm_pair * norm_first norm_main
q_minus_F - q F
q_minus_FZ - q_minus_F Z
C_after_alpha - q_minus_FZ alpha
scaled_t * twice_cell_bits x
marked_rhs - C_after_alpha scaled_t
W - marked_rhs Z
odd_index + scaled_t inner_bits
index_product * delta A
index_rhs + odd_index index_product
difference_multiple * index_rhs R12
exponent_partial + W difference_multiple
modulus_multiple * rho a4m5
exponent_rhs + exponent_partial modulus_multiple
mu2 * exponent_rhs exponent_rhs
kappa2 * index_rhs index_rhs
scaled_kappa2 * A kappa2
norm_input - mu2 scaled_kappa2
norm_triple * norm_pair norm_input
aux_y2 * y_aux y_aux
hpm1 * h UM
index_difference - R10b hpm1
gap_product * repunit q_minus_F
gap + gap_product q_minus_FZ
Lm1 - Lbig 1
rproduct * gap Lm1
qMF * q MF
mask_factor + MC qMF
mask * mask_factor Jrep
r_lhs + rproduct mask
norm_index - index_difference r_lhs
kinner + Kconstant w
innerC * kinner marked_rhs
transport_partial + innerC q_minus_F
local_rhs * transport_quotient repunit
norm_transport - transport_partial local_rhs
auxiliary_Tf_minus_one - auxiliary_Tf 1
auxiliary_c_Tf * R10a auxiliary_Tf_minus_one
auxiliary_R_f2 * r_lhs L16
aux_u_rhs - auxiliary_c_Tf auxiliary_R_f2
H2 * aux_u_rhs aux_u_rhs
aux_square_gap - H2 aux_y2
aux_coefficient_root * i Ac2
R16 * aux_coefficient_root aux_coefficient_root
scaled_f_square * A L16
norm_strong - scaled_f_square R16
L17 * R16 aux_square_gap
norm_aux + L17 aux_y2
norm_four * norm_triple norm_aux
norm_product * norm_four norm_index
all_units * norm_product norm_transport
seven_units * all_units norm_strong
polynomial - seven_units A
'''
WITNESSES='Jrep F alpha transport_quotient L16 h i auxiliary_Tf s w tau_root eta zeta y_aux Z delta rho sigma'.split()
FIXED='Bm1 Kconstant twice_cell_bits inner_bits MC MF'.split()
def need(ok,message):
    if not ok:raise ValueError(message)
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def digest(x):return sha256(stable(x)).hexdigest()
def same(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b

def source_contract():
    for name,pin in PINS.items():need(sha256((ROOT/'source'/name).read_bytes()).hexdigest()==pin,'source pin '+name)
    packet=json.loads((ROOT/'source/complete82_auxiliary_square_product_chart.json').read_text())['packet']
    rows=[[int(x) if x.isdigit() else x for x in line.split()] for line in ROWS.strip().splitlines()]
    need(rows==packet['source'],'all82 row definitions and order')
    need(packet['witnesses']==WITNESSES and packet['fixed_numerals']==FIXED,'witness/fixed interface')
    need(packet['free']==WITNESSES+['x']+FIXED,'free-port order')
    need(packet['ordinary_input']=='x' and packet['output']=='polynomial','input/output')
    need(packet['factors']=='norm_first norm_main norm_input norm_aux norm_index norm_transport norm_strong'.split(),'factors')
    ops=Counter(r[1] for r in rows);need(len(rows)==82 and ops['*']==45 and ops['+']+ops['-']==37,'ledger')
    return dict(status='PASS',rows_compared=82,witnesses=18,M=45,A=37,pins=PINS,upstream_executed=False,saved_schedule_evaluated=False)

# This sparse polynomial engine evaluates only the handwritten identities below,
# never the upstream rows or any previously saved program.
class Poly:
    names='q F Z alpha ellx W K w C e2 eps J MC MF Delta c i Faux U R y P5 L'.split()
    zero=(0,)*len(names)
    def __init__(self,x=0):self.d=x if isinstance(x,dict) else ({self.zero:x} if x else {})
    @classmethod
    def var(cls,name):
        z=list(cls.zero);z[cls.names.index(name)]=1;return cls({tuple(z):1})
    def __add__(self,b):
        if not isinstance(b,Poly):b=Poly(b)
        d=self.d.copy()
        for k,v in b.d.items():d[k]=d.get(k,0)+v
        return Poly({k:v for k,v in d.items() if v})
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.d.items()})
    def __sub__(self,b):return self+-(b if isinstance(b,Poly) else Poly(b))
    def __rsub__(self,b):return Poly(b)+-self
    def __mul__(self,b):
        if not isinstance(b,Poly):b=Poly(b)
        d={}
        for x,u in self.d.items():
            for y,v in b.d.items():
                z=tuple(a+b for a,b in zip(x,y));d[z]=d.get(z,0)+u*v
        return Poly({k:v for k,v in d.items() if v})
    __rmul__=__mul__
    def __pow__(self,n):
        out=Poly(1)
        for _ in range(n):out=out*self
        return out
    def __eq__(self,b):return self.d==(b.d if isinstance(b,Poly) else Poly(b).d)

def symbolic_cuts():
    q,F,Z,alpha,ellx,W,K,w,C,e2,eps,J,MC,MF,Delta,c,i,Faux,U,R,y,P5,L=[Poly.var(n) for n in Poly.names]
    need((q-1)*(q-F)+(q-F-Z)==q*q-q*F-Z,'actual G cut')
    need(q-F-Z-(q-F-2*Z-W-ellx)-ellx==W+Z,'C alpha cut')
    need((q*q-q*(L*(W+Z)+1-eps)-Z)*(q*q-1)+(MC+q*MF)*J==(q*q-q*(L*W+1-eps))*(q*q-1)+(MC+q*MF)*J-(q*q-1)*(1+q*L)*Z,'affine CRT R')
    FF=(K+e2)*C+1-eps
    need((K+w)*C+q-FF-((q-1)+C*(w-e2))==eps,'transport sign')
    S=i*Delta*c*c;V=c*(U-1)-R*Faux;Na=S*S*V*V-(S*S-1)*y*y;Qs=Faux-Delta*i*i*c**4
    full=P5*Na*(Delta*Faux-S*S)-Delta
    need(full==Delta*(P5*Na*Qs-1),'full output')
    return dict(status='PASS',identities=5,full_output_monomials=len(full.d))

def crt(pairs):
    z,m=0,1
    for a,n in pairs:
        need(gcd(m,n)==1,'CRT moduli');z+=m*((a-z)*pow(m,-1,n)%n);m*=n
    return z or m

def outer(a,b,K,MC,MF0,x,r):
    d=5**a;B=1<<d;ell=2*d;I=ell*x+b;t=5**r
    need(r>=a and t>=4*max(I,K.bit_length(),61,16),'outer sizing')
    need(0<MC<B-1 and MC%4==2 and 0<MF0<B-1,'necessary mask conditions')
    MF=MF0+B-1;q=1<<t;N=5**(r-a);J=(q-1)//(B-1);Q=q*q-1;M=(MC+q*MF)*J;W=1<<I;m3=(MC+2*MF)%3
    need(q==B**N and J*(B-1)==q-1,'radix')
    need((q%5,q%7) in ((2,2),(2,4)) and gcd(Q,35)==1,'radix residues')
    need(M%3==m3 and M%4==2,'mask residues')
    if m3:
        eps=1 if m3==2 else -1;e=9 if K%5==1 else 8
        L=K+(1<<e);beta=Q*(1+q*L);AA=Q*(q*q-q*(L*W+1-eps))+M
        need(gcd(beta,t)==1,'A coefficient unit');target=(3*e*pow(2,-1,t)-eps)%t
        Z=crt([(1,4),((AA-target)*pow(beta,-1,t)%t,t)])
        need(1<=Z<=4*t,'A Z bound')
    else:
        eps=1;valid=[h for h in range(1,13) if (1+q*(K+(1<<(5*h))))%5 and (1+q*(K+(1<<(5*h))))%7]
        need(len(valid)>=6,'h choices');h0=valid[0];e=5*h0;L=K+(1<<e);beta=Q*(1+q*L);AA=Q*(q*q-q*L*W)+M;T=t//5
        need(gcd(beta,7*T)==1,'B coefficient unit')
        Z=crt([(1,4),((AA+1)*pow(beta,-1,7)%7,7),((AA-(7*h0-1))*pow(beta,-1,T)%T,T)])
        need(1<=Z<=28*T,'B Z bound')
    F=L*(W+Z)+1-eps;alpha=q-F-2*Z-W-ell*x;G=q*q-q*F-Z;R=G*Q+M
    need(R==AA-beta*Z and R%4==3 and R%3==m3,'actual R')
    need(min(J,F,Z,alpha)>0 and F+Z<q,'positive outer witnesses')
    need(2*q-1<=G<=q*q-q-1 and 0<M<(q-1)*(1+2*q),'mask interval cuts')
    need((2*q-1)*Q<R<q**4-q**3 and R>q**3>100*t,'R interval')
    need(q-F-Z-alpha-ell*x==W+Z,'actual C')
    if m3:
        need((R+eps)%6==0,'integer u');u=(R+eps)//6;p=4*u;n=3*u;yexp=2*u-1
        need(u>=3 and u%2==(eps==-1),'u threshold/parity')
    else:
        need((R+1)%28==0 and R%(t//5)==(7*h0-1)%(t//5),'integer v and residue')
        v=(R+1)//28;p=20*v;n=14*v;yexp=15*v-1;need(v>=2,'v threshold')
    need(p%t==e and 2*n==R+eps,'rank residues')
    need(p>I and p>t+e and yexp>=3*t,'input/scale margins')
    need(p*(p-n)==(yexp+1)*(2*n-p),'exact resonance exponent')
    need((p-t-e)%t==0 and p-t-e>0,'transport positive exponent difference')
    need(pow(2,t,q-1)==1 and pow(2,(p-t)%t,q-1)==1<<e,'transport via verified period')
    return dict(a=a,b=b,K=K if K.bit_length()<30 else 'large:'+str(K.bit_length()),MC=MC,MF0=MF0,x=x,r=r,m3=m3,epsilon=eps,e=e,Z=Z,t=t,R_bits=R.bit_length(),p_bits=p.bit_length(),outer_digest=digest([hex(z) for z in (J,F,alpha,Z,R,p,n,yexp)]))

def outer_checks():
    records=[outer(a,5,K,2,MF0,x,r) for a in (1,2) for r in (4,5) for x in (1,2) for K in range(1,71) for MF0 in (4,12,20)]
    for case in [(3,25,1,6,4,1,5),(3,125,1<<700,10,12,2,6),(4,5,3,14,20,1,6)]:records.append(outer(*case))
    counts=Counter((z['m3'],z['epsilon']) for z in records)
    return dict(status='PASS',cases=len(records),branches=[dict(m3=m,epsilon=e,count=n) for (m,e),n in sorted(counts.items())],max_t=max(z['t'] for z in records),max_R_bits=max(z['R_bits'] for z in records),records_sha256=digest(records),examples=records[:3]+records[-3:],X_or_Pell_materialized=False,fixture_scope='Diagnostic necessary-condition tuples, not materialized genuine compilers')

def pell(A,n):
    need(A>=2 and 0<=n<=200,'bounded Pell argument')
    D=A*A-1;x,y=1,0
    for _ in range(n):x,y=A*x+D*y,x+A*y
    need(x*x-D*y*y==1,'Pell norm');return x,y

def family(branch,z):
    p,n,yexp=(4*z,3*z,2*z-1) if branch=='A' else (20*z,14*z,15*z-1)
    X=1<<p;Y=1<<yexp;E=X*Y;a0=Y*(X+1);A=a0+2;Delta=A*A-1;H=4*a0+3;P=2*X*Y*Y+1
    D,c=pell(A,p);tau,j=pell(P,n);k=2*j;eta=c-k*Y;zeta=k-eta
    need(p*(p-n)==(yexp+1)*(2*n-p),'small exact resonance')
    need(min(eta,zeta)>0 and eta*X<4*p*Y*k,'strict ratio and bound')
    need(tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1,'first norm')
    need((k-2*n)%E==0 and (k-2*n)//E>0,'positive integral h')
    gamma,rem=divmod(D-a0*c-X,H);need(rem==0 and gamma>0 and c%2==0,'main projection even c')
    for I in (3,5,p-1):
        mu,kappa=pell(A,I);delta,rem=divmod(kappa-I,Delta);need(rem==0 and delta>0,'input delta')
        rho,rem=divmod(mu-a0*kappa-(1<<I),H);sigma=gamma-rho
        need(rem==0 and min(rho,sigma)>0,'shared rho sigma')
        need(mu==(1<<I)+a0*(I+delta*Delta)+rho*H,'literal input root')
    Faux=Delta*c**4+1;need((c*D-1)**2<Faux<(c*D)**2,'nonsquare')
    return dict(branch=branch,parameter=z,p=p,n=n,yexp=yexp,c_bits=c.bit_length(),component_sha256=digest([hex(v) for v in (D,c,tau,k,eta,zeta,gamma)]))

def component_checks():
    families=[family('A',u) for u in range(3,17)]+[family('B',v) for v in range(2,9)];aux=[]
    for Delta in (8,24,120):
        for c in range(1,13):
            for R in (3,7,11,15,19):
                S=Delta*c*c;Faux=Delta*c**4+1;chi,y=pell(S,R);V,rem=divmod(chi,S)
                need(rem==0 and (V+R)%c==0,'direct odd quotient and even/odd c congruence')
                U,rem=divmod(V+R*Faux,c);U+=1;need(rem==0 and min(U,V,y,Faux)>0,'positive integral auxiliary witnesses')
                need(V==c*(U-1)-R*Faux,'literal V')
                Na=S*S*V*V-(S*S-1)*y*y;Qs=Faux-Delta*c**4
                need(Na==Qs==1 and Delta*(Na*Qs-1)==0,'full finalizer cuts')
                aux.append((Delta,c,R,digest([hex(v) for v in (Faux,U,y)])))
    projection=0
    for A in (2,3,5,15,64):
        H=4*A-5;prev=0
        for n in range(1,31):
            chi,psi=pell(A,n);g,rem=divmod(chi-(A-2)*psi-(1<<n),H)
            need(rem==0 and (n==1 or g>prev),'projection monotonicity')
            if n%2:need((psi-n)%(A*A-1)==0,'odd index congruence')
            prev=g;projection+=1
    return dict(status='PASS',family_cases=len(families),families=families,shared_input_cases=3*len(families),auxiliary_cases=len(aux),even_c_auxiliary_cases=sum(c%2==0 for D,c,R,h in aux),auxiliary_sha256=digest(aux),projection_cases=projection,max_c_bits=max(z['c_bits'] for z in families),fixture_scope='Small component lemmas only, not full compiler witnesses')

def residue_checks():
    rows=[]
    for q7 in (2,4):
        for K in range(35):
            valid=[h for h in range(1,13) if (1+2*(K+pow(2,5*h,5)))%5 and (1+q7*(K+pow(2,5*h,7)))%7]
            need(len(valid)>=6,'all h residue classes');rows.append([q7,K,valid])
    for K in range(5):
        e=9 if K==1 else 8;need((1+2*(K+pow(2,e,5)))%5!=0,'8/9 exponent')
    need(8*3<2**6 and 40*2<2**10,'gap thresholds')
    need((13*625)**4<2**625,'outer initial threshold')
    return dict(status='PASS',h_cases=70,minimum_h_choices=min(len(x[2]) for x in rows),branch_A_residues=5,residue_sha256=digest(rows))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
    need(not(a.output and a.expect),'choose output or expect')
    result=dict(status='PASS',recovery='Newly reconstructed science packet; not byte-identical authentication of lost release.',theorem='Every unchanged genuine compiler and positive input has full positive zeros of the pinned auxiliary square/product82.',checker_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),proof_sha256=sha256((ROOT/'COUNTERFAMILY.md').read_bytes()).hexdigest(),source_contract=source_contract(),symbolic_cuts=symbolic_cuts(),residue_checks=residue_checks(),outer_checks=outer_checks(),component_checks=component_checks(),execution_boundary='Only newly authored checker code executes. Upstream code and saved rows are data only.',verification_limit='Finite checks corroborate the separate unbounded proof; no giant full compiler witness is materialized.')
    if a.expect:need(same(result,json.loads(a.expect.read_text())),'type-exact receipt equality')
    if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',outer_cases=result['outer_checks']['cases'],Pell_family_cases=result['component_checks']['family_cases'],auxiliary_cases=result['component_checks']['auxiliary_cases'],source_rows_compared=82,saved_schedule_executed=False),sort_keys=True))
if __name__=='__main__':main()
