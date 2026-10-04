#!/usr/bin/env python3
"""Independent bounded checks of HEIGHT.md; all source snapshots are data only.
No eval/exec/import of upstream code and no evaluation of a saved schedule.
Small inner components and outer packing fixtures are disjoint, never full tuples.
Every check remains active with Python -O. Standard library only.
"""
from pathlib import Path
from fractions import Fraction
from math import comb
import hashlib
import json

ROOT = Path(__file__).resolve().parent
CAP = 500_000
PINS = {
    'BASE_COUNTERFAMILY.md':'690c5a1dc237bd53a9582bfbe01fcd8a176174e6b116089a1842532f83c1770b',
    'source/complete82_auxiliary_square_product_chart.py':'5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc',
    'source/complete82_auxiliary_square_product_chart.json':'7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a',
    'source/complete82_auxiliary_square_product_chart.md':'10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9',
    'source/review_complete82_auxiliary_square_product_chart.md':'02a12fd0426ad57b7c2bc822bc93266ed6511334e98cfb712cdd9f893d75722c',
    'source/FIXED_RAW_UNIVERSAL_76_PROOF.md':'75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
    'source/HALF_PARAMETER_PELL_92_PROOF.md':'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
    'source/complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
    'source/complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
}
CHECKS = 0
MAX_BITS = 0

def need(ok, message):
    global CHECKS
    CHECKS += 1
    if not ok:
        raise ValueError(message)

def cap(*values):
    global MAX_BITS
    for v in values:
        MAX_BITS = max(MAX_BITS, abs(v).bit_length())
        need(abs(v).bit_length() <= CAP, 'component size cap')

def exact_bl(value, predicted, name):
    need(value > 0, name+' positivity')
    need(value.bit_length() == predicted, name+' exact bit length')

def ceil_log2(v):
    return (v-1).bit_length()

def pell(A, j):
    # Our own ordinary recurrence, independent of all source schedules.
    x,y=1,0
    D=A*A-1
    for _ in range(j):
        x,y=A*x+D*y,x+A*y
    cap(x,y)
    return x,y

def source_checks():
    for name,want in PINS.items():
        got=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
        need(got==want,'data pin '+name)
    packet=json.loads((ROOT/'source/complete82_auxiliary_square_product_chart.json').read_text())['packet']
    witnesses=['Jrep','F','alpha','transport_quotient','L16','h','i','auxiliary_Tf','s','w','tau_root','eta','zeta','y_aux','Z','delta','rho','sigma']
    need(packet['witnesses']==witnesses,'18 actual supplied witness ports')
    need(packet['fixed_numerals']==['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF'],'six fixed ports')
    need(packet['ordinary_input']=='x','ordinary input')
    need(len(packet['source'])==82,'82 paid rows')
    # Literal definitions compared as inert JSON data, never evaluated.
    rows={r[0]:r[1:] for r in packet['source']}
    cones={
      'Ac2':['*','A','c2'],'c2':['*','R10a','R10a'],
      'aux_coefficient_root':['*','i','Ac2'],
      'R16':['*','aux_coefficient_root','aux_coefficient_root'],
      'scaled_f_square':['*','A','L16'],
      'norm_strong':['-','scaled_f_square','R16'],
      'auxiliary_Tf_minus_one':['-','auxiliary_Tf',1],
      'auxiliary_c_Tf':['*','R10a','auxiliary_Tf_minus_one'],
      'auxiliary_R_f2':['*','r_lhs','L16'],
      'aux_u_rhs':['-','auxiliary_c_Tf','auxiliary_R_f2'],
      'H2':['*','aux_u_rhs','aux_u_rhs'],
      'aux_y2':['*','y_aux','y_aux'],
      'aux_square_gap':['-','H2','aux_y2'],
      'L17':['*','R16','aux_square_gap'],
      'norm_aux':['+','L17','aux_y2'],
      'norm_pair':['*','norm_first','norm_main'],
      'norm_triple':['*','norm_pair','norm_input'],
      'norm_four':['*','norm_triple','norm_aux'],
      'norm_product':['*','norm_four','norm_index'],
      'all_units':['*','norm_product','norm_transport'],
      'seven_units':['*','all_units','norm_strong'],
      'polynomial':['-','seven_units','A'],
    }
    for name,want in cones.items():
        need(rows[name]==want,'literal auxiliary/final cone '+name)
    return {'pinned_files':len(PINS),'literal_rows_compared':len(cones),'saved_schedule_executed':False}

def uniform_checks():
    for p in range(16,257):
        bound=Fraction(8*p*p,1<<p)
        need(bound<=Fraction(1,32),'uniform perturbation exponent')
        need(Fraction((p+1)**2,1<<(p+1))<Fraction(p*p,1<<p),'decrease')
        need(ceil_log2(p)+3<=p,'eta table domination')
    for R in range(100,501):
        a_plus=Fraction(4*R**3+4*R**2-7*R+2,3)
        a_minus=Fraction(4*R**3-12*R**2+9*R+2,3)
        b=Fraction(25*R**3+25*R**2-39*R+3,14)
        for v in [a_plus,a_minus,b]:
            need(Fraction(5,4)*R**3<v<2*R**3,'explicit cubic squeeze')
    need(Fraction(5,4)*Fraction(99,100)**3>1,'radix lower multiplier')
    return {'p_values':241,'cubic_R_values':401}

def fixture(branch,z):
    if branch=='A':
        u=z; eps=1 if u%2==0 else -1
        p,n,y,R=4*u,3*u,2*u-1,6*u-eps
    else:
        v=z; eps=1
        p,n,y,R=20*v,14*v,15*v-1,28*v-1
    L=p+y+1; C=(p-1)*L; F0=4*C+2*L-2; N=(R-1)*(2*p*L-1)
    need(p>=16 and y>=3 and n>=3 and R>=8 and R<2*p,'inner hypotheses')
    need(N+2*p*L<CAP,'prospective component cap')
    need((n-1)*(p+2*y+2)==C-y-1,'resonance first form')
    need(n*(p+2*y+2)==p*L,'resonance second form')
    need(N-F0>=R,'U additive error gap')
    X,Y=1<<p,1<<y
    a0=Y*(X+1); A=a0+2; Delta=A*A-1; H=4*a0+3
    D,c=pell(A,p)
    P=2*X*Y*Y+1
    tau,k0=pell(P,n); k=2*k0
    need(D*D-Delta*c*c==1,'main norm')
    need(tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1,'first norm')
    exact_bl(c,C+1,'c')
    exact_bl(k,C-y+1,'k')
    exact_bl(tau,p*L,'tau')
    eta,zeta=c-k*Y,k-(c-k*Y)
    need(eta>0 and zeta>0,'ratio witnesses')
    need(eta.bit_length()<=C-p+ceil_log2(p)+3,'eta bound')
    need(zeta.bit_length()<=C-y+1,'zeta bound')
    need((k-2*n)%(X*Y)==0,'index divisibility')
    h=(k-2*n)//(X*Y)
    exact_bl(h,C-p-2*y+1,'h')
    need(k-h*X*Y-R==eps,'retained index')
    gamma=(D-a0*c-X)//H
    need((D-a0*c-X)%H==0,'main projection')
    input_cases=0
    for I in range(3,p,2):
        mu,kappa=pell(A,I)
        need((kappa-I)%Delta==0,'input divisibility')
        delta=(kappa-I)//Delta
        need((mu-a0*kappa-(1<<I))%H==0,'input projection')
        rho=(mu-a0*kappa-(1<<I))//H
        sigma=gamma-rho
        exact_bl(delta,(I-3)*L+3,'delta')
        exact_bl(rho,(I-2)*L+1,'rho')
        exact_bl(sigma,(p-2)*L+1,'sigma')
        need(mu*mu-Delta*kappa*kappa==1,'input norm')
        input_cases+=1
    S=Delta*c*c; Faux=Delta*c**4+1
    cx,yaux=pell(S,R)
    need(cx%S==0,'auxiliary quotient integral')
    V=cx//S
    need((V+R*Faux)%c==0,'U congruence')
    U=(V+R*Faux)//c+1
    need(S*S*V*V-(S*S-1)*yaux*yaux==1,'auxiliary norm')
    exact_bl(Faux,F0+1,'Faux')
    exact_bl(V,N+1,'V')
    exact_bl(yaux,N+1,'yaux')
    exact_bl(U,N-C+1,'U')
    need(yaux>max(Faux,U,h,tau,eta,zeta,delta,rho,sigma),'inner domination')
    need(c%8==0 and c>2*R,'auxiliary minimum prerequisites')
    if branch=='A':
        cubic=Fraction(4*R**3+(8*eps-4)*R*R+(1-8*eps)*R+2,3)
    else:
        cubic=Fraction(25*R**3+25*R*R-39*R+3,14)
    need(cubic==N+1,'exact cubic formula')
    return {'branch':branch,'parameter':z,'epsilon':eps,'p':p,'n':n,'yexp':y,'R':R,'input_exponents_checked':input_cases,'y_aux_bits':yaux.bit_length(),'U_aux_bits':U.bit_length(),'max_component_bits':cx.bit_length()}

def crt(pairs):
    value,modulus=0,1
    for a,m in pairs:
        value+=modulus*((a-value)*pow(modulus,-1,m)%m)
        modulus*=m
    return value or modulus

def outer_checks():
    # These satisfy the needed inequalities/residues but are diagnostic masks,
    # never claimed genuine compiled programs. Stop before Pell coordinates.
    records=[]
    for x in [1,5,23]:
        for K in [1,17,100]:
            for MF0 in [1,2,3]:
                B=32; d=5; ell=10; b=5; MC=2; MF=31+MF0
                I=ell*x+b; W=1<<I; Mmax=max(I,K.bit_length(),61)
                t=d
                while t<4*Mmax:t*=5
                need(t>=max(d,4*Mmax) and t<=max(d,20*Mmax),'minimal-r bounds')
                q=1<<t; J=(q-1)//31; Q=q*q-1; mask=(MC+q*MF)*J
                m3=(MC+2*MF)%3
                if m3:
                    eps=1 if m3==2 else -1
                    e=9 if K%5==1 else 8
                    Lpack=K+(1<<e); beta=Q*(1+q*Lpack)
                    astar=Q*(q*q-q*(Lpack*W+1-eps))+mask
                    target=(3*e*pow(2,-1,t)-eps)%t
                    Z=crt([(1,4),((astar-target)*pow(beta,-1,t)%t,t)])
                else:
                    eps=1
                    h0=next(j for j in range(1,13) if (1+q*(K+(1<<(5*j))))%5 and (1+q*(K+(1<<(5*j))))%7)
                    e=5*h0; Lpack=K+(1<<e); beta=Q*(1+q*Lpack)
                    astar=Q*(q*q-q*Lpack*W)+mask; T=t//5
                    Z=crt([(1,4),((astar+1)*pow(beta,-1,7)%7,7),((astar-(7*h0-1))*pow(beta,-1,T)%T,T)])
                F=Lpack*(W+Z)+1-eps
                alpha=q-F-2*Z-W-ell*x
                R=(q*q-q*F-Z)*Q+mask
                need(alpha>0 and F+Z<q and Z<=6*t,'outer positivity')
                need(J.bit_length()<=t and alpha.bit_length()<=t,'J/alpha table')
                need(F.bit_length()<=(t+1)//2+3,'F table')
                need(Z.bit_length()<=(6*t).bit_length(),'Z table')
                need(R%4==3 and R>1<<(3*t),'outer R residue and size')
                need(R==q**4-q**3*F-q*q*(Z+1)+q*F+Z+mask,'R expansion')
                diff=q**4-R
                need(0<diff and diff*diff*q<25*q**8,'explicit R closeness without floats')
                need(100*R>99*q**4,'R > .99 q^4')
                if m3:
                    u=(R+eps)//6; p,n,y=4*u,3*u,2*u-1
                    need(R+eps==6*u,'A integrality')
                else:
                    v=(R+1)//28; p,n,y=20*v,14*v,15*v-1
                    need(R+1==28*v,'B integrality')
                L=p+y+1; C=(p-1)*L; N=(R-1)*(2*p*L-1)
                need(p%t==e%t and p>56*t and y>=3*t,'inner exponent requirements')
                need((1<<(12*t))<N+1<(1<<(12*t+1)),'explicit height-bit squeeze')
                lc=ceil_log2(W+Z)
                need(lc<=(t+3)//4+1,'packing C logarithm')
                need(p-2*t+lc+2<p,'transport domination')
                cap(R,N)
                records.append({'x':x,'K':K,'MF0':MF0,'branch_mod3':m3,'t':t,'R_bits':R.bit_length(),'predicted_height_bitlength_bits':(N+1).bit_length()})
    return records

def negative_checks():
    # These must reject in normal and optimized execution alike.
    caught=0
    for fn in [lambda:need(False,'intentional fail-closed check'),lambda:exact_bl(17,4,'intentional bad floor')]:
        try:fn()
        except ValueError:caught+=1
    need(caught==2,'both negative controls rejected')
    return caught

def run():
    binding=source_checks()
    uniform=uniform_checks()
    inner=[fixture('A',u) for u in range(4,9)]+[fixture('B',2)]
    outer=outer_checks()
    negatives=negative_checks()
    return {'status':'PASS','scope':'Bounded independent corroboration, not proof by testing. No upstream code or saved schedule executed; no full witness tuple materialized.','source_binding':binding,'uniform_checks':uniform,'inner_component_fixtures':inner,'diagnostic_outer_fixtures':outer,'negative_controls_rejected':negatives,'active_checks':CHECKS,'maximum_materialized_integer_bits':MAX_BITS,'materialization_cap_bits':CAP}

if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
