#!/usr/bin/env python3
"""Complete82 arithmetic chart; auxiliary erasure is not a universality proof."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'review_complete84_scaled_strong_output.md':'6379d0ea3e7befded4be709c1f785a0e81dd915e813608db9b0a32ffbaf9b330',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md':'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
 'first_index_scaled_obstruction.md':'b67d208d4c18e45145cf91f272d72e2852c09d79be631da8f0a0ce5f377ba1fd',
 'first_index_scaled_obstruction.json':'52b04d7d47065b822d174f6d480fc31d40d908cc014d4fe517600f2b14ac1cea',
 'free_coefficient83_native_alias.md':'542775d7ff0ccd84f5fe94c32d6c396ad45a8cc033dd1cbd37ed72dedd40f96f',
 'free_coefficient83_native_alias.json':'9bf5e1c6452c5c5700821adaf63d59df1c61d2968704a23e63aae3cac067e846',
}
F='L16';U='auxiliary_Tf'
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']
FIXED=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
def need(x,m):
    if not x:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def same(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b

def graph(p):
    env={n:0 if n in FIXED else 1 for n in p['free']};table={}
    need(len(env)==len(p['free']),'unique ports')
    for n,o,a,b in p['source']:
        need(n not in env and o in ('+','-','*'),'SSA/opcode')
        need(all(type(v) is int or type(v) is str and v in env for v in (a,b)),'operand')
        x=env[a] if type(a) is str else 0;y=env[b] if type(b) is str else 0
        env[n]=x+y if o=='*' else max(x,y);table[n]=[o,a,b]
    live=set();todo=[p['output']]
    while todo:
        v=todo.pop()
        if type(v) is int or v in live:continue
        live.add(v)
        if v in table:todo+=table[v][1:]
    need(live==set(env),'all supplied ports and paid rows live')
    c=Counter(r[1] for r in p['source'])
    return dict(M=c['*'],A=c['+']+c['-'],total=len(table),free_ports=len(p['free']),naive_degree=env[p['output']])

def construct(old):
    removed=[['L16','*','f','f'],['auxiliary_Tf','*','auxiliary_quotient','f']]
    need(all(old['source'].count(r)==1 for r in removed),'two literal coordinate producers')
    replace={'f':F,'auxiliary_quotient':U}
    p=dict(source=[list(r) for r in old['source'] if r not in removed],
           free=[replace.get(n,n) for n in old['free']],witnesses=[replace.get(n,n) for n in old['witnesses']],
           fixed_numerals=list(old['fixed_numerals']),ordinary_input=old['ordinary_input'],output=old['output'],
           factors=list(old['factors']),witness_domain='strictly positive integers',
           ledger=dict(M=45,A=37,total=82,core_M=39,core_A=36,core_total=75,finalizer_M=6,finalizer_A=1,finalizer_total=7),
           exact_degree=185,factor_exact_degrees=[22,18,32,58,7,2,46],universal_soundness='UNPROVED')
    need(p['factors']==FACTORS and p['fixed_numerals']==FIXED and len(p['witnesses'])==18,'literal interface')
    need(graph(p)==dict(M=45,A=37,total=82,free_ports=25,naive_degree=195),'complete actual count')
    uses={n:[r[0] for r in old['source'] if n in r[2:]] for n in ['f','auxiliary_quotient','i','y_aux']}
    need(uses==dict(f=['L16','auxiliary_Tf'],auxiliary_quotient=['auxiliary_Tf'],i=['aux_coefficient_root'],y_aux=['aux_y2']),'all coordinate consumers')
    changed={F,U,'i','y_aux'}
    for n,o,a,b in p['source']:
        if a in changed or b in changed:changed.add(n)
    need(set(FACTORS)&changed=={'norm_aux','norm_strong'},'five complete factors unchanged')
    need(not {'A','R10a','r_lhs'}&changed,'sector ports independent of erased coordinates')
    final=[['norm_pair','*','norm_first','norm_main'],['norm_triple','*','norm_pair','norm_input'],
           ['norm_four','*','norm_triple','norm_aux'],['norm_product','*','norm_four','norm_index'],
           ['all_units','*','norm_product','norm_transport'],['seven_units','*','all_units','norm_strong'],
           ['polynomial','-','seven_units','A']]
    need(all(p['source'].count(r)==1 for r in final),'complete seven-gate finalizer')
    nodes={}
    def node(key):
        if key not in nodes:nodes[key]=len(nodes)
        return nodes[key]
    def run(rows,e):
        for n,o,a,b in rows:e[n]=node((o,e[a] if type(a) is str else node(('integer',a)),e[b] if type(b) is str else node(('integer',b))))
        return e
    a=run(old['source'],{n:node(('port',n)) for n in old['free']})
    b=run(p['source'],{n:a[n] if n in (F,U) else node(('port',n)) for n in p['free']})
    need(all(a[n]==b[n] for n,o,x,y in p['source']),'whole forward graph identity')
    return p,dict(removed_rows=removed,consumers=uses,formal_register_identities=82,
                  whole_identity='P82(L16=f^2,auxiliary_Tf=T*f)=P84',unaffected_factors=[n for n in FACTORS if n not in ('norm_aux','norm_strong')])

def evaluate(rows,values):
    e=dict(values)
    for n,o,a,b in rows:
        x=e[a] if type(a) is str else a;y=e[b] if type(b) is str else b
        e[n]=x*y if o=='*' else x+y if o=='+' else x-y
    return e

def dense(rows,free,mod):
    e={k:list(v) for k,v in free.items()}
    for n,o,a,b in rows:
        x=e[a] if type(a) is str else [a%mod];y=e[b] if type(b) is str else [b%mod]
        if o=='*':
            z=[0]*(len(x)+len(y)-1)
            for i,v in enumerate(x):
                for j,w in enumerate(y):z[i+j]=(z[i+j]+v*w)%mod
        else:z=[((x[i] if i<len(x) else 0)+(1 if o=='+' else -1)*(y[i] if i<len(y) else 0))%mod for i in range(max(len(x),len(y)))]
        while len(z)>1 and z[-1]==0:z.pop()
        e[n]=z
    return e

def degree(p):
    rows={n:[o,a,b] for n,o,a,b in p['source']}
    expected={
      'Ac2':['*','A','c2'],'c2':['*','R10a','R10a'],
      'aux_coefficient_root':['*','i','Ac2'],'R16':['*','aux_coefficient_root','aux_coefficient_root'],
      'scaled_f_square':['*','A',F],'norm_strong':['-','scaled_f_square','R16'],
      'auxiliary_Tf_minus_one':['-',U,1],'auxiliary_c_Tf':['*','R10a','auxiliary_Tf_minus_one'],
      'auxiliary_R_f2':['*','r_lhs',F],'aux_u_rhs':['-','auxiliary_c_Tf','auxiliary_R_f2'],
      'H2':['*','aux_u_rhs','aux_u_rhs'],'aux_y2':['*','y_aux','y_aux'],
      'aux_square_gap':['-','H2','aux_y2'],'L17':['*','R16','aux_square_gap'],
      'norm_aux':['+','L17','aux_y2'],'polynomial':['-','seven_units','A']}
    need(all(rows[n]==r for n,r in expected.items()),'actual new auxiliary/strong/final cones')
    cases=[]
    for j,mod in enumerate([1000003,1000033]):
        fixed=dict(Bm1=15+16*j,Kconstant=97+j,twice_cell_bits=8+2*j,inner_bits=3+j,MC=14-j,MF=19+j)
        coeff={n:i+3+j for i,n in enumerate(p['free']) if n not in FIXED}
        e=dense(p['source'],{n:[fixed[n]] if n in FIXED else [0,coeff[n]] for n in p['free']},mod)
        need([len(e[n])-1 for n in FACTORS]==[22,18,32,58,7,2,46],'all factor degree diagnostics')
        Q=fixed['Bm1']*coeff['Jrep'];k=coeff['eta']+coeff['zeta'];gamma=coeff['rho']+coeff['sigma']
        C=Q-coeff['F']-coeff['Z']-coeff['alpha']-fixed['twice_cell_bits']*coeff['x']
        Nt=coeff['w']*C-coeff['transport_quotient']*Q
        top=32*pow(Q,111,mod)*coeff['h']*gamma*coeff['delta']**2*coeff['i']**4*pow(k,13,mod)*pow(coeff['w'],18,mod)*pow(coeff['s'],31,mod)*Nt*coeff[U]**2%mod
        need(len(e['polynomial'])==186 and e['polynomial'][-1]==top and top!=0,'entire degree185 leader diagnostic')
        cases.append(dict(modulus=mod,degree=185,leading_coefficient=top))
    return dict(exact_degree=185,naive_upper=195,factor_degrees=[22,18,32,58,7,2,46],
                uniform_coefficient='-32*Bm1^112',dense_diagnostics=cases,
                proof='Five common factor leaders inherit pinned84; actual V top=c_top*U, K_top=i^2*Delta_top^2*c_top^4, Na top=K_top*c_top^2*U^2, Ns top=-K_top.')

# Small sparse coefficient proof of the complete output relation at its ports.
def coefficient_identity():
    names=['Delta','i','c','Faux','U','R','y','P5'];N=len(names);z=(0,)*N
    def c(x):return {z:x} if x else {}
    def v(n):
        m=list(z);m[names.index(n)]=1;return {tuple(m):1}
    def add(a,b,sgn=1):
        d=dict(a)
        for m,x in b.items():d[m]=d.get(m,0)+sgn*x
        return {m:x for m,x in d.items() if x}
    def mul(a,b):
        d={}
        for m,x in a.items():
            for n,y in b.items():
                k=tuple(i+j for i,j in zip(m,n));d[k]=d.get(k,0)+x*y
        return {m:x for m,x in d.items() if x}
    def sq(a):return mul(a,a)
    Delta,i,cp,fp,up,R,y,P5=[v(n) for n in names]
    S=mul(i,mul(Delta,sq(cp)));K=sq(S)
    V=add(mul(cp,add(up,c(1),-1)),mul(R,fp),-1)
    Na=add(mul(K,add(sq(V),sq(y),-1)),sq(y))
    Ns=add(mul(Delta,fp),K,-1)
    source=add(mul(P5,mul(Na,Ns)),Delta,-1)
    Qs=add(fp,mul(Delta,sq(mul(i,sq(cp)))),-1)
    wanted=mul(Delta,add(mul(P5,mul(Na,Qs)),c(1),-1))
    need(source==wanted,'full all-ring discriminant factor identity')
    return dict(monomials=len(source),polynomial_sha256=sha(stable([[list(m),x] for m,x in sorted(source.items())])),identity='P82=Delta*(P5*Na*(Faux-Delta*i^2*c^4)-1)')

def pell(A,n):
    x,y=1,0;D=A*A-1
    for _ in range(n):x,y=A*x+D*y,x+A*y
    return x,y

def extension(Delta,c,R,i,epsilon):
    B=Delta*i*i*c**4
    need(Delta>0 and c>0 and c%2==1 and R>0 and i>0 and epsilon in (-1,1) and B>1,'sector hypotheses')
    Faux=B+epsilon;S=i*Delta*c*c
    # First find the CRT class, then make it positive without changing it.
    candidates=[epsilon*R+c*j for j in range(4) if (epsilon*R+c*j)%4==3]
    need(len(candidates)==1,'unique odd-c CRT class');v=candidates[0]
    if v<=0:v+=4*c*((-v)//(4*c)+1)
    need(v>0 and v%4==3 and (v-epsilon*R)%c==0,'positive CRT index')
    chi,y=pell(S,v);need(chi%S==0,'odd quotient');V=chi//S
    Uaux,rem=divmod(V+R*Faux,c);Uaux+=1
    need(rem==0 and min(Faux,Uaux,y,V)>0,'positive integral extension')
    need(V==c*(Uaux-1)-R*Faux,'literal auxiliary argument')
    Na=S*S*(V*V-y*y)+y*y;Ns=Delta*Faux-S*S
    need(Na==1 and Ns==epsilon*Delta and epsilon*Na*Ns-Delta==0,'complete finalizer on outer P5=epsilon')
    return dict(Delta=Delta,c=c,R=R,i=i,epsilon=epsilon,auxiliary_index=v,
                F_bits=Faux.bit_length(),U_bits=Uaux.bit_length(),y_bits=y.bit_length(),
                component_sha256=sha(stable([hex(x) for x in [Faux,Uaux,y,S,V]])))

def native_t13():
    t=13;p=t*(t+2);n=t*(t+1);R=2*n-1;X=2**p;Y=2**(t+1);E=X*Y
    a=Y*(X+1);A=a+2;Delta=A*A-1;H=4*a+3;P=2*X*Y*Y+1
    D,c=pell(A,p);tau,kn=pell(P,n);k=2*kn
    eta=c-k*Y;zeta=k-eta;gam,rem=divmod(D-a*c-X,H);need(rem==0 and gam>1,'main projection')
    h,rem=divmod(k-2*n,E);need(rem==0 and h>0 and eta>0 and zeta>0,'retained positive index/ratio')
    need(tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1 and D*D-Delta*c*c==1 and k-h*E-R==1,'three native factors')
    need(R%4==3 and c%2==1 and p!=R,'unconditional v=R extension for this family')
    need(math.gcd(c,p)==195 and (R-p)%195!=0,'old free-S CRT really fails')
    Faux=1+Delta*c**4;M=D*c
    need((M-1)**2<Faux<M*M,'strict nonsquare interval')
    need(Faux-(M-1)**2==c*(2*D-c) and M*M-Faux==c*c-1,'exact endpoint gaps')
    vals=dict(X=X,Y=Y,w=X//16,s=Y//16**3,D=D,c=c,tau=tau,k=k,eta=eta,zeta=zeta,rho=1,sigma=gam-1,h=h,F_aux=Faux,S=Delta*c*c)
    return dict(t=t,p=p,n=n,R=R,old_CRT_gcd=195,auxiliary_index=R,
                fields_sha256=sha(stable({n:hex(v) for n,v in vals.items()})),bit_lengths={n:v.bit_length() for n,v in vals.items()},
                auxiliary_extension='V,y,U exist by the sector theorem; not materialized',full_compiler_zero=False)

def verify(root):
    for n,pin in PINS.items():need(sha((root/n).read_bytes())==pin,'pin '+n)
    parent=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet']
    p,g=construct(parent);checks=0
    for j in range(48):
        vals={n:Fraction((j+5)*(k+7)%31-15,1 if j<24 else 1+k%4) for k,n in enumerate(parent['free'])}
        a=evaluate(parent['source'],vals);b=evaluate(p['source'],{n:a[n] if n in (F,U) else vals[n] for n in p['free']})
        need(all(a[n]==b[n] for n,o,x,y in p['source']),'entire forward rational/integer evaluation');checks+=82
    fixtures=[extension(D,c,R,i,e) for D in [1,3,8,24] for c in [1,3,5,9] for R in [1,2,5] for i in [1,2] for e in [-1,1] if D*i*i*c**4>1]
    residue_cases=0
    for S in range(4):
        for V in range(4):
            for y in range(4):need((S*S*(V*V-y*y)+y*y)%4!=3,'auxiliary negative unit exclusion');residue_cases+=1
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),dependency_pins=PINS,
                packet=p,source_graph=g,complete_source_sha256=sha(stable(p['source'])),coefficient_identity=coefficient_identity(),degree=degree(p),
                forward_evaluations=48,rational_forward_evaluations=24,retained_value_checks=checks,
                small_sector_extensions=fixtures,mod4_negative_unit_cases=residue_cases,native_t13=native_t13(),
                theorem='On positive outer tuples with c odd,R>0,Delta*i^2*c^4>1, projection of complete82 zeros is exactly P5 in {-1,1}; the intended five +1 factor sector always extends.',
                limitation='No universal82 theorem or false accepted ordinary input; native mismatch fixtures are not full compiler zeros.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
    need(not(a.output and a.expect),'choose output or expect');r=verify(a.root)
    need(same(r,json.loads(json.dumps(r))),'typed roundtrip')
    if a.expect:need(same(r,json.loads(a.expect.read_text())),'exact receipt mismatch')
    if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',operations=82,degree=185,sector_extensions=len(r['small_sector_extensions']),native_target=r['native_t13']['R'],universal_soundness='UNPROVED')))
if __name__=='__main__':main()
