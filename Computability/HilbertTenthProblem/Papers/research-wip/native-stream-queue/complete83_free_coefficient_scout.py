#!/usr/bin/env python3
"""Bounded data-only scout: 83 gates, but no universal soundness claim."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

PINS = {
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'review_complete84_scaled_strong_output.md':'6379d0ea3e7befded4be709c1f785a0e81dd915e813608db9b0a32ffbaf9b330',
 'complete85_auxiliary_bezout_projection.md':'d8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b',
 'review_complete85_auxiliary_bezout_math.md':'77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md':'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
}
S = 'aux_coefficient_root'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def stable(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()

def same(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b

def eval_source(rows, values):
    e=dict(values)
    for name,op,a,b in rows:
        a=e[a] if type(a) is str else a
        b=e[b] if type(b) is str else b
        e[name]=a*b if op=='*' else a+b if op=='+' else a-b
    return e

def audit_graph(packet):
    e=set(packet['free']); rows=packet['source']; table={}
    for name,op,a,b in rows:
        need(name not in e and op in ('+','-','*'), 'SSA/opcode')
        need(all(type(x) is int or type(x) is str and x in e for x in (a,b)), 'operand')
        table[name]=[op,a,b]; e.add(name)
    live=set()
    def walk(n):
        if type(n) is int or n in live: return
        live.add(n)
        if n in table:
            walk(table[n][1]); walk(table[n][2])
    walk(packet['output'])
    need(live==set(table)|set(packet['free']), 'complete live closure')
    c=Counter(row[1] for row in rows)
    return dict(M=c['*'],A=c['+']+c['-'],total=len(rows),witnesses=len(packet['witnesses']))

def make_packet(parent):
    rows=parent['source']; table={r[0]:r for r in rows}
    need(table[S]==[S,'*','i','Ac2'], 'literal removed row')
    consumers={x:[r[0] for r in rows if x in r[2:]] for x in ['i','f','auxiliary_quotient','y_aux','Ac2']}
    need(consumers['i']==[S], 'private i consumer')
    need(consumers['f']==['L16','auxiliary_Tf'], 'f consumers')
    need(consumers['auxiliary_quotient']==['auxiliary_Tf'], 'T consumers')
    need(consumers['y_aux']==['aux_y2'], 'y consumers')
    need(consumers['Ac2']==['norm_main',S], 'paid coefficient consumers')
    for row in [['R16','*',S,S],['scaled_f_square','*','A','L16'],
                ['norm_strong','-','scaled_f_square','R16'],
                ['L17','*','R16','aux_square_gap'],['norm_aux','+','L17','aux_y2'],
                ['polynomial','-','seven_units','A']]:
        need(table.get(row[0])==row,'actual local/full-finalizer source')
    child=dict(source=[list(r) for r in rows if r[0]!=S],
               free=[S if n=='i' else n for n in parent['free']],
               witnesses=[S if n=='i' else n for n in parent['witnesses']],
               fixed_numerals=list(parent['fixed_numerals']),ordinary_input=parent['ordinary_input'],
               output=parent['output'],factors=list(parent['factors']),
               witness_domain='strictly positive integers',
               ledger=dict(M=46,A=37,total=83,core_M=40,core_A=36,core_total=76,
                           finalizer_M=6,finalizer_A=1,finalizer_total=7),
               exact_degree=111,factor_exact_degrees=[22,18,32,16,7,2,14],
               universal_soundness='UNPROVED',
               scope='Complete arithmetic candidate only; no 83-operation universal bound or false accepted-input witness is established.')
    need(audit_graph(child)==dict(M=46,A=37,total=83,witnesses=18),'candidate ledger')
    # The two graph maps are identities of formal expression DAGs, not numeric cuts.
    # Inject S=i*Ac2, then compare all 83 actual retained register expressions.
    intern={}; memo={}
    def atom(value):
        key=('const',value) if type(value) is int else ('free',value)
        if key not in intern: intern[key]=len(intern)
        return intern[key]
    def op_node(op,a,b):
        key=(op,a,b)
        if key not in intern: intern[key]=len(intern)
        return intern[key]
    def run(source,env):
        for name,op,a,b in source:
            env[name]=op_node(op,env[a] if type(a) is str else atom(a),env[b] if type(b) is str else atom(b))
        return env
    old=run(rows,{n:atom(n) for n in parent['free']})
    new=run(child['source'],{n:old[S] if n==S else atom(n) for n in child['free']})
    need(all(new[r[0]]==old[r[0]] for r in child['source']), 'complete formal forward graph')
    # No changed-coordinate consumer can enter any retained nonauxiliary factor.
    affected={'f','auxiliary_quotient','y_aux',S}
    for name,_,a,b in child['source']:
        if a in affected or b in affected: affected.add(name)
    retained=[n for n in child['factors'] if n not in ('norm_aux','norm_strong')]
    need(not set(retained)&affected,'extension changes a retained factor')
    return child,dict(consumers=consumers,formal_register_identities=len(child['source']),
                      unchanged_factor_ports=retained,forward_identity='F83(S=i*Ac2)=F84',
                      rational_pullback='F84(i=S/Ac2)=F83 whenever Ac2 is nonzero')

def dense(rows,line,mod):
    e={k:list(v) for k,v in line.items()}
    for name,op,a,b in rows:
        a=e[a] if type(a) is str else [a%mod]
        b=e[b] if type(b) is str else [b%mod]
        if op=='*':
            z=[0]*(len(a)+len(b)-1)
            for i,x in enumerate(a):
                for j,y in enumerate(b): z[i+j]=(z[i+j]+x*y)%mod
        else:
            z=[((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%mod for i in range(max(len(a),len(b)))]
        while len(z)>1 and z[-1]==0:z.pop()
        e[name]=z
    return e

def degree_check(child):
    upper={n:0 if n in child['fixed_numerals'] else 1 for n in child['free']}
    for n,op,a,b in child['source']:
        da=upper[a] if type(a) is str else 0; db=upper[b] if type(b) is str else 0
        upper[n]=da+db if op=='*' else max(da,db)
    need(upper['polynomial']==121,'gate upper')
    diagnostics=[]
    for case,mod in enumerate([1000033,1000037]):
        constants=dict(Bm1=15+16*case,Kconstant=97+case,twice_cell_bits=2+2*case,inner_bits=3+case,MC=7+case,MF=5+case)
        coeff={n:j+9+case for j,n in enumerate(child['free']) if n not in constants}
        line={n:[constants[n]] if n in constants else [0,coeff[n]] for n in child['free']}
        e=dense(child['source'],line,mod)
        need([len(e[n])-1 for n in child['factors']]==child['factor_exact_degrees'],'factor degrees')
        Q=constants['Bm1']*coeff['Jrep']; k=coeff['eta']+coeff['zeta']; gamma=coeff['rho']+coeff['sigma']
        Ct=Q-coeff['F']-coeff['Z']-coeff['alpha']-constants['twice_cell_bits']*coeff['x']
        Nt=coeff['w']*Ct-coeff['transport_quotient']*Q
        lead=-32*pow(Q,63,mod)*coeff['h']*gamma*coeff['delta']**2*k**5*coeff['w']**12*coeff['s']**17*coeff[S]**2*Nt*coeff['auxiliary_quotient']**2*coeff['f']**4%mod
        need(len(e['polynomial'])==112 and e['polynomial'][-1]==lead and lead!=0,'complete leader')
        diagnostics.append(dict(modulus=mod,degree=111,leading_coefficient=lead))
    return dict(exact=111,gate_upper=121,uniform_nonzero_monomial_coefficient='32*Bm1^64',diagnostics=diagnostics)

def pair_mul(a,b,D,mod=None):
    x=a[0]*b[0]+D*a[1]*b[1]; y=a[0]*b[1]+a[1]*b[0]
    return (x%mod,y%mod) if mod else (x,y)

def pell(A,n,mod=None):
    need(A>=2 and n>=0,'Pell parameters')
    D=A*A-1; out=(1,0); cur=(A,1)
    while n:
        if n&1:out=pair_mul(out,cur,D,mod)
        cur=pair_mul(cur,cur,D,mod); n//=2
    return out

def crt_index(c,p):
    d=math.gcd(c,8*p); need((2*p)%d==0,'CRT compatibility')
    m=8*p//d
    k=(2*p//d)*pow(c//d,-1,m)%m
    t=p+c*k
    need(t>0 and t%c==p%c and t%(8*p)==3*p%(8*p) and t%4==3,'CRT representative')
    return t

def odd_quotient_mod(B,t,mod):
    # Q_v(B^2)=chi_B(2v+1)/B without ever dividing modulo mod.
    # Q_0=1,Q_1=4B^2-3 and Q_{v+1}=(4B^2-2)Q_v-Q_{v-1}.
    v=(t-1)//2; need(t>0 and t%2==1,'odd auxiliary index')
    if not v:return 1%mod
    def mm(a,b):
        return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%mod for i in range(2) for j in range(2))
    M=((4*B*B-2)%mod,(-1)%mod,1,0); P=(1,0,0,1); e=v-1
    while e:
        if e&1:P=mm(P,M)
        M=mm(M,M);e//=2
    return (P[0]*(4*B*B-3)+P[1])%mod

def family_check(A,p,materialize=False):
    need(p>=5 and p%2==1,'odd main index')
    Delta=A*A-1; D,c=pell(A,p)
    need(c>2 and c%2==1 and math.gcd(c,D)==1,'main arithmetic')
    if p%4==3:
        f,v=D,c;t=p;inverse=Fraction(1,c)
    else:
        f,v=pell(A,2*p); need(v==2*D*c,'duplication')
        t=crt_index(c,p);inverse=Fraction(2*D,c)
        need(pell(A,4*p,f)==(f-1,0),'four-p sign')
        need(pell(A,8*p,f)==(1,0),'eight-p period')
        need(pell(A,t,f)[1]==c%f and pell(A,3*p)[1]==(2*f+1)*c,'three-p congruence')
    Scoef=Delta*v
    need(f*f-Delta*v*v==1 and Delta*f*f-Scoef*Scoef==Delta,'scaled strong')
    need(Scoef%c==0 and f*f%c==1 and math.gcd(c,f)==1,'CRT denominator split')
    Vmodc=odd_quotient_mod(Scoef,t,c); Vmodf=odd_quotient_mod(Scoef,t,f)
    need(Vmodc==(-p)%c and Vmodf==(-c)%f,'both quotient congruences')
    need(inverse.denominator>1 and Fraction(Scoef,Delta*c*c)==inverse,'nonintegral inverse')
    result=dict(A=A,p=p,branch=p%4,auxiliary_index=t,c_bits=c.bit_length(),f_bits=f.bit_length(),
                inverse_numerator=inverse.numerator,inverse_denominator=inverse.denominator,
                two_congruences=True,materialized_native_subsystem=materialize)
    if materialize:
        chi,y=pell(Scoef,t);need(chi%Scoef==0,'odd quotient integer');V=chi//Scoef
        need((V+c+p*f*f)%(c*f)==0,'integer T')
        T=(V+c+p*f*f)//(c*f)
        need(T>0 and V>0 and y>0,'positive subsystem')
        need(V==c*(T*f-1)-p*f*f,'literal Bezout argument')
        need(Scoef*Scoef*V*V-(Scoef*Scoef-1)*y*y==1,'auxiliary norm')
        result.update(V_bits=V.bit_length(),T_bits=T.bit_length(),y_bits=y.bit_length(),
                      positive_subsystem_digest=sha(stable([hex(f),hex(Scoef),hex(V),hex(y),hex(T)])))
    return result

def verify(root):
    root=root.resolve()
    for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'dependency '+name)
    parent=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet']
    child,graph=make_packet(parent)
    # Numeric checks supplement the formal all-value source identity.
    checks=0
    for case in range(40):
        values={n:Fraction(((case+7)*(j+3))%29-14,1 if case<20 else 1+j%5) for j,n in enumerate(parent['free'])}
        old=eval_source(parent['source'],values)
        newvalues={n:old[S] if n==S else values[n] for n in child['free']}
        new=eval_source(child['source'],newvalues)
        need(all(new[r[0]]==old[r[0]] for r in child['source']),'whole forward evaluation');checks+=1
    pullbacks=0
    for case in range(24):
        values={n:Fraction(2+((case+3)*(j+7))%13,1+j%3) for j,n in enumerate(child['free'])}
        new=eval_source(child['source'],values);need(new['Ac2']!=0,'positive rational Ac2')
        oldvalues={n:values[S]/new['Ac2'] if n=='i' else values[n] for n in parent['free']}
        old=eval_source(parent['source'],oldvalues)
        need(all(old[r[0]]==new[r[0]] for r in child['source']),'whole rational pullback');pullbacks+=1
    cases=[family_check(A,p,materialize=(A,p) in [(12,7),(16,11),(2,5)]) for A,p in [(12,7),(16,11),(24,19),(32,27),(2,5),(3,5),(7,9),(11,13),(17,17),(29,25)]]
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),dependency_pins=PINS,packet=child,
                complete_source_sha256=sha(stable(child['source'])),graph_proof=graph,degree=degree_check(child),
                forward_whole_evaluations=checks,rational_forward_evaluations=20,rational_pullbacks=pullbacks,
                family_cases=cases,
                theorem='Every full positive84 zero has positive83 zero extensions at the same ordinary input whose literal rational inverse i=S/Ac2 is nonintegral; both p mod4 branches.',
                limitation='No complete giant compiler zero is materialized. Recurrence fixtures are auxiliary/main subsystems; the full-zero theorem is parametric. No false ordinary input or sound83 universal representation is proved.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args()
    need(not(args.output and args.expect),'choose output or expect');r=verify(args.root)
    need(same(r,json.loads(json.dumps(r))),'typed JSON round trip')
    if args.expect:need(same(r,json.loads(args.expect.read_text())),'exact receipt mismatch')
    if args.output:args.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',operations=83,degree=111,universal_soundness='UNPROVED',full_forward_checks=r['forward_whole_evaluations'],rational_pullbacks=r['rational_pullbacks'],family_cases=len(r['family_cases']))))

if __name__=='__main__':main()
