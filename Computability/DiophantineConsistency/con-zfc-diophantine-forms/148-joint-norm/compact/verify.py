#!/usr/bin/env python3
"""Independent exact checks for the delivered finite polynomial object."""
from pathlib import Path
import ast
import copy
import gzip
import hashlib
import json
from collections import Counter
import subprocess
import sys

ROOT=Path(__file__).resolve().parent

def need(test, message):
    if not test:
        raise ValueError(message)

def const(n):
    return {():n} if n else {}

def atom(name):
    return {(name,):1}

def add(a,b,sign=1):
    z=a.copy()
    for mon,c in b.items():
        z[mon]=z.get(mon,0)+sign*c
        if not z[mon]: del z[mon]
    return z

def mul(a,b):
    z={}
    for am,ac in a.items():
        for bm,bc in b.items():
            mon=tuple(sorted(am+bm)); z[mon]=z.get(mon,0)+ac*bc
    return {m:c for m,c in z.items() if c}

def power(a,n):
    z=const(1)
    while n:
        if n&1: z=mul(z,a)
        a=mul(a,a); n//=2
    return z

def polyexpr(text):
    def go(t):
        if isinstance(t,ast.Name): return atom(t.id)
        if isinstance(t,ast.Constant) and isinstance(t.value,int): return const(t.value)
        if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return mul(const(-1),go(t.operand))
        if isinstance(t,ast.BinOp):
            if isinstance(t.op,ast.Add):return add(go(t.left),go(t.right))
            if isinstance(t.op,ast.Sub):return add(go(t.left),go(t.right),-1)
            if isinstance(t.op,ast.Mult):return mul(go(t.left),go(t.right))
            if isinstance(t.op,ast.Pow) and isinstance(t.right,ast.Constant) and isinstance(t.right.value,int) and t.right.value>=0:
                return power(go(t.left),t.right.value)
        raise ValueError('Unsupported exact polynomial syntax')
    return go(ast.parse(text,mode='eval').body)

# These independently transcribed equations cover the entire displayed formula.
CUTS=[
 ('bJ','beta*J'),('q','bJ+1'),('Y','q**3*s'),('C','q-F-alpha'),
 ('X','w*q'),('k','eta+zeta'),('c','k*Y+eta'),('XY','X*Y'),
 ('Am1','XY+Y'),('Hp','4*Am1-1'),
 ('Dtau','1+(XY*k*Y)*(XY*k*Y+k)'),
 ('R','(bJ*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J'),
 ('e','k-R-1'),('Bt','(K0+w)*C-F'),('c2','c*c'),
 ('Delta','Am1*(Am1+2)'),('Dm','1+Delta*c2'),('A','Am1+1'),
 ('U','i*A*c2'),('S','Dtau*Dm'),('a','Delta*U*U*S'),
 ('F2','1+a'),('Q','Delta*a'),('Gstar','S*F2'),
 ('cTR','c*T-R'),('V','F2*cTR-c'),('L','cTR*V'),
 ('Kpos','X*(3*c-2*X)+2'),('Mtot','bJ*XY*Hp'),
 ('Znum','bJ*XY*(Hp*(n-L*Bt)+Kpos)-Hp*(XY*Bt+bJ*e)'),
 ('N','Q*(Znum*Znum-Mtot*Mtot*Gstar*V*V)+(Mtot*Mtot*Gstar-Znum*Znum)'),
]

def graph_check(obj):
    expected_inputs=['J','F','alpha','i','T','w','s','n','eta','zeta']
    expected_ports=['beta','K0','MC','MF']
    need(obj['witnesses']==expected_inputs,'Wrong witness domain/list')
    need(obj['fixed_numerals']==expected_ports,'Wrong fixed ports')
    need(obj['domain']=='strictly positive integers','Wrong domain')
    have=set(expected_inputs+expected_ports)
    rows=obj['source']; lookup={}
    for row in rows:
        need(len(row)==4,'Bad row length')
        name,op,left,right=row
        need(name not in have,'Duplicate row')
        need(op in ['+','-','*'],'Nonpolynomial operation')
        need(all(isinstance(v,int) or v in have for v in [left,right]),'Bad edge/order')
        have.add(name);lookup[name]=(op,left,right)
    live=set()
    def visit(name):
        if isinstance(name,int) or name in live:return
        live.add(name)
        if name in lookup:
            _,left,right=lookup[name]; visit(left);visit(right)
    visit(obj['output'])
    need(live==have,'Dead or missing input/port/gate')
    need(len(rows)==78==obj['operations'],'Wrong operation count')
    counts=dict(sorted(Counter(row[1] for row in rows).items()))
    need(counts=={'*':46,'+':18,'-':14}==obj['operation_breakdown'],'Wrong operation profile')
    known=set(expected_inputs+expected_ports);covered=set()
    for name,expr in CUTS:
        def expand(x):
            if isinstance(x,int):return const(x)
            if x in known:return atom(x)
            covered.add(x)
            op,l,r=lookup[x];p,q=expand(l),expand(r)
            return mul(p,q) if op=='*' else add(p,q,1 if op=='+' else -1)
        got=expand(name)
        need(got==polyexpr(expr),'Cut identity failed: '+name)
        known.add(name)
    need(covered==set(lookup),'Cut coverage incomplete')
    return lookup,counts,len(covered)

def leading_check(obj):
    variables=set(obj['witnesses'])
    lead={name:atom(name) for name in obj['witnesses']+obj['fixed_numerals']}
    degree={name:(1 if name in variables else 0) for name in lead}
    def get(v):return (0,const(v)) if isinstance(v,int) else (degree[v],lead[v])
    for name,op,l,r in obj['source']:
        dl,pl=get(l); dr,pr=get(r)
        if op=='*':d,p=dl+dr,mul(pl,pr)
        elif dl>dr:d,p=dl,pl
        elif dr>dl:d,p=dr,pr if op=='+' else mul(const(-1),pr)
        else:d,p=dl,add(pl,pr,1 if op=='+' else -1)
        need(bool(p),'Leading cancellation needs deeper analysis at '+name)
        need(all(sum(v in variables for v in mon)==d for mon in p),'Nonhomogeneous leading part')
        degree[name]=d;lead[name]=p
    want=polyexpr('-16*(beta*J)**284*w**42*s**80*i**8*(eta+zeta)**38*T**2')
    need(degree['N']==454==obj['exact_degree'],'Wrong global degree')
    need(lead['N']==want,'Wrong full leading form')
    mon=tuple(sorted(['beta']*284+['J']*284+['w']*42+['s']*80+['i']*8+['eta']*38+['T']*2))
    need(lead['N'].get(mon)==-16,'Actual nonzero coefficient witness fails')
    return {name:degree[name] for name in ['A','Delta','c','Dtau','Dm','U','S','a','F2','Q','Gstar','cTR','V','L','Mtot','Bt','Znum','N']},len(want)

def coefficients(obj):
    vals={};reports={}
    for port,b in obj['coefficient_binding']['ports'].items():
        packed=(ROOT/'coefficients'/b['file']).read_bytes();raw=gzip.decompress(packed)
        need(hashlib.sha256(packed).hexdigest()==b['gzip_sha256'],'Compressed coefficient changed: '+port)
        need(hashlib.sha256(raw).hexdigest()==b['raw_sha256'],'Coefficient changed: '+port)
        value=int.from_bytes(raw,'little')
        need(value.bit_length()==b['bits'],'Coefficient bit length changed')
        vals[port]=value;reports[port]={'bits':b['bits'],'raw_sha256':b['raw_sha256']}
    need(vals['beta']>=31 and vals['beta']%2==1,'Wrong beta port')
    need(vals['K0']>0 and 0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'Wrong port box')
    return vals,reports

def direct(x,p):
    J,F,alpha,i,T,w,s,n,eta,zeta=[x[v] for v in ['J','F','alpha','i','T','w','s','n','eta','zeta']]
    beta,K0,MC,MF=[x[v] for v in ['beta','K0','MC','MF']]
    h=beta*J%p;q=(h+1)%p;C=(q-F-alpha)%p;X=w*q%p;Y=q**3*s%p
    k=(eta+zeta)%p;c=(k*Y+eta)%p;A=(Y*(X+1)+1)%p;Delta=(A*A-1)%p;H=(4*A-5)%p
    ell=X*Y*k*Y%p;E=(1+ell*(ell+k))%p
    R=((h*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J)%p;e=(k-R-1)%p;B=((K0+w)*C-F)%p
    Dm=(1+Delta*c*c)%p;U=i*A*c*c%p;S=E*Dm%p;a=Delta*U*U*S%p
    F2=(1+a)%p;Q=Delta*a%p;G=S*F2%p;b=(c*T-R)%p;V=(F2*b-c)%p;L=b*V%p
    K=(X*(3*c-2*X)+2)%p;M=h*X*Y*H%p
    Z=(h*X*Y*(H*(n-L*B)+K)-H*(X*Y*B+h*e))%p
    return ((Q-1)*Z*Z-M*M*G*(Q*V*V-1))%p

def evaluate(obj,values,p):
    env={k:v%p for k,v in values.items()}
    def val(x):return x if isinstance(x,int) else env[x]
    for name,op,l,r in obj['source']:
        a,b=val(l),val(r);env[name]=(a+b if op=='+' else a-b if op=='-' else a*b)%p
    return env[obj['output']]

def small_kernel_control():
    # Synthetic arithmetic data only; not a consistency-equation witness.
    A=3;Delta=8;c=35;d=99;tau=2;E=tau*tau;Dm=d*d
    f,I=1,0
    for _ in range(630):f,I=A*f+Delta*I,f+A*I
    divisor=A*c*c*tau*d
    need(I%divisor==0,'Synthetic strong divisibility')
    i=I//divisor;U=i*A*c*c;S=E*Dm;a=Delta*U*U*S;F2=1+a;Q=Delta*a;G=S*F2
    need(F2==f*f and Q==(Delta*I)**2,'New strong identity')
    need(G==(tau*d*f)**2,'Recovered product root')
    V=4*Q-3;y=4*Q-1;T=(V+c+3*f*f)//(c*f*f)
    need(F2*(c*T-3)-c==V,'Synthetic auxiliary congruence')
    need(Q*V*V-(Q-1)*y*y==1,'Synthetic auxiliary norm')
    z=tau*d*f*y
    need((Q-1)*z*z==G*(Q*V*V-1),'Synthetic new finalizer')
    return {'base':A,'main_index':3,'strong_index':630,'scope':'local kernel only; no calibrated zero'}

def main():
    obj=json.loads((ROOT/'equation78_degree454.json').read_text())
    lookup,counts,covered=graph_check(obj);degrees,terms=leading_check(obj)
    values,coeff=coefficients(obj)
    regressions=0
    for modulus in [1000000007,1000000009,2147483647]:
        for seed in range(1,9):
            point={v:(seed*(j+3)%19)-9 for j,v in enumerate(obj['witnesses'])}
            point.update(values)
            need(evaluate(obj,point,modulus)==direct(point,modulus),'Independent whole-formula regression')
            regressions+=1
    local=small_kernel_control()
    controls=[]
    mutations=[('Dm',3,2),('F2',3,2),('Q',2,'Dm'),('Gstar',3,'a'),
               ('V',3,'c2'),('Zpart2',2,'Am1'),('correction',3,'M2'),
               ('Delta_c2',2,'Am1'),('a',3,'c2')]
    for target,index,replacement in mutations:
        altered=copy.deepcopy(obj)
        row=next(r for r in altered['source'] if r[0]==target)
        row[index]=replacement
        try:graph_check(altered)
        except ValueError as exc:
            need(str(exc).startswith('Cut identity failed:'),'Mutation rejected before exact algebra: '+target)
            controls.append(target)
        else:raise ValueError('Mutation accepted: '+target)
    harmless=copy.deepcopy(obj)
    row=next(r for r in harmless['source'] if r[0]=='Gstar')
    row[2],row[3]=row[3],row[2]
    graph_check(harmless)
    subprocess.run([sys.executable,'-B',str(ROOT/'build.py'),'--check'],check=True,stdout=subprocess.PIPE)
    subprocess.run([sys.executable,'-B',str(ROOT/'rebuild_coefficients.py')],check=True,stdout=subprocess.PIPE)
    report={'status':'passed','variables':10,'domain':obj['domain'],'operations':78,
        'operation_breakdown':counts,'exact_degree':454,'covered_gates':covered,
        'exact_polynomial_cuts':len(CUTS),'full_leading_terms':terms,'degrees':degrees,
        'coefficient_binding':coeff,'modular_regression_controls':regressions,
        'rejected_count_and_liveness_preserving_mutations':controls,
        'accepted_commutative_rewrite':True,'whole_tuple_reconstructed':True,'kernel_control':local,
        'scope':'Finite polynomial/data verification; unbounded proofs and inherited calibration are identified in PROOF.md.'}
    if '--receipt' in sys.argv:
        path=Path(sys.argv[sys.argv.index('--receipt')+1]);path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
