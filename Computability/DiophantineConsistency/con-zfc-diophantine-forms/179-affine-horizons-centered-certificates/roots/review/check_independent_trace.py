#!/usr/bin/env python3
"""Independent endpoint audit; does not import producer code or execute sources."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,itertools
import sympy as S
ROOT=Path(__file__).resolve().parents[1]
MOD=1000000007

def need(ok,message):
    if not ok: raise ValueError(message)

def add(a,b,sign=1):
    c=dict(a)
    for n,v in b.items():c[n]=(c.get(n,0)+sign*v)%MOD
    return {n:v for n,v in c.items() if v}
def mul(a,b):
    c={}
    for i,v in a.items():
        for j,w in b.items():c[i+j]=(c.get(i+j,0)+v*w)%MOD
    return {n:v for n,v in c.items() if v}

def weighted_top(expr,variables,weights):
    terms=S.Poly(S.expand(expr),*variables).terms()
    degree=max(sum(m*w for m,w in zip(mon,weights)) for mon,c in terms)
    top=sum(c*S.prod(v**m for v,m in zip(variables,mon)) for mon,c in terms if sum(m*w for m,w in zip(mon,weights))==degree)
    return degree,S.expand(top)

bind=json.loads((ROOT/'inherited_round20/inherited/coefficients/BINDING.json').read_text())
ports={}
for name,e in bind['payloads'].items():
    raw=gzip.decompress((ROOT/'inherited_round20/inherited/coefficients'/e['file']).read_bytes())
    need(hashlib.sha256(raw).hexdigest()==e['raw_sha256'],'coefficient SHA '+name)
    need(len(raw)==e['raw_bytes'],'coefficient length '+name)
    value=int.from_bytes(raw,'little')
    need(value.bit_length()==e['bits'],'coefficient bits '+name)
    ports[name]=value%MOD
need(ports['beta']==(pow(2,1064921,MOD)-1)%MOD,'beta finite recipe')
need(ports['cone_A']==pow(2,1113,MOD),'cone A recipe')
need(ports['cone_B']==pow(2,666104,MOD),'cone B recipe')

# Universal identities, independent of any coefficient specialization.
x,p,t,U,Z,L,k,G=S.symbols('x p t U Z L k G')
need(S.expand(S.prod(x-ep*p-et*t for ep,et in itertools.product([-1,1],repeat=2))-((x*x-p*p-t*t)**2-4*p*p*t*t))==0,'norm signed product')
Dt=1+L*(L+k)
for shift in [0,1]:
    # rho_new = p+t, old carrier ratio is rho_new - p + t -2L-k.
    znew=U*(p+t)
    zold=znew-U*p+U*t-U*(2*L+k)
    carrier=(zold+U*k)**2+4*U*(L*zold-U)
    need(S.expand(carrier-4*U*U*(t*t-Dt))==0,'carrier restore')
N=lambda z: (z*z-U*U*G-U*U*Dt)**2-4*U**4*G*Dt
vars=[Z,U,L,k,G]
d85,top85=weighted_top(N(Z+U*L),vars,[7,6,9,5,16])
d87,top87=weighted_top(N(Z),vars,[7,6,9,5,18])
need(d85==58 and S.expand(top85+4*U**4*G*L**2)==0,'85 complete weighted top')
need(d87==60 and S.expand(top87-U**4*(G-L**2)**2)==0,'87 complete weighted top')

def bind_full_formula(g,degree):
    front=[('J','1+6*j'),('qm','J*beta'),('q','1+qm'),('W','4+12*w'),('X','W*q'),('Y','v'),('F','C*(K0+W)-qm*z'),('R','(q*q-q*F-C)*(q*q-1)+J*(MC+MF*q)'),('E','X*Y'),('a','Y+E'),('H','3+4*a'),('Delta','H+a*a')]
    if degree==85:front += [('ell','E*Y'),('k','1+R+ell*h')]
    else:front += [('k','1+R+E*h')]
    front += [('eta','c-Y*k'),('L','ell*k' if degree==85 else 'E*Y*k'),('I','4*c*c*(1+2*r)'),('Q','Delta*(f*f-1)'),('V','f*c*T-f*R-c'),('q3','q*q*q'),('M','2*q3'),('U','H*M'),('Klo','2*X*X-3*X*c-2')]
    front += [('Z','U*n+U*L+M*Klo+H*Y-H*q3' if degree==85 else 'U*n+M*Klo+H*Y-H*q3')]
    front += [('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'),('budget','Y*Y*(k*k*(q*q-Derr)-4*q*q*eta*eta)-k*k*q**'+('6' if degree==85 else '2*q3**2' )),('pos2','1+p2*p2+p3*p3+p3'),('G','budget-pos2'),('strong','f*f-Delta*I*I'),('uu','V*V+2*V*y+y*y'),('auxiliary','Q*V*V+(1-Q)*uu'),('Dt','1+L*L+L*k'),('U2','U*U'),('ga','G*U2'),('db','Dt*U2'),('N','Z**4-2*Z*Z*(ga+db)+(ga-db)**2'),('P','N*strong*auxiliary+strong*auxiliary-1')]
    sy={v:S.Symbol(v) for v in set(g['variables']+list(ports)+[n for n,f in front])}
    cuts={};covered=set();ns=g['nodes']
    def expr(i,memo):
        if i in cuts:return cuts[i]
        if i in memo:return memo[i]
        covered.add(i);row=ns[i];kind=row[0]
        if kind=='integer':x=S.Integer(row[1])
        elif kind in ('variable','coefficient'):x=sy[row[1]]
        else:
            a,b=expr(row[1],memo),expr(row[2],memo)
            x=a+b if kind=='add' else a-b if kind=='sub' else a*b
        memo[i]=x;return x
    for name,formula in front:
        index=g['named_registers'][name]
        need(S.expand(expr(index,{})-S.sympify(formula,locals=sy))==0,'independent formula '+name)
        cuts[index]=sy[name]
    need(covered==set(range(len(ns))),'independent formula coverage')
    need(g['output']==g['named_registers']['P'],'formula output')

v_aux,y_aux,q_aux=S.symbols('v_aux y_aux q_aux')
u_aux=(v_aux+y_aux)**2
need(S.expand(u_aux-q_aux*(u_aux-v_aux*v_aux)-(v_aux*v_aux-(q_aux-1)*y_aux*(2*v_aux+y_aux)))==0,'shared auxiliary exact whole-polynomial identity')

receipts=[]
for degree,ops in [(85,110),(87,108)]:
    path=ROOT/f'integer14_degree{degree}.json';g=json.loads(path.read_text());ns=g['nodes']
    bind_full_formula(g,degree)
    need(g['variable_count']==len(g['variables'])==14,'variable count')
    need(len(set(g['variables']))==14,'duplicate variables')
    vals=[];seen=set()
    for i,row in enumerate(ns):
        kind=row[0]
        if kind in ('add','sub','mul'):
            need(all(type(k)==int and 0<=k<i for k in row[1:]),'topology')
            a,b=(vals[k] for k in row[1:])
            val=mul(a,b) if kind=='mul' else add(a,b,1 if kind=='add' else -1)
        elif kind=='integer':val={0:row[1]%MOD} if row[1]%MOD else {}
        elif kind=='coefficient':val={0:ports[row[1]]}
        elif kind=='variable':val={} if row[1] in ('C','h') else {1:1}
        else:raise ValueError('unknown node')
        vals.append(val)
    def visit(i):
        if i in seen:return
        seen.add(i)
        if ns[i][0] in ('add','sub','mul'):
            visit(ns[i][1]);visit(ns[i][2])
    visit(g['output'])
    need(seen==set(range(len(ns))),'dead node')
    need({r[1] for r in ns if r[0]=='variable'}==set(g['variables']),'variable liveness')
    need({r[1] for r in ns if r[0]=='coefficient'}==set(ports),'port liveness')
    counts=dict(Counter(r[0] for r in ns if r[0] in ('add','sub','mul')))
    need(sum(counts.values())==ops==g['operations'] and counts==g['operation_counts'],'operation count')
    poly=vals[g['output']]
    need(max(poly)==degree,'attained exact fixed-slice degree')
    q=6*ports['beta']%MOD;a=12*q%MOD;R=pow(q,4,MOD);u=96*pow(q,4,MOD)%MOD;l=12*pow(q,5,MOD)%MOD
    strong=-64*a*a;aux=2*a*a*R
    if degree==85:
        budget=-pow(q,10,MOD)*(ports['cone_A']**2+4+pow(q,4,MOD))
        n=-4*pow(u,4,MOD)*budget*l*l
    else:
        budget=-pow(q,8,MOD)*R*R
        n=pow(u,4,MOD)*(budget-l*l)**2
    expected=n*strong*aux%MOD
    need(poly[degree]==expected and expected!=0,'formal leading coefficient at authentic ports')
    receipts.append({'degree':degree,'operations':ops,'operation_counts':counts,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'all_nodes_and_fourteen_variables_and_six_ports_live':True,'all_literal_registers_independently_bound':True,'authentic_fixed_slice':'C=h=0; all other variables=t','prime':MOD,'top_coefficient_mod_prime':expected,'weighted_norm_degree':d85 if degree==85 else d87})
result={'status':'PASS','optimized':not __debug__,'coefficient_payloads_authenticated':6,'norm_factorization':'all four signed factors exact','signed_carrier_identity':'exact','shared_auxiliary_whole_polynomial_identity':'exact','endpoints':receipts,'scope':'Finite identities, authenticated arithmetic and exact degree/cost. Signed unbounded reduction is in independent review; inherited native/compiler calibration is not re-proved.'}
output=ROOT/'review'/('INDEPENDENT_OPTIMIZED.json' if not __debug__ else 'INDEPENDENT_NORMAL.json')
output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
