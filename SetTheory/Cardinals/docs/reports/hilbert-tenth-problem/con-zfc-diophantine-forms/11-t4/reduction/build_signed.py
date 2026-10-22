"""Own deterministic circuit emitter and bounded diagnostic checker.

Input JSON packets are read as inert data. No received repository program is
executed, no giant coefficient is materialized, and no halting test is run.
The general proof and uniform leading forms are in SIGNED_DOMAIN_PROOF.md.
"""
from pathlib import Path
import collections, hashlib, json, random

ROOT=Path(__file__).resolve().parent
SRC=ROOT.parent/'comparison'
POS=('Jrep','F','alpha','transport_quotient','i','s','w','eta','zeta')
FREE=('h','f','auxiliary_quotient','gamma','tau_root','y_aux')
FACTOR_NAMES=('norm_first','norm_main','norm_aux','norm_index','norm_transport','norm_strong')
EXPECTED_DEGREES=(44,35,50,13,4,44)
P=1_000_000_007

def prefix():
    ports=[]; gates=[]
    for x in POS:
        u,v,r=(x+'__'+t for t in ('u','v','r'))
        ports.extend((u,v,r))
        gates.extend([
            [x+'__u2','*',u,u], [x+'__v2','*',v,v],
            [x+'__rp1','+',r,1], [x+'__rrp1','*',r,x+'__rp1'],
            [x+'__uv2','+',x+'__u2',x+'__v2'],
            [x+'__sum','+',x+'__uv2',x+'__rrp1'],
            [x,'+',x+'__sum',1]])
    return ports+list(FREE),gates

def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b,sign=1):
    c=[0]*max(len(a),len(b))
    for j,v in enumerate(a):c[j]+=v
    for j,v in enumerate(b):c[j]+=sign*v
    return trim([v%P for v in c])
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b):c[j+k]=(c[j+k]+x*y)%P
    return trim(c)
def poly_eval(packet,seed):
    rng=random.Random(seed)
    e={v:[rng.randrange(1,100),rng.randrange(1,100)] for v in packet['witnesses']}
    e.update(dict(zip(packet['fixed_numerals'],([31],[97],[6],[35]))))
    for name,op,x,y in packet['source']:
        a=[x%P] if isinstance(x,int) else e[x]
        b=[y%P] if isinstance(y,int) else e[y]
        e[name]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
    return e
def integer_eval(packet,values):
    e=values.copy()
    for name,op,x,y in packet['source']:
        a=x if isinstance(x,int) else e[x]
        b=y if isinstance(y,int) else e[y]
        e[name]=a*b if op=='*' else a+b if op=='+' else a-b
    return e
def ledger(gates):
    d=collections.Counter(g[1] for g in gates)
    return {'multiplications':d['*'],'additions_subtractions':d['+']+d['-'],'total':len(gates)}
def compact(e):
    J,F,alpha,z,i,s,w,eta,zeta=(e[x] for x in POS)
    h,f,T,gamma,tau,y=(e[x] for x in FREE)
    q=e['Bm1']*J+1; C=q-F-alpha; X=w*q; Y=s*q**3; E=X*Y
    k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
    D=X+a*c+gamma*H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(e['MC']+q*e['MF'])*J
    V=c*(T*f-1)-R*f*f; I=i*c*c; S=Delta*(f*f-1)
    factors=[tau*tau-E*k*Y*(E*k*Y+k),D*D-Delta*c*c,
             S*(V*V-y*y)+y*y,k-h*E-R,
             (e['Kconstant']+w)*C+q-F-z*(q-1),1+I*I-S]
    prod=1
    for value in factors:prod*=value
    return factors,prod-1,sum((value-1)**2 for value in factors)

receipts={}
for kind,source_file,total,degree in (
    ('product','hybrid_product69.json',132,190),
    ('system','hybrid_system61.json',124,50),
    ('sos','hybrid_sos78.json',141,100)):
    original=json.loads((SRC/source_file).read_text())
    ports,gates=prefix()
    packet={**original,'name':'Signed 33-variable '+kind,
            'witnesses':ports,'witness_domain':'unrestricted integers',
            'source':gates+original['source'],
            'positive_original_ports':list(POS),'free_signed_original_ports':list(FREE),
            'proof':'SIGNED_DOMAIN_PROOF.md',
            'coefficient_recipe':'../bridge/T4_CONSTANTS.json',
            'fallback_coefficient_recipe':'../comparison/sources/06-blank67/data/k215_constants.json',
            'equivalence':'Existence of unrestricted integer solutions is equivalent to K215 blank halting.',
            'ledger':ledger(gates+original['source'])}
    for key in ('exact_degree','exact_maximum_degree','factor_degrees','residual_degrees'):
        packet.pop(key,None)
    if kind=='system':
        packet['exact_maximum_degree']=degree
        packet['residual_degrees']=list(EXPECTED_DEGREES)
    else:packet['exact_degree']=degree
    if kind=='product':packet['factor_degrees']=list(EXPECTED_DEGREES)
    assert len(ports)==33 and len(set(ports))==33
    assert packet['ledger']['total']==total
    seen=set(ports+packet['fixed_numerals'])
    for name,op,x,y in packet['source']:
        assert name not in seen and op in ('+','-','*')
        assert all(isinstance(v,int) or v in seen for v in (x,y))
        seen.add(name)
    outputs=([packet['output']] if 'output' in packet
             else [v for pair in packet['comparisons'] for v in pair if isinstance(v,str)])
    live=set(outputs)
    for name,op,x,y in reversed(packet['source']):
        assert name in live, ('dead gate',kind,name)
        live.update(v for v in (x,y) if isinstance(v,str))
    assert set(ports).issubset(live)
    line_checks=[]
    for seed in (101,102,103):
        result=poly_eval(packet,seed)
        if kind=='system':
            got=[]
            for x,y in packet['comparisons']:
                a=[x] if isinstance(x,int) else result[x]
                b=[y] if isinstance(y,int) else result[y]
                got.append(len(add(a,b,-1))-1)
            assert got==list(EXPECTED_DEGREES),(kind,got)
        else:
            got=len(result[packet['output']])-1
            assert got==degree,(kind,got)
        line_checks.append(got)
    for seed in range(40):
        rng=random.Random(seed)
        values={x:rng.randrange(-3,4) for x in ports}
        values.update({'Bm1':31,'Kconstant':97,'MC':6,'MF':35})
        result=integer_eval(packet,values)
        factors,product,sos=compact(result)
        if kind=='product':
            assert result[packet['output']]==product
            assert [result[x] for x in FACTOR_NAMES]==factors
        elif kind=='sos':assert result[packet['output']]==sos
        else:
            residuals=[]
            for x,y in packet['comparisons']:
                a=x if isinstance(x,int) else result[x]
                b=y if isinstance(y,int) else result[y]
                residuals.append(a-b)
            assert residuals==[v-1 for v in factors]
    name='signed33_'+kind+'.json'
    (ROOT/name).write_text(json.dumps(packet,indent=2)+'\n')
    receipts[name]={'variables':len(ports),'ledger':packet['ledger'],
                    'exact_degree_or_maximum':degree,
                    'uniform_degree_proof':'SIGNED_DOMAIN_PROOF.md',
                    'diagnostic_line_degrees':line_checks,
                    'independent_formula_evaluations':40,'all_gates_and_ports_live':True,
                    'sha256':hashlib.sha256((ROOT/name).read_bytes()).hexdigest()}
(ROOT/'SIGNED_VALIDATION.json').write_text(json.dumps({
    'status':'PASS','source_pin':'3b201cdea32d2c816f5f3d20734051f25fd3ef14',
    'scope':'Finite schema, sharing, count, exact-integer formula, and modular weighted-degree diagnostics. Mathematical proof supplied separately; not a proof of consistency.',
    'packets':receipts},indent=2)+'\n')
print(json.dumps(receipts,indent=2))
