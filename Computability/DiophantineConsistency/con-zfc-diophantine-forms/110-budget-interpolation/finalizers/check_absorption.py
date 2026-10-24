#!/usr/bin/env python3
"""Independent checks for bounded-guard absorption. Imports no builder."""
import ast,gzip,hashlib,itertools,json,math
from pathlib import Path
ROOT=Path(__file__).resolve().parent
P=1000000007
p=json.loads((ROOT/'absorbed15_degree176.json').read_text())
dag=json.loads((ROOT/'absorbed15_degree176_dag.json').read_text())
checks={}
def require(c,s):
    if not c:raise ValueError(s)
def expr(s,e,mod=None,degree=False):
    def visit(n):
        if isinstance(n,ast.Name):return e[n.id]
        if isinstance(n,ast.Constant):return 0 if degree else n.value
        if isinstance(n,ast.UnaryOp):return visit(n.operand) if degree else -visit(n.operand)
        a=visit(n.left)
        if isinstance(n.op,ast.Pow):return a*n.right.value if degree else pow(a,n.right.value,mod) if mod else a**n.right.value
        b=visit(n.right)
        if degree:return a+b if isinstance(n.op,ast.Mult) else max(a,b)
        v=a+b if isinstance(n.op,ast.Add) else a-b if isinstance(n.op,ast.Sub) else a*b
        return v%mod if mod else v
    return visit(ast.parse(s,mode='eval').body)
binding=json.loads((ROOT/p['coefficient_binding']).read_text());ports={}
for n,v in binding['ports'].items():
    raw=gzip.decompress((ROOT/p['coefficient_binding']).parent.joinpath(v['file']).read_bytes())
    require(hashlib.sha256(raw).hexdigest()==v['sha256_raw'],'coefficient '+n)
    ports[n]=int.from_bytes(raw,'little')%P
require(len(p['variables'])==len(set(p['variables']))==15,'variable census')
env={n:0 for n in ports};env.update({n:1 for n in p['variables']})
for n,f in p['polynomial_abbreviations']:env[n]=expr(f,env,degree=True)
require(env['norm15']==176,'safe degree bound')
checks['degree_upper_bound']=176
live=set()
def mark(r):
    if r[0]!='node':return
    i=r[1]
    if i in live:return
    live.add(i)
    for a in dag['nodes'][i][1:]:mark(a)
mark(dag['output'])
require(live==set(range(len(dag['nodes']))),'all gates live')
for i,(op,a,b) in enumerate(dag['nodes']):
    require(op in ['add','sub','mul'],'gate syntax')
    for r in (a,b):require(r[0] in ['node','leaf','const'] and (r[0]!='node' or 0<=r[1]<i),'topology')
leafs={r[1] for node in dag['nodes'] for r in node[1:] if r[0]=='leaf'}
require(leafs==set(p['variables']+p['fixed_numerals']),'exact live leaf closure')
checks['live_variables']=len(p['variables'])
checks['live_fixed_ports']=len(p['fixed_numerals'])
checks['operations']=len(dag['nodes'])
checks['counts']={op:sum(n[0]==op for n in dag['nodes']) for op in ['add','sub','mul']}
slopes=p['degree_certificate']['slopes']
def evaluate(t):
    e=ports|{n:s*t%P for n,s in slopes.items()}
    for n,f in p['polynomial_abbreviations']:e[n]=expr(f,e,P)
    vals=[]
    def get(r):return r[1]%P if r[0]=='const' else e[r[1]] if r[0]=='leaf' else vals[r[1]]
    for op,a,b in dag['nodes']:
        x,y=get(a),get(b);vals.append((x+y if op=='add' else x-y if op=='sub' else x*y)%P)
    require(get(dag['output'])==e['norm15'],'DAG/packet evaluation')
    return e['norm15']
row=[evaluate(t) for t in range(177)]
for _ in range(176):row=[(b-a)%P for a,b in zip(row,row[1:])]
lead=row[0]*pow(math.factorial(176)%P,-1,P)%P
require(lead==p['degree_certificate']['final_leading_coefficient_mod_prime']!=0,'independent leading coefficient')
checks['leading_coefficient_mod_prime']=lead
n=0
for q,a,b,k,eta,t in itertools.product(range(-3,4),range(-4,5),range(-4,5),range(-3,4),range(-4,5),range(-2,3)):
    G=a*b-(q-a-b)**2;Z=eta*(k-eta);guard=G*Z-(t*t-G-Z+1)**2-1
    require(12*(guard+1)<=q*q*k*k,'universal guard bound diagnostic')
    for s in (1,2,3):require(guard-q*q*k*k*s<0,'absorption diagnostic')
    n+=1
checks['finite_guard_and_absorption_cases']=n
n=z=0
for a,b,c,t in itertools.product(range(-5,6),range(-5,6),range(-5,11),range(-20,21)):
    A=4*a+1;B=4*b+1;x=2*t+1;U=t*(t+1)-a-B+4*c;M=U*U+4*x*x*c-A*B;N=M*M-16*x*x*U*U*c
    if N==0:
        require(all(v>=0 and math.isqrt(v)**2==v for v in (A,B,c)),'parity square recovery diagnostic')
        z+=c==0
    n+=1
checks['finite_parity_cases']=n;checks['zero_C_norm_zeros']=z
require(z>0,'zero C corner actually tested')
checks['status']='pass; finite diagnostics supplement the universal proof'
(ROOT/'ABSORPTION_CHECKS.json').write_text(json.dumps(checks,indent=2,sort_keys=True)+'\n')
print(json.dumps(checks,indent=2,sort_keys=True))
