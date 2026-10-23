#!/usr/bin/env python3
"""Exact small comparison-circuit synthesis; stdlib only."""
import ast, collections, gzip, hashlib, json, random
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PIN='8c6eec9d19ef80538c8e61ff6e0180040583446a'
def require(c,m):
    if not c: raise ValueError(m)
class Ring:
    def __init__(self,names,nvars): self.names=names; self.nvars=nvars; self.zero=(0,)*len(names)
    def const(self,n): return {self.zero:n} if n else {}
    def var(self,n):
        a=list(self.zero);a[self.names.index(n)]=1;return {tuple(a):1}
    def add(self,p,q,sign=1):
        r=dict(p)
        for m,c in q.items():
            r[m]=r.get(m,0)+sign*c
            if not r[m]:del r[m]
        return r
    def mul(self,p,q):
        r={}
        for a,c in p.items():
            for b,d in q.items():
                k=tuple(x+y for x,y in zip(a,b));r[k]=r.get(k,0)+c*d
        return {k:v for k,v in r.items() if v}
    def parse(self,s,env=None):
        env=env or {}
        def f(t):
            if isinstance(t,ast.Name): return env[t.id] if t.id in env else self.var(t.id)
            if isinstance(t,ast.Constant): return self.const(t.value)
            if isinstance(t,ast.BinOp):
                p=f(t.left)
                if isinstance(t.op,ast.Pow):
                    r=self.const(1)
                    for _ in range(t.right.value): r=self.mul(r,p)
                    return r
                q=f(t.right)
                return self.mul(p,q) if isinstance(t.op,ast.Mult) else self.add(p,q,-1 if isinstance(t.op,ast.Sub) else 1)
            if isinstance(t,ast.UnaryOp):return {m:-v for m,v in f(t.operand).items()}
            raise ValueError(ast.dump(t))
        return f(ast.parse(s.replace('^','**'),mode='eval').body)
    def degree(self,p):return max((sum(m[:self.nvars]) for m in p),default=-1)
    def terms(self,p):return [{'powers':list(m),'coefficient':v} for m,v in sorted(p.items())]

class Circuit:
    def __init__(self,inputs): self.source=[]; self.env={x:x for x in inputs};self.cache={}
    def gate(self,op,a,b):
        if op in '+*' and str(a)>str(b):a,b=b,a
        key=(op,a,b)
        if key not in self.cache:
            n='g'+str(len(self.source)+1);self.cache[key]=n;self.source.append([n,op,a,b])
        return self.cache[key]
    def parse(self,s):
        def f(t):
            if isinstance(t,ast.Name):return self.env[t.id]
            if isinstance(t,ast.Constant):return t.value
            if isinstance(t,ast.BinOp):
                a=f(t.left)
                if isinstance(t.op,ast.Pow):
                    require(t.right.value==2,'square only');return self.gate('*',a,a)
                return self.gate({ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(t.op)],a,f(t.right))
            raise ValueError(ast.dump(t))
        return f(ast.parse(s,mode='eval').body)
    def assign(self,n,s):self.env[n]=self.parse(s);return self.env[n]
    def ledger(self,outs,inputs):
        live=set(outs)
        for n,op,a,b in reversed(self.source):
            if n in live:live.update([a,b])
        require(all(n in live for n,_,_,_ in self.source),'dead gate')
        require(all(n in live for n in inputs),'dead input')
        counts=collections.Counter(op for _,op,_,_ in self.source)
        return dict(operations=len(self.source),multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'],all_gates_live=True,all_inputs_live=True)

old=json.loads((ROOT/'upstream/quartic31.json').read_text())
canonical=json.loads((ROOT.parent/'coefficients/COEFFICIENT_BINDING.json').read_text())
require(canonical['instance']=='wang943-mixed-121x8801','unexpected coefficient instance')
aliases={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}
active_files={}
for port,payload in aliases.items():
    record=next(r for r in canonical['files'] if r['port']==payload)
    raw=gzip.decompress((ROOT.parent/'coefficients'/record['file']).read_bytes())
    require(hashlib.sha256(raw).hexdigest()==record['sha256'],'bad active coefficient bytes '+port)
    require(int.from_bytes(raw,'little').bit_length()==record['bit_length'],'bad coefficient bit length '+port)
    active_files[port]=dict(record,path='../coefficients/'+record['file'])
active=dict(schema='complete-fixed-instance-binding-v1',instance=canonical['instance'],
            canonical_binding='../coefficients/COEFFICIENT_BINDING.json',
            path_base='directory containing this INSTANCE.json',
            coefficient_files=active_files,port_aliases=aliases,
            adapter_proof='../coefficients/COEFFICIENT_PROOF.md',
            scope='All four ports use the complete new tuple. Historical upstream metadata is evidence only.',
            mask_convention='MF is MF_source, already shifted by B-1.')
variables=old['variables'];constants=old['constants'];inputs=variables+constants
c=Circuit(inputs)
for n,s in [('rep','beta*J'),('q','rep+1'),('k','eta+zeta'),('H','4*a+3'),('qF','q-F'),('C','qF-alpha'),('Lplus','L+1'),('Y','a-E'),('Q','c-eta'),('T','P-k'),('R','j*c-V')]:c.assign(n,s)
pairs=[('Lplus','q*q'),('N','q*Lplus'),('X','w*q'),('Y','s*N'),('E','X*Y'),('Q','k*Y'),('T','E*Q'),('tau*tau','P*T+1'),('D','X+a*c+gamma*H'),('Delta','a*a+H'),('C2','c*c'),('D*D','Delta*C2+1'),('k','R+1+h*E'),('R','qF*(N-q)-C*L+(MC+q*MF)*J'),('(K0+w)*C','F+z*rep'),('F2','f*f'),('V','o*f-c'),('g','y*y-V*V'),('I','i*C2'),('Baux','I*I'),('Baux','Delta*(F2-1)'),('y*y-Baux*g','1')]
comparisons=[[c.parse(a),c.parse(b)] for a,b in pairs]
ledger=c.ledger([x for p in comparisons for x in p],inputs)
print(ledger)
require(ledger['operations']==60,'unexpected count')
ring=Ring(inputs,len(variables));env={x:ring.var(x) for x in inputs}
for n,op,a,b in c.source:
    p=ring.const(a) if isinstance(a,int) else env[a];q=ring.const(b) if isinstance(b,int) else env[b]
    env[n]=ring.mul(p,q) if op=='*' else ring.add(p,q,-1 if op=='-' else 1)
res=[]
for a,b in comparisons:
    p=ring.const(a) if isinstance(a,int) else env[a];q=ring.const(b) if isinstance(b,int) else env[b]
    res.append(ring.add(p,q,-1))
source_res=[]
for e in old['equations']:
    s=e['residual']
    # source is fully expanded in the witness coordinates. Only z changes.
    ep={'z':ring.parse('z+1')}
    for name,expr in old['affine_abbreviations'].items():ep[name]=ring.parse(expr,ep)
    source_res.append(ring.parse(s,ep))
signs=[]
for p,q in zip(res,source_res):
    sign=1 if p==q else -1 if p=={m:-v for m,v in q.items()} else 0
    require(sign!=0,'residual differs beyond sign');signs.append(sign)
degrees=[ring.degree(p) for p in res]
require(degrees==[2]*22,'non-quadratic residual')
sos={}
for p in res:sos=ring.add(sos,ring.mul(p,p))
require(ring.degree(sos)==4,'not quartic')
tau4=[0]*len(inputs);tau4[variables.index('tau')]=4
require(sos.get(tuple(tau4))==1,'tau fourth power')
base=list(c.source)
rr=[c.gate('-',a,b) for a,b in comparisons]
ss=[c.gate('*',r,r) for r in rr]
out=ss[0]
for sq in ss[1:]:out=c.gate('+',out,sq)
polyledger=c.ledger([out],inputs)
require(polyledger['operations']==125,'SOS count')
def save(n,x):(ROOT/n).write_text(json.dumps(x,indent=2)+'\n')
packet=dict(name='quartic31_comparison60',repository_pin=PIN,witness_domain='strictly positive integers',variables=variables,constants=constants,source=base,comparisons=comparisons,ledger=ledger,exact_maximum_degree=2,equation_count=22,transport_convention='z_old=z+1',active_instance=active['instance'],coefficient_binding_file='INSTANCE.json',coefficient_binding_path_base='directory containing this JSON',formal_status='Exact port-parametric algebraic reduction, instantiated by the complete new adapter; inherited compiler and K215 proofs not re-formalized.')
save('INSTANCE.json',active)
save('quartic31_system60.json',packet)
save('quartic31_sos125.json',dict(packet,name='quartic31_sos125',source=c.source,output=out,ledger=polyledger,exact_degree=4,system_source=base))
save('quartic31_sparse.json',dict(variables=variables,constants=constants,active_instance=active['instance'],coefficient_binding_file='INSTANCE.json',source_residual_signs=signs,equations=[dict(number=i+1,comparison=pairs[i],degree=degrees[i],terms=ring.terms(p)) for i,p in enumerate(res)],sos_terms=ring.terms(sos)))
checks=dict(status='PASS',source_sha256=hashlib.sha256((ROOT/'upstream/quartic31.json').read_bytes()).hexdigest(),source_pin=PIN,exact_residual_agreement_up_to_sign=True,source_residual_signs=signs,residual_degrees=degrees,sos_degree=4,sos_terms=len(sos),tau4_coefficient=1,system_ledger=ledger,polynomial_ledger=polyledger,active_instance=active['instance'],actual_coefficient_hashes={p:r['sha256'] for p,r in active_files.items()},proof_scope='Exact symbolic identities and metric checks; no consistency or solvability test.')
save('QUARTIC60_CHECKS.json',checks)
print(json.dumps(checks,indent=2))
