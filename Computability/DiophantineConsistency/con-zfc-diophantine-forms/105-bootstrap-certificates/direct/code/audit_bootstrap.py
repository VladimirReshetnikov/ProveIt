#!/usr/bin/env python3
"""Exact source/interface audits and finite controls for the new lemmas.

The universal mathematical arguments are in proofs/NEW_RESULTS.md.
Finite tests are explicitly not substitutes for these arguments.
"""
from __future__ import annotations
import ast
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
import math
from pathlib import Path
import random
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'code'),str(ROOT/'provenance/upstream')]
from bootstrap_builder import construct,DeferredBinomialMixin,LOCAL_NAMES
from bootstrap_factorial import BootstrapFactorialBuilder
from bootstrap_frame_audit import bootstrap_frame_audit
from verify_synchronized import need,majorant,product_index_audit,exact_expansion

class CompleteBuilder(DeferredBinomialMixin,BootstrapFactorialBuilder):
    pass

def read(path): return json.loads(path.read_text())

def inherited_pins():
    pins=read(ROOT/'PROVENANCE.json')['inherited_file_sha256']
    for path,digest in pins.items():
        relative=Path(path)
        need(not relative.is_absolute() and '..' not in relative.parts
             and relative.as_posix()==path and '\\' not in path,
             'nonportable inherited file path: '+path)
        need('__pycache__' not in relative.parts and relative.suffix not in ('.pyc','.pyo'),
             'ephemeral bytecode must not be pinned: '+path)
        need(sha256((ROOT/path).read_bytes()).hexdigest()==digest,'inherited file changed: '+path)
    return len(pins)

def get_function(path):
    return next(n for n in ast.parse(path.read_text()).body
                if isinstance(n,ast.FunctionDef) and n.name=='source_pair_calculus')

def is_assignment(node,name):
    return isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in node.targets)

def constructor_audit():
    old=get_function(ROOT/'code/direct_source_factored.py')
    new=get_function(ROOT/'code/hybrid_source.py')
    def prefix(fn,end):
        return deepcopy(fn.body[:next(i for i,n in enumerate(fn.body) if is_assignment(n,end))])
    a,b=prefix(old,'pq'),prefix(new,'carrier')
    def tuple_binding(body):
        return next((i,n) for i,n in enumerate(body) if isinstance(n,ast.Assign)
                    and isinstance(n.targets[0],ast.Tuple)
                    and any(isinstance(x,ast.Name) and x.id=='a' for x in n.targets[0].elts))
    i,oi=tuple_binding(a);j,nj=tuple_binding(b)
    need([x.id for x in oi.targets[0].elts]==['a','b','c','d','p','q','v'],'old inputs')
    need([x.id for x in nj.targets[0].elts]==['a','b','c','d','v'],'new inputs')
    a[i]=nj
    dump=lambda z:[ast.dump(x,include_attributes=False) for x in z]
    need(dump(a)==dump(b),'constructor prefix changed beyond premise projection')
    need(LOCAL_NAMES==('v','a','b','c','d','S','Sp','u','vq'),'local columns differ')
    return {'constructor_prefix_exact_AST_match':True,'projected_coordinates':['p','q'],
            'local_columns':list(LOCAL_NAMES),'carrier_label_bound':'I(m,m)+2=8*m^2+8*m+2'}

def factorial_controls():
    count=0;linear=0
    for n in range(13):
        K=math.factorial(n)
        values=set(range(401))|set(range(max(0,K-12),K+13))
        for F in values:
            R=F*F;C=math.comb(R+n,n);N=(R+1)**n
            ceiling=(N+C-1)//C
            need((F==ceiling)==(F==K),'bootstrap factorial fixed point counterexample')
            count+=1
            Rlinear=n*n*F;Cl=math.comb(Rlinear+n,n);Nl=(Rlinear+1)**n
            need((F==(Nl+Cl-1)//Cl)==(F==K),'linear-radius fixed point counterexample')
            linear+=1
    shared=0
    for H in range(1,25):
        R=math.factorial(H)**2
        for n in range(H+1):
            C=math.comb(R+n,n);N=(R+1)**n;F=(N+C-1)//C
            need(F==math.factorial(n),'shared radius factorial mismatch')
            remainder=N+C-C*F-1;slack=C-remainder-1
            need(remainder>=0 and slack>=0,'ceiling witnesses not natural')
            need(N+C==C*F+remainder+1 and C==remainder+slack+1,'ceiling rows')
            shared+=1
    return {'bootstrap_fixed_point_controls':count,'linear_radius_fixed_point_controls':linear,'shared_radius_controls':shared,
            'scope':'Finite regression controls; the unrestricted proof is NEW_RESULTS.md.'}

def abstract_source_controls():
    fn=get_function(ROOT/'code/hybrid_source.py')
    fn=deepcopy(fn)
    for n in fn.body:
        if is_assignment(n,'codes'):
            n.value=ast.Attribute(value=ast.Name(id='self',ctx=ast.Load()),attr='codes',ctx=ast.Load())
    module=ast.fix_missing_locations(ast.Module(body=[fn],type_ignores=[]))
    namespace={};exec(compile(module,'abstract_hybrid_source','exec'),namespace)
    f=namespace['source_pair_calculus']
    class Numeric:
        def __init__(self,codes): self.codes=[('c',n) for n in codes]
        def add(self,a,b): return ('c',a[1]+b[1])
        def mul(self,a,b): return ('c',a[1]*b[1])
        def square(self,a):return self.mul(a,a)
        def sum(self,xs):return ('c',sum(x[1] for x in xs))
        def product(self,xs):return ('c',math.prod(x[1] for x in xs))
        def pair_add(self,p,q):return self.add(p[0],q[0]),self.add(p[1],q[1])
        def pair_mul(self,p,q):return self.add(self.mul(p[0],q[0]),self.mul(p[1],q[1])),self.add(self.mul(p[0],q[1]),self.mul(p[1],q[0]))
        def pair_square(self,p):return self.add(self.square(p[0]),self.square(p[1])),self.mul(('c',2),self.mul(p[0],p[1]))
    source={'horn_branches':[{'name':n} for n in ['truth','rho1','rho2','rho3','rho4','rho5','rho6','growG','rho8','bundle','mp','gen']]}
    I=lambda a,b:2*(a+b)*(a+b+1)+4*b
    rng=random.Random(20261023);count=0
    for z in range(600):
        codes=[rng.randrange(20) for _ in range(9)]
        env={k:rng.randrange(8) for k in ['a','b','c','d','v','M0','S','Sp','x','y','u','vq']}
        index=rng.randrange(5);a,b,c,d,v=[env[k] for k in ['a','b','c','d','v']]
        M=env['M0']+1;S,Sp=env['S'],env['Sp'];w=lambda n:1+n*M
        G=((c-a)*(c-b))**2-(d+1)**2
        K=v*math.prod(v-h for h in codes[:8]);B=(v-codes[8])**2+G*G
        LA=Sp*w(v)-S;LM=Sp*w(v)-S*w(a)*w(I(a,v));LG=Sp*w(v)-S*w(b)
        den=1+(index+1)*env['y']
        beta=(env['x']-S-den*env['u'])**2+(env['x']-Sp-(den+env['y'])*env['vq'])**2
        expected=(K*K*B+LA*LA)*LM*LM*((v-I(a,b)-2)**2+LG*LG)+beta
        ep,fp=f(Numeric(codes),source,{k:('c',x) for k,x in env.items()},('c',index),False)
        need(ep[1]-fp[1]==expected,'abstract source pair reconstruction')
        count+=1
    return {'abstract_code_source_controls':count,'scope':'Checks the new signed-pair formula independently with abstract axiom codes; constructor identities checked by AST separately.'}

def factorial_interface(b):
    gates={out:(op,a,c) for (op,a,c),out in b.cache.items()}
    fac=[r for r in b.macro_log if r['macro']=='factorial']
    need(len(fac)==2,'not two factorial requests')
    H=fac[0]['n'];t=fac[1]['n'];F=fac[0]['output'];R=b.factorial_radius
    need(b.factorial_radius_bound==H,'wrong radius bound')
    need(gates[R]==('mul',F,F),'radius is not the square of the first factorial output')
    need(len(b.factorial_radius_log)==2 and all(tuple(z['radius'])==R for z in b.factorial_radius_log),'radii not shared')
    need(gates[t][0]=='add' and ('c',1) in gates[t][1:],'t not positive successor')
    for entry in fac:
        n,out=entry['n'],entry['output']
        plus=next(v for v,(op,a,c) in gates.items() if op=='add' and {a,c}=={R,n})
        need((plus,n) in b.binomials,'factorial binomial absent')
        rplus=next(v for v,(op,a,c) in gates.items() if op=='add' and {a,c}=={R,('c',1)})
        need((rplus,n) in b.powers,'factorial numerator power absent')
    need(set(b.shared_indices)=={k for n,k in b.powers},'an exponent lacks its primitive index graph')
    need(set(b.shared_bases)=={n for n,k in b.powers},'a base lacks its modulus graph')
    need(len(b.shared_indices)==18 and len(b.shared_bases)==7,'changed finite census')
    return {'factorial_requests':2,'radius':'F_H^2','shared_radius':True,
            'primitive_index_certificates':18,'distinct_base_moduli':7,
            'positive_base_argument':'2*A*n=T+n^2+1 with natural T rules out n=0 before factorial decoding.'}

def audit():
    source_bytes=(ROOT/'provenance/upstream/wire_eliminated_source.json').read_bytes()
    b,c=construct(CompleteBuilder,json.loads(source_bytes))
    ans={'status':'PASS','inherited_hashes':inherited_pins(),'constructors':constructor_audit(),
         'majorant':majorant(c),'frame':bootstrap_frame_audit(b,c),
         'index_product':product_index_audit(b),'factorial_interface':factorial_interface(b),
         'factorial_controls':factorial_controls(),'source_controls':abstract_source_controls()}
    for name in ['parent781','parent783','natural469','natural468','natural467']:
        p=ROOT/'equations'/name
        ans[name]=exact_expansion(read(p/'equation.json'),read(p/'expanded_polynomial.json'))
    return ans

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args()
    result=audit()
    if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))
