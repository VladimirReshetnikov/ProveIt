#!/usr/bin/env python3
"""Independent finite audit of both Pell-doubling one-square equations.

This checks the finite algebra, complete evaluator, coefficient binding,
degree, and coprimality identities. It does not prove unbounded native
calibration or consistency. Requires only Python 3's standard library.
"""
from collections import Counter
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
import argparse
import ast
import gzip
import json
import math

HERE = Path(__file__).resolve().parent

def require(test, message):
    if not test:
        raise ValueError(message)

def constant(n): return {():n} if n else {}
def variable(s): return {(s,):1}
def add(a,b,sign=1):
    out=dict(a)
    for m,n in b.items(): out[m]=out.get(m,0)+sign*n
    return {m:n for m,n in out.items() if n}
def multiply(a,b):
    out={}
    for m,n in a.items():
        for k,l in b.items():
            key=tuple(sorted(m+k)); out[key]=out.get(key,0)+n*l
    return {m:n for m,n in out.items() if n}
def power(a,n):
    out=constant(1)
    for _ in range(n): out=multiply(out,a)
    return out
def expression(text):
    root=ast.parse(text,mode='eval').body
    def visit(node):
        if isinstance(node,ast.Name): return variable(node.id)
        if isinstance(node,ast.Constant) and type(node.value) is int: return constant(node.value)
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
            return multiply(constant(-1),visit(node.operand))
        require(isinstance(node,ast.BinOp), 'Polynomial-only expression')
        if isinstance(node.op,ast.Pow):
            require(isinstance(node.right,ast.Constant) and type(node.right.value) is int and node.right.value>=0,
                    'Nonnegative literal exponent')
            return power(visit(node.left),node.right.value)
        a,b=visit(node.left),visit(node.right)
        if isinstance(node.op,ast.Mult): return multiply(a,b)
        if isinstance(node.op,ast.Add): return add(a,b)
        if isinstance(node.op,ast.Sub): return add(a,b,-1)
        raise ValueError('Polynomial-only expression')
    return visit(root),{node.id for node in ast.walk(root) if isinstance(node,ast.Name)}
def substitute(poly,mapping):
    out={}
    for monomial,coefficient in poly.items():
        term=constant(coefficient)
        for name in monomial: term=multiply(term,mapping.get(name,variable(name)))
        out=add(out,term)
    return out

def formulas(weight):
    return [
        ('bJ','beta*J'), ('q','bJ+1'), ('C','q-F-alpha'),
        ('X','w*q'), ('k','eta+zeta'), ('c','k*Y+eta'),
        ('mu','q*q+1'), ('Am1','mu*Y*(X+1)'),
        ('Hp','4*Am1-1'), ('V0','X*mu*mu*Y*Y'),
        ('Dtau','1+V0*(V0+1)*k*k'),
        ('R','(bJ*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J'),
        ('e','k-R-1'), ('Bt','(K0+w)*C-F'),
        ('Delta','Am1*(Am1+2)'), ('U','i*c*c'),
        ('DpI2','Delta*U*U*Dtau'), ('Df','1+DpI2'),
        ('Fsqr','1+4*DpI2*Df'),
        ('Q','4*Delta*DpI2*Df'),
        ('cTR','c*(T+alpha)-R'), ('V','Df*cTR-c'),
        ('P1','q*q*q*bJ'),
        ('center','n-'+('cTR*V' if weight=='bV' else 'V*V')+'*Bt'), ('Kpos','X*(3*c-2*X)+2'),
        ('Znum','P1*mu*mu*(Hp*center+Kpos)+Hp*(mu*mu*(bJ*Y-q*q*q*Bt)-P1*e)'),
        ('Mtot','P1*mu*mu*Hp'), ('Dg','Dtau*Df'),
        ('N','(Q-1)*Znum*Znum-Mtot*Mtot*Dg*(Q*V*V-1)'),
    ]

def audit(packet):
    inputs=['J','F','alpha','i','T','w','Y','n','eta','zeta']
    ports=['beta','K0','MC','MF']
    require(packet['witnesses']==inputs and packet['fixed_numerals']==ports,
            'Quantified input/constant signature changed')
    require(packet['domain']=='strictly positive integers' and packet['output']=='N',
            'Domain or output changed')
    rows=packet['source']; known=set(inputs+ports); degrees={x:1 for x in inputs}|{x:0 for x in ports}
    definitions={}
    for name,op,a,b in rows:
        require(name not in known and op in ('+','-','*'), 'Invalid gate')
        require(all(isinstance(x,int) or x in known for x in (a,b)), 'Non-topological gate')
        definitions[name]=(op,a,b); known.add(name)
        da,db=[0 if isinstance(x,int) else degrees[x] for x in (a,b)]
        degrees[name]=da+db if op=='*' else max(da,db)
    live=set(); todo=['N']
    while todo:
        name=todo.pop()
        if isinstance(name,int) or name in live:
            continue
        live.add(name)
        if name in definitions:
            todo.extend(definitions[name][1:])
    require(live==known, 'Dead or unbound gate/input/port')
    small=packet['transport_weight']=='bV'
    require(packet['transport_weight'] in ('bV','V2'), 'Specified transport weight')
    count=85 if small else 84; degree=328 if small else 436
    require(len(rows)==count==packet['operations'], 'Operation count')
    require(dict(Counter(r[1] for r in rows))=={'*':51 if small else 50,'+':19,'-':15}==packet['operation_breakdown'],
            'Operation breakdown')
    covered=set(); available=set(inputs+ports)
    interfaces=[]
    for target,text in formulas(packet['transport_weight']):
        if target=='V': text='Fsqr*cTR-c'
        wanted,boundary=expression(text)
        require(boundary<=available, 'Unjustified semantic boundary '+target)
        memo={name:variable(name) for name in boundary}
        def expand_node(name):
            if isinstance(name,int): return constant(name)
            if name in memo: return memo[name]
            require(name in definitions, 'Unbound interface leaf '+name)
            op,a,b=definitions[name]; covered.add(name)
            aa,bb=expand_node(a),expand_node(b)
            result=multiply(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
            memo[name]=result
            return memo[name]
        actual=expand_node(target)
        require(actual==wanted, 'Literal polynomial interface '+target)
        interfaces.append(target); available.add(target)
    require(covered==set(definitions), 'Every literal gate must be covered')
    require(degrees['N']==degree and packet['exact_degree']==degree,
            'Global degree upper bound')
    return degrees,interfaces

def polynomial_ray(packet,constants,prime=2305843009213693951):
    # Exact arithmetic in F_p[t], with every unknown replaced by t.
    def trim(a):
        while a and not a[-1]: a.pop()
        return a
    def plus(a,b,sgn=1):
        ans=list(a)+[0]*max(0,len(b)-len(a))
        for j,x in enumerate(b): ans[j]=(ans[j]+sgn*x)%prime
        return trim(ans)
    def times(a,b):
        ans=[0]*(len(a)+len(b)-1) if a and b else []
        for j,x in enumerate(a):
            if x:
                for k,y in enumerate(b):
                    if y: ans[j+k]=(ans[j+k]+x*y)%prime
        return trim(ans)
    env={x:[0,1] for x in packet['witnesses']}|{x:[n%prime] for x,n in constants.items()}
    for name,op,a,b in packet['source']:
        aa=[a%prime] if isinstance(a,int) else env[a]
        bb=[b%prime] if isinstance(b,int) else env[b]
        env[name]=times(aa,bb) if op=='*' else plus(aa,bb,1 if op=='+' else -1)
    beta=constants['beta']%prime
    if packet['transport_weight']=='bV':
        degree=328
        expected=-(2**10)*pow(beta,156,prime)*pow(2,44,prime)*pow(beta-1,2,prime)%prime
    else:
        degree=436
        expected=2**14*pow(beta,200,prime)*pow(2,60,prime)*pow(beta-1,4,prime)*pow(beta-2,2,prime)%prime
    require(expected!=0 and len(env['N'])-1==degree and env['N'][-1]==expected,
            'Attained degree over the actual coefficient tuple')
    return {'prime':prime,'degree':degree,'leading_coefficient_mod_prime':expected}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    packets=[json.loads((HERE/f'equation_{n}.json').read_text()) for n in (84,85)]
    packet=packets[0]
    constants={}; payloads=[]
    for name,pin in packet['coefficient_binding']['ports'].items():
        data=(HERE/'coefficients'/pin['file']).read_bytes(); raw=gzip.decompress(data)
        value=int.from_bytes(raw,'little')
        require(sha256(data).hexdigest()==pin['gzip_sha256'], 'Gzip binding '+name)
        require(sha256(raw).hexdigest()==pin['raw_sha256'], 'Raw binding '+name)
        require(value.bit_length()==pin['bits'] and len(raw)==(value.bit_length()+7)//8,
                'Canonical coefficient encoding '+name)
        constants[name]=value;payloads.append({'name':name,'bits':value.bit_length(),'raw_sha256':pin['raw_sha256']})
    be=constants['beta'];require(be>=31 and be%2==1 and constants['K0']>0 and
                                0<constants['MC']<be<constants['MF']<2*be,'Whole coefficient box')
    parent=(HERE/'parent-equation.json').read_bytes()
    require(sha256(parent).hexdigest()==packet['parent_sha256'],'Parent binding')
    require(json.loads(parent)['coefficient_binding']==packet['coefficient_binding'], 'Whole tuple retained')
    # Exact Pell doubling and coprimality identities, at free boundaries.
    ex=lambda s:expression(s)[0]
    require(ex('(1+2*a)**2-(1+4*a*(1+a))')=={}, 'Polynomial doubled trace')
    require(ex('Dlt*(1+4*Dlt*U*U*E*(1+Dlt*U*U*E)-1)-4*Dlt*Dlt*U*U*E*(1+Dlt*U*U*E)')=={},
            'Q is polynomial multiple of G')
    require(ex('(1+2*Dlt*U*U*E)**2-1-4*Dlt*U*U*E*(1+Dlt*U*U*E)')=={},
            'Strong Pell norm after G becomes a square')
    # Every term is checked in the polynomial ring, including carrier clearing.
    Z=ex('q**3*h*mu**2*(H*(n-L*B)+K)+H*(mu**2*(h*Y-q**3*B)-q**3*h*e)')
    cleared=ex('q**3*h*mu**2*H*n+q**3*h*mu**2*K+h*mu**2*H*Y-q**3*mu**2*H*(1+h*L)*B-q**3*h*H*e')
    require(Z==cleared,'Entire rational carrier clearing')
    require(ex('(Q-1)*Z*Z-RG*(Q*V*V-1)-Q*(Z*Z-RG*V*V)-RG+Z*Z')=={},
            'One-operation finalizer saving')
    require(ex('8*(F-1)**2-4*F*(F-1)')==ex('4*(F-1)*(F-2)'),
            'Fifth-index bound inequality numerator')
    require(ex('8*Q*Q-20*Q+5')==substitute(ex('8*x*x+28*x+17'),{'x':ex('Q-3')}),
            'Fifth-index lower bound Q>=3')
    # Independent finite stress controls supplement the general gcd proof.
    controls=0
    for aa in range(2,8):
        dd=aa*aa-1
        for cc in range(1,8):
            for ii in range(1,5):
                for ee in range(2,9):
                    uu=ii*cc*cc; f0=1+dd*uu*uu*ee; gg=ee*f0
                    fsqr=1+4*(f0-1)*f0
                    qq=dd*(fsqr-1); de=qq-1
                    for bb in (-2,-1,0,1,3):
                        vv=fsqr*bb-cc; dy=qq*vv*vv-1
                        require(math.gcd(ee,f0)==1 and math.gcd(gg,de*dy)==1,
                                'Coprime factor stress control')
                        controls+=1
    # Mutating actual circuit gates must be detected by the semantic collector.
    results=[]
    for packet in packets:
        degrees,interfaces=audit(packet)
        require(packet['coefficient_binding']==packets[0]['coefficient_binding'],'Same whole tuple for both equations')
        rejections=[]
        for label,target,column,value in [
            ('wrong doubling factor','fouraF0',2,2),
            ('undoubled auxiliary base','DfcTR',2,'Df'),
            ('wrong transport weight','LBt',2,'cTR'),
            ('missing positive center input','center',2,1),
            ('wrong final sign','N',1,'-'),
        ]:
            bad=deepcopy(packet);next(r for r in bad['source'] if r[0]==target)[column]=value
            try: audit(bad)
            except (ValueError,KeyError): rejections.append(label)
            else: raise ValueError('Undetected actual mutation '+label)
        results.append({
            'name':packet['name'],'operations':packet['operations'],
            'operation_breakdown':packet['operation_breakdown'],'exact_degree':packet['exact_degree'],
            'semantic_interfaces':interfaces,'all_live_gates_checked':packet['operations'],
            'degree_bounds':{k:degrees[k] for k in ['Am1','c','U','Dtau','Df','Fsqr','Q','V','Dg','Znum','Mtot','RGV2','Z2','Qinside','N']},
            'exact_polynomial_ray':polynomial_ray(packet,constants),
            'actual_mutations_rejected':rejections,
        })
    result={
        'status':'passed','variables':10,'domain':packet['domain'], 'equations':results,
        'actual_fixed_tuple':payloads,
        'gcd_stress_controls':controls,
        'scope':'Finite specification, exact algebra, complete evaluator, actual tuple, and global degree. Unbounded equivalence is proved in PROOF.md relative to the retained native-source contracts.'
    }
    text=json.dumps(result,indent=2)+'\n'
    if args.output: args.output.write_text(text)
    print(text,end='')

if __name__=='__main__': main()
