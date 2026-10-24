#!/usr/bin/env python3
"""Independent universal norm-kernel and exact degree verification.

Newton identities compute the signed-root norm independently of the
builder's repeated quadratic-conjugation circuit. No builder is imported.
"""
import ast
import gzip
import hashlib
import json
import math
from functools import lru_cache
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PRIME=1_000_000_007


def require(condition,message):
    if not condition:
        raise ValueError(message)


def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+sign*c
        if not out[m]: del out[m]
    return out


def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(x+y for x,y in zip(m,n))
            out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}


def constant(v,n): return {} if not v else {(0,)*n:v}


def compositions(total,n):
    if n==1:
        yield (total,)
    else:
        for first in range(total+1):
            for tail in compositions(total-first,n-1):
                yield (first,)+tail


def newton_norm(n):
    """Exact independent product over all signed sums of n square roots."""
    N=2**n
    ps={}
    for j in range(1,N//2+1):
        fact=math.factorial(2*j)
        ps[j]={m: N*fact//math.prod(math.factorial(2*e) for e in m)
               for m in compositions(j,n)}
    coefficients=[constant(1,n)]
    for k in range(1,N//2+1):
        numerator={}
        for j in range(1,k+1):
            numerator=add(numerator,mul(coefficients[k-j],ps[j]))
        require(all(c%(2*k)==0 for c in numerator.values()),'Newton divisibility')
        coefficients.append({m:-c//(2*k) for m,c in numerator.items() if c})
    full={}
    for k,poly in enumerate(coefficients):
        for m,c in poly.items():
            full[(N-2*k,)+m]=c
    return full


@lru_cache(None)
def parsed(expression): return ast.parse(expression,mode='eval').body


def symbolic(expression,env,n):
    def go(node):
        if isinstance(node,ast.Name): return env[node.id]
        if isinstance(node,ast.Constant): return constant(node.value,n)
        if isinstance(node,ast.UnaryOp):
            return {m:-c for m,c in go(node.operand).items()}
        if isinstance(node,ast.BinOp):
            a,b=go(node.left),go(node.right)
            if isinstance(node.op,ast.Add): return add(a,b)
            if isinstance(node.op,ast.Sub): return add(a,b,-1)
            if isinstance(node.op,ast.Mult): return mul(a,b)
        raise ValueError(ast.dump(node))
    return go(parsed(expression))


def audit_kernel(n):
    packet=json.loads((ROOT/('norm'+str(n)+'_kernel.json')).read_text())
    names=['carrier']+['rad'+str(i) for i in range(n)]
    env={name:{tuple(int(i==j) for i in range(n+1)):1}
         for j,name in enumerate(names)}
    for name,expression in packet['polynomial_abbreviations']:
        env[name]=symbolic(expression,env,n+1)
    norm=env[packet['output']]
    independent=newton_norm(n)
    require(norm==independent,'full universal norm'+str(n)+' mismatch')
    top=(0,)*n+(2**(n-1),)
    require(norm[top]==1,'dominant radicand coefficient')
    data={'variables':names,'terms':[{'powers':m,'coefficient':c}
                                    for m,c in sorted(norm.items())]}
    path=ROOT/('norm'+str(n)+'_expanded.json')
    path.write_text(json.dumps(data,separators=(',',':'),sort_keys=True)+'\n')
    return {'radicands':n,'terms':len(norm),'binary_operations':packet['binary_operations'],
            'universal_polynomial_identity':'PASS (Newton identities vs quadratic-conjugation circuit)',
            'expanded_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}


def mod_eval(expression,env):
    def go(node):
        if isinstance(node,ast.Name): return env[node.id]
        if isinstance(node,ast.Constant): return node.value%PRIME
        if isinstance(node,ast.UnaryOp): return -go(node.operand)%PRIME
        if isinstance(node,ast.BinOp):
            a=go(node.left)
            if isinstance(node.op,ast.Pow):
                require(isinstance(node.right,ast.Constant) and isinstance(node.right.value,int) and node.right.value>=0,'exponent')
                return pow(a,node.right.value,PRIME)
            b=go(node.right)
            if isinstance(node.op,ast.Add): return (a+b)%PRIME
            if isinstance(node.op,ast.Sub): return (a-b)%PRIME
            if isinstance(node.op,ast.Mult): return a*b%PRIME
        raise ValueError(ast.dump(node))
    return go(parsed(expression))


def bound(expression,env):
    def go(node):
        if isinstance(node,ast.Name): return env[node.id]
        if isinstance(node,ast.Constant): return 0
        if isinstance(node,ast.UnaryOp): return go(node.operand)
        if isinstance(node,ast.BinOp):
            if isinstance(node.op,ast.Pow): return go(node.left)*node.right.value
            a,b=go(node.left),go(node.right)
            if isinstance(node.op,(ast.Add,ast.Sub)): return max(a,b)
            if isinstance(node.op,ast.Mult): return a+b
        raise ValueError(ast.dump(node))
    return go(parsed(expression))


def audit_degree(name,ports):
    p=json.loads((ROOT/(name+'.json')).read_text())
    n=5 if p['variable_count']==13 else 4
    kernel=json.loads((ROOT/('norm'+str(n)+'_kernel.json')).read_text())
    require(p['polynomial_abbreviations'][-len(kernel['polynomial_abbreviations']):]==kernel['polynomial_abbreviations'],'literal kernel '+name)
    cert=p['degree_certificate']
    denv={key:0 for key in ports}
    denv.update({key:1 for key in p['variables']})
    for var,e in p['polynomial_abbreviations']:
        denv[var]=bound(e,denv)
    degrees=[bound(e,denv) for e in p['factored_residuals']]
    require(degrees==cert['residual_degrees'],'residual bounds '+name)
    dg=(degrees[0] if p['finalizer']=='direct' else
        2*max(degrees) if p['finalizer']=='sos' else sum(degrees))
    require(dg==p['exact_degree'],'exact claimed upper bound '+name)
    values=[]
    for t in range(dg+1):
        env=dict(ports)
        env.update({var:slope*t%PRIME for var,slope in cert['slopes'].items()})
        for var,e in p['polynomial_abbreviations']:
            env[var]=mod_eval(e,env)
        rows=[mod_eval(e,env) for e in p['factored_residuals']]
        if p['finalizer']=='direct': final=rows[0]
        elif p['finalizer']=='sos': final=sum(r*r for r in rows)%PRIME
        else:
            final=1
            for r in rows: final=final*(1+4*r)%PRIME
            final=(final-1)%PRIME
        values.append(final)
    while len(values)>1:
        values=[(b-a)%PRIME for a,b in zip(values,values[1:])]
    lead=values[0]*pow(math.factorial(dg)%PRIME,-1,PRIME)%PRIME
    require(lead!=0 and lead==cert['leading_coefficient_mod_prime'],'finite-difference leading coefficient '+name)
    return {'variables':p['variable_count'],'exact_degree':dg,
            'leading_coefficient_mod_prime':lead,'finite_difference_verification':'PASS'}


def main():
    kernel_receipts={str(n):audit_kernel(n) for n in (4,5)}
    print(json.dumps({'kernel_audit':kernel_receipts}),flush=True)
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
    ports={}
    for name,item in binding['ports'].items():
        raw=gzip.decompress((ROOT/'coefficients'/item['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest()==item['sha256_raw'],'coefficient '+name)
        ports[name]=int.from_bytes(raw,'little')%PRIME
    receipts={name:audit_degree(name,ports) for name in
              ('parity14_sos','parity14_unit_product','parity13_direct')}
    report={'status':'PASS','kernels':kernel_receipts,'equations':receipts,
            'scope':'Universal finite polynomial norm identities, actual coefficient bytes and exact degrees. Canonical source calibration remains an explicitly inherited mathematical theorem.'}
    (ROOT/'NORM_FAMILY_AUDIT.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=='__main__': main()
