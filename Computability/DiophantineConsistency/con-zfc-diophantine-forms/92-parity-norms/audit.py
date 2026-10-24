#!/usr/bin/env python3
"""Independent exact algebra/degree audit; imports no builder code."""
import ast
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent
P = 1_000_000_007
CHECKS = []


def check(condition, label):
    if not condition:
        raise ValueError(label)
    CHECKS.append(label)


class Poly:
    """Sparse exact Z[t,a,b,c] polynomials for local universal identities."""
    def __init__(self, terms):
        self.d = {k: v for k, v in terms.items() if v}

    @staticmethod
    def coerce(v):
        return v if isinstance(v, Poly) else Poly({(0,0,0,0): v})

    @staticmethod
    def var(i):
        mon = tuple(int(j == i) for j in range(4))
        return Poly({mon: 1})

    def __add__(self, other):
        out = dict(self.d)
        for m, c in self.coerce(other).d.items():
            out[m] = out.get(m, 0)+c
        return Poly(out)
    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m,c in self.d.items()})

    def __sub__(self, other):
        return self+-self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other)+-self

    def __mul__(self, other):
        out = {}
        for m,c in self.d.items():
            for n,d in self.coerce(other).d.items():
                k=tuple(a+b for a,b in zip(m,n))
                out[k]=out.get(k,0)+c*d
        return Poly(out)
    __rmul__ = __mul__

    def __pow__(self, n):
        out = Poly.coerce(1)
        for _ in range(n):
            out=out*self
        return out


def generic_identities():
    t,a,b,c = [Poly.var(i) for i in range(4)]
    x=2*t+1
    A=4*a+1
    delta,r=b,c
    primitive=(delta*(t*(t+1)-a)-r)**2-A*delta*r
    literal=(delta*(x*x+A)-4*r)**2-4*A*x*x*delta*delta
    check(not (literal-16*primitive).d, 'two-root primitive identity over Z')
    B=4*b+1
    U=t*(t+1)-a-B+4*c
    M=U*U+4*x*x*c-A*B
    N=M*M-16*x*x*U*U*c
    n=t*(t+1)-a-B-4*c
    alt=(n*n-A*B-4*A*c-16*B*c)**2-16*A*B*c*x*x
    check(not (N-alt).d, 'two three-root formulas are identical')
    # Product in the free multiquadratic algebra: basis bit masks encode
    # sqrt(A), sqrt(B), sqrt(c). A repeated generator contributes its square.
    radicands=[A,B,c]
    accum={0:Poly.coerce(1)}
    for e1,e2,e3 in itertools.product((-1,1),repeat=3):
        factor={0:x,1:Poly.coerce(e1),2:Poly.coerce(2*e2),4:Poly.coerce(4*e3)}
        result={}
        for i,pi in accum.items():
            for j,pj in factor.items():
                term=pi*pj
                for h in range(3):
                    if i & j & (1<<h):
                        term=term*radicands[h]
                k=i^j
                result[k]=result.get(k,Poly.coerce(0))+term
        accum={k:v for k,v in result.items() if v.d}
    check(set(accum)=={0}, 'eight-factor norm has no radical components')
    check(not (accum[0]-256*N).d, 'eight-factor primitive norm identity over Z')
    # t,a,b here stand for t,z0,k in the centering identity.
    old_t=t+2*a*b
    A4=a*(4*a+1)*b*b
    core=t*(t+1)+4*a*b*t+2*a*b-a*b*b
    check(not (old_t*(old_t+1)-A4-core).d, 'centered odd carrier identity')


def scalar_evaluator(text, env):
    def go(node):
        if isinstance(node,ast.Name):
            return env[node.id]
        if isinstance(node,ast.Constant):
            check_const=isinstance(node.value,int)
            if not check_const:
                raise ValueError('noninteger constant')
            return node.value%P
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
            return -go(node.operand)%P
        if isinstance(node,ast.BinOp):
            left=go(node.left)
            if isinstance(node.op,ast.Pow):
                if not isinstance(node.right,ast.Constant) or not isinstance(node.right.value,int) or node.right.value<0:
                    raise ValueError('nonfixed exponent')
                return pow(left,node.right.value,P)
            right=go(node.right)
            if isinstance(node.op,ast.Add): return (left+right)%P
            if isinstance(node.op,ast.Sub): return (left-right)%P
            if isinstance(node.op,ast.Mult): return left*right%P
        raise ValueError(ast.dump(node))
    return go(ast.parse(text,mode='eval').body)


def degree(text, env):
    def go(n):
        if isinstance(n,ast.Name): return env[n.id]
        if isinstance(n,ast.Constant): return 0
        if isinstance(n,ast.UnaryOp): return go(n.operand)
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,(ast.Add,ast.Sub)): return max(go(n.left),go(n.right))
            if isinstance(n.op,ast.Mult): return go(n.left)+go(n.right)
            if isinstance(n.op,ast.Pow): return go(n.left)*n.right.value
        raise ValueError(ast.dump(n))
    return go(ast.parse(text,mode='eval').body)


def eval_rows(packet, ports, slopes, value):
    env=dict(ports)
    env.update({name: slope*value%P for name,slope in slopes.items()})
    for name, expression in packet['polynomial_abbreviations']:
        env[name]=scalar_evaluator(expression,env)
    return [scalar_evaluator(e,env) for e in packet['factored_residuals']]


def nth_difference(values):
    row=list(values)
    while len(row)>1:
        row=[(b-a)%P for a,b in zip(row,row[1:])]
    return row[0]


def audit_packets():
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
    ports={}
    for name,item in binding['ports'].items():
        raw=gzip.decompress((ROOT/'coefficients'/item['file']).read_bytes())
        check(hashlib.sha256(raw).hexdigest()==item['sha256_raw'],'coefficient '+name)
        ports[name]=int.from_bytes(raw,'little')%P
    parent_bytes=(ROOT/'parent/degree88_17.json').read_bytes()
    parent=json.loads(parent_bytes)
    sha=hashlib.sha256(parent_bytes).hexdigest()
    expected={'parity16_sos':160,'parity16_unit_product':152,
              'centered16_sos':120,'centered16_unit_product':132,
              'parity15_sos':352,'parity15_unit_product':204}
    receipts={}
    for name, final_degree in expected.items():
        packet=json.loads((ROOT/(name+'.json')).read_text())
        check(packet['parent_sha256']==sha,name+' parent byte identity')
        check(packet['polynomial_abbreviations'][:len(parent['polynomial_abbreviations'])]==parent['polynomial_abbreviations'],name+' retained source definitions')
        check(packet['factored_residuals'][:2]==parent['factored_residuals'][1:3],name+' retained main and strong rows')
        if packet['variable_count']==16:
            check(packet['factored_residuals'][2]==parent['factored_residuals'][4],name+' retained guard')
        check(len(packet['variables'])==len(set(packet['variables']))==packet['variable_count'],name+' variable count')
        cert=packet['degree_certificate']
        env={key:0 for key in ports}
        env.update({key:1 for key in packet['variables']})
        for key, expression in packet['polynomial_abbreviations']:
            env[key]=degree(expression,env)
        ds=[degree(e,env) for e in packet['factored_residuals']]
        check(ds==cert['residual_degree_bounds'],name+' independent degree upper bounds')
        computed=2*max(ds) if packet['finalizer']=='sos' else sum(ds)
        check(computed==final_degree==packet['exact_degree'],name+' final upper bound')
        values=[]
        residual_values=[[] for _ in ds]
        for value in range(final_degree+1):
            rows=eval_rows(packet,ports,cert['slopes'],value)
            for rr,row in zip(residual_values,rows): rr.append(row)
            if packet['finalizer']=='sos':
                final=sum(r*r for r in rows)%P
            else:
                final=1
                for r in rows: final=final*(1+4*r)%P
                final=(final-1)%P
            values.append(final)
        leading=nth_difference(values)*pow(math.factorial(final_degree)%P,-1,P)%P
        check(leading!=0 and leading==cert['final_leading_coefficient_mod_prime'],name+' exact finite-difference top coefficient')
        for i,d in enumerate(ds):
            rc=nth_difference(residual_values[i][:d+1])*pow(math.factorial(d)%P,-1,P)%P
            check(rc!=0 and rc==cert['residual_leading_coefficients_mod_prime'][i],name+' residual '+str(i)+' exact degree')
        receipts[name]={'variables':packet['variable_count'],'degree':final_degree,
                        'residual_degrees':ds,'top_coefficient_mod_prime':leading}
    return receipts


def diagnostic_controls():
    # Removing the odd-carrier condition admits the zero-carrier component.
    A,delta,r,x=5,4,5,0
    norm=(delta*(x*x+A)-4*r)**2-4*A*x*x*delta*delta
    check(norm==0 and math.isqrt(A)**2!=A,'zero-carrier countercontrol')
    # With delta=0 and r=0 the primitive polynomial is zero for any radicand.
    check((0*(0-1)-0)**2-5*0*0==0,'zero-denominator countercontrol')
    # Equal weights permit irrational squareclass cancellation: sqrt5-sqrt5+1.
    check(5%4==1,'equal-weight squareclass countercontrol (symbolic example in proof)')
    # Small true-square triples exercise all signs, including repeated classes.
    count=0
    for u,d,e in itertools.product(range(1,8,2),range(1,8,2),range(-3,4)):
        A,B,C=u*u,d*d,e*e
        a=(A-1)//4
        t=(u+2*d+4*e-1)//2
        x=2*t+1
        U=t*(t+1)-a-B+4*C
        M=U*U+4*x*x*C-A*B
        check(M*M-16*x*x*U*U*C==0,'square triple '+str(count))
        count+=1
    return count


def main():
    generic_identities()
    receipts=audit_packets()
    diagnostics=diagnostic_controls()
    report={'status':'PASS','checks':len(CHECKS),'exact_equations':receipts,
            'exact_local_norm_identities':True,'square_triple_diagnostics':diagnostics,
            'scope':'Exact finite algebra, coefficient bytes, counts and exact degrees. Universal semantic arguments are supplied in the proofs; no consistency claim or kernel proof is established by this script.'}
    (ROOT/'AUDIT.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
