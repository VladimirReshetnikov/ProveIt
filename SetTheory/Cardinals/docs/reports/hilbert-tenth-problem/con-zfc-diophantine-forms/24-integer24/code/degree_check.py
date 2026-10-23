#!/usr/bin/env python3
"""Full univariate finite-field degree diagnostics for arithmetic DAGs.

The convolution is exact: coefficients are nonnegative residues; 128-bit
packing words prevent carries because each convolution coefficient is less
than min(len(a),len(b))*(p-1)^2 < 2^128. No floating point is used.
These diagnostics do not replace the uniform symbolic degree proof.
"""
import json,random,sys
from pathlib import Path
WORD=16

def trim(a):
    while len(a)>1 and not a[-1]:a.pop()
    return a

def mul(a,b,p):
    if not any(a)or not any(b):return [0]
    if min(len(a),len(b))*(p-1)**2 >= (1<<(8*WORD)):raise ValueError('packing overflow')
    aa=int.from_bytes(b''.join(x.to_bytes(WORD,'little')for x in a),'little')
    bb=int.from_bytes(b''.join(x.to_bytes(WORD,'little')for x in b),'little')
    n=len(a)+len(b)-1;raw=(aa*bb).to_bytes(WORD*n,'little')
    return trim([int.from_bytes(raw[i:i+WORD],'little')%p for i in range(0,len(raw),WORD)])

def add(a,b,p,sign=1):
    n=max(len(a),len(b));out=[0]*n
    for i,x in enumerate(a):out[i]=x
    for i,x in enumerate(b):out[i]=(out[i]+sign*x)%p
    return trim(out)

def diagnostic(packet,prime=1000000007,seed=215,beta_exponent=None,coefficient_values=None):
    rng=random.Random(seed)
    # Homogeneous slices reveal the leading degree without choosing a root.
    v={n:[0,rng.randrange(1,prime)] for n in packet['witnesses']}
    coeff=[31,127,10,45]
    if coefficient_values is not None:
        if beta_exponent is not None:raise ValueError('Specify a complete tuple or beta_exponent, not both')
        if set(coefficient_values)!=set(packet['fixed_numerals']):raise ValueError('Incomplete coefficient tuple')
        coeff=[coefficient_values[n]%prime for n in packet['fixed_numerals']]
    elif beta_exponent is not None:coeff[0]=(pow(2,beta_exponent,prime)-1)%prime
    v.update({n:[x]for n,x in zip(packet['fixed_numerals'],coeff)})
    for n,op,a,b in packet['source']:
        a=[a%prime]if isinstance(a,int)else v[a];b=[b%prime]if isinstance(b,int)else v[b]
        v[n]=mul(a,b,prime)if op=='*'else add(a,b,prime,1 if op=='+'else -1)
    if 'output'in packet:
        r=v[packet['output']];result={'degree':len(r)-1,'leading_coefficient':r[-1]}
        if 'exact_degree'in packet and len(r)-1!=packet['exact_degree']:raise ValueError((packet['name'],result,packet['exact_degree']))
    else:
        residuals=[]
        for a,b in packet['comparisons']:
            a=[a%prime]if isinstance(a,int)else v[a];b=[b%prime]if isinstance(b,int)else v[b]
            r=add(a,b,prime,-1);residuals.append({'degree':len(r)-1,'leading_coefficient':r[-1]})
        result={'residuals':residuals}
        if 'residual_exact_degrees'in packet and [r['degree']for r in residuals]!=packet['residual_exact_degrees']:
            raise ValueError((packet['name'],result,packet['residual_exact_degrees']))
    return {'name':packet['name'],'prime':prime,'seed':seed,
            'coefficient_source':'supplied complete tuple' if coefficient_values is not None else 'small diagnostic fixture',
            'coefficient_fixture':dict(zip(packet['fixed_numerals'],coeff)),**result}

def main():
    if not sys.argv[1:]:raise SystemExit('Usage: degree_check.py CIRCUIT.json ...')
    records=[]
    for name in sys.argv[1:]:
        packet=json.loads(Path(name).read_text())
        for p,seed in [(1000000007,215),(1000000009,216)]:records.append(diagnostic(packet,p,seed))
    print(json.dumps({'scope':'Exact full finite-field univariate diagnostic; does not replace uniform degree proof.','records':records},indent=2))
if __name__=='__main__':main()
