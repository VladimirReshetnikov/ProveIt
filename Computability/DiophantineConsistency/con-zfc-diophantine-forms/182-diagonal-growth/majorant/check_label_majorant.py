#!/usr/bin/env python3
"""Check a uniform majorant for the actual square-shell C222 label list.

Default checking uses exact outward-rounded dyadic arithmetic.  It constructs
the real arithmetic DAG, computes its degrees, and determines exact bit lengths
of the relevant huge integers without expanding the polynomial.  --exact also
evaluates those huge integers as an independent cross-check.  --write writes
the small certificate; otherwise an existing certificate is checked.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import sys
import types
from pathlib import Path

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'shell_source.py'
SOURCE_SHA='59c68a354fe5cdbc04bde33720080db2436cb51ae25e3485ac5ae45ff4230199'
EXPECTED_DEGREES=[16,8,8,8,8,32,16,8,524288,1,1,2,2,0]
PRECISION=64

def require(ok,message):
    if not ok:raise ValueError(message)

class Builder:
    def __init__(self):self.nodes=[];self.cache={}
    def node(self,op,*args):
        require(op in ('+','*'),'Unsupported arithmetic operation')
        key=(op,)+args
        if key not in self.cache:
            self.cache[key]=len(self.nodes);self.nodes.append(key)
        return ('n',self.cache[key])
    def add(self,a,b):return self.node('+',a,b)
    def mul(self,a,b):return self.node('*',a,b)
    def square(self,a):return self.mul(a,a)
    def sum(self,items):
        value=('c',0)
        for item in items:value=self.add(value,item)
        return value

def get_source_dag():
    raw=SOURCE.read_bytes()
    require(len(raw)==2955,'Unexpected source byte length')
    require(hashlib.sha256(raw).hexdigest()==SOURCE_SHA,'Unexpected source SHA-256')
    stub=types.ModuleType('build_equation')
    for name,value in [('ZERO',0),('ONE',1),('TWO',2),('FOUR',4)]:
        setattr(stub,name,('c',value))
    sys.modules['build_equation']=stub
    namespace={}
    # This executes only the exact authenticated finite source above.  Its
    # codes_only path accepts our symbolic builder, never a numeric oracle.
    exec(compile(raw,str(SOURCE),'exec'),namespace)
    require(namespace['SHELL_SCHEME']=='xx0','Unexpected shell orientation')
    builder=Builder();env={name:('v',name) for name in ('a','b','c','d','p','q','v')}
    result=namespace['direct_source'](builder,None,env,None,False,codes_only=True)
    labels=result['codes']+[env['a'],env['b'],result['I'](env['a'],env['b']),
                             result['A'](env['a'],env['b']),('c',1)]
    require(len(labels)==14,'Unexpected number of label-bound summands')
    total=builder.sum(labels)
    for index,(op,a,b) in enumerate(builder.nodes):
        for tag,value in (a,b):
            require(tag in ('n','c','v'),'Unexpected leaf kind')
            if tag=='n':require(0<=value<index,'Non-topological DAG')
            if tag=='c':require(isinstance(value,int) and value>=0,'Negative coefficient leaf')
            if tag=='v':require(value in ('a','b','c','d'),'Unexpected source variable')
    return builder.nodes,labels,total

def evaluate(nodes,roots,leaf,add,mul):
    values=[]
    def get(value):
        tag,item=value
        return values[item] if tag=='n' else leaf(tag,item)
    for op,a,b in nodes:
        values.append((add if op=='+' else mul)(get(a),get(b)))
    return [get(root) for root in roots],values

def ceil_shift(m,s):
    require(m>=0 and s>=0,'Invalid dyadic alignment')
    return 0 if m==0 else 1+((m-1)>>s)

def normalize(m,e,upper):
    require(m>=0 and e>=0,'Invalid dyadic bound')
    shift=max(0,m.bit_length()-PRECISION)
    if shift:
        m=ceil_shift(m,shift) if upper else m>>shift;e+=shift
    return m,e

def dyadic_add(a,b,upper):
    ma,ea=a;mb,eb=b;e=max(ea,eb)
    if upper:m=ceil_shift(ma,e-ea)+ceil_shift(mb,e-eb)
    else:m=(ma>>(e-ea))+(mb>>(e-eb))
    return normalize(m,e,upper)

def dyadic_mul(a,b,upper):
    return normalize(a[0]*b[0],a[1]+b[1],upper)

def dyadic_power(c,n,upper):
    out=(1,0);base=(c,0)
    while n:
        if n&1:out=dyadic_mul(out,base,upper)
        n//=2
        if n:base=dyadic_mul(base,base,upper)
    return out

def bit_interval(a):
    m,e=a;require(m>0,'A positive bound is required')
    return e+m.bit_length()-1,e+m.bit_length()

def build_certificate(nodes,labels,total):
    # -1 denotes the zero polynomial; all nonzero coefficients are positive.
    def degree_leaf(tag,value):return (0 if value else -1) if tag=='c' else 1
    def degree_mul(a,b):return -1 if min(a,b)<0 else a+b
    degrees,_=evaluate(nodes,labels+[total],degree_leaf,max,degree_mul)
    require(degrees[:-1]==EXPECTED_DEGREES,'Unexpected label degrees')
    require(degrees[-1]==524288,'Unexpected J degree')
    records=[]
    for c in (462,463,464):
        bounds=[]
        for upper in (False,True):
            vals,_=evaluate(nodes,[total],
                lambda tag,value:((value,0) if tag=='c' else (c,0)),
                lambda a,b:dyadic_add(a,b,upper),lambda a,b:dyadic_mul(a,b,upper))
            bounds.append((vals[0],dyadic_power(c,3*c*c,upper)))
        (jl,tl),(ju,tu)=bounds
        jl_bits,ju_bits,tl_bits,tu_bits=map(bit_interval,(jl,ju,tl,tu))
        require(jl_bits==ju_bits,'J bit length was not determined exactly')
        require(tl_bits==tu_bits,'Power bit length was not determined exactly')
        succeeds=ju_bits[1]<=tl_bits[0]
        fails=tu_bits[1]<=jl_bits[0]
        require(succeeds!=fails,'Comparison is inconclusive')
        records.append({'c':c,'exponent':3*c*c,'J_lower':jl,'J_upper':ju,
                        'power_lower':tl,'power_upper':tu,
                        'J_bit_length':ju_bits[1],'power_bit_length':tl_bits[1],
                        'J_strictly_below_power':succeeds})
    require([r['J_strictly_below_power'] for r in records]==[False,True,True],
            'Unexpected success/failure boundary')
    require(3*464*464>=degrees[-1],'Exponent is below the polynomial degree')
    return {'source_path':'shell_source.py','source_bytes':2955,'source_sha256':SOURCE_SHA,
            'precision_bits':PRECISION,'arithmetic_node_count':len(nodes),
            'summand_degrees':degrees[:-1],'J_degree':degrees[-1],
            'selected_c':464,'selected_exponent':645888,'cases':records}

def exact_cross_check(nodes,total,certificate):
    records={r['c']:r for r in certificate['cases']}
    for c in (462,464):
        values,_=evaluate(nodes,[total],lambda tag,value:value if tag=='c' else c,
                          lambda a,b:a+b,lambda a,b:a*b)
        j=values[0];power=c**(3*c*c);record=records[c]
        require(j.bit_length()==record['J_bit_length'],'Exact J bit-length mismatch')
        require(power.bit_length()==record['power_bit_length'],'Exact power bit-length mismatch')
        require((j<power)==record['J_strictly_below_power'],'Exact comparison mismatch')
        print('exact integer cross-check passed for c='+str(c),flush=True)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    parser.add_argument('--exact',action='store_true');args=parser.parse_args()
    nodes,labels,total=get_source_dag()
    certificate=build_certificate(nodes,labels,total)
    # Round-trip tuples into the JSON representation before comparison.
    certificate=json.loads(json.dumps(certificate))
    path=ROOT/'LABEL_GROWTH_CERTIFICATE.json'
    if args.write:path.write_text(json.dumps(certificate,indent=2)+'\n')
    else:require(json.loads(path.read_text())==certificate,'Certificate mismatch')
    if args.exact:exact_cross_check(nodes,total,certificate)
    print(json.dumps(certificate,indent=2))
    print('PASS: every source assignment 0 <= a,b,c,d < t, t >= 464, has J < t^645888.')

if __name__=='__main__':main()
