#!/usr/bin/env python3
"""Independently check the serialized fusion proofs, without their generator."""
import argparse,hashlib,json
from pathlib import Path
F=['const',1]
A=['var','A'];B=['var','B']
def imp(a,b):return ['I',a,b]
def uni(d,a):return ['U',d,a]
def neg(a):return imp(a,F)
def require(test,description):
    if not test:raise ValueError(description)
def form(f):
    require(isinstance(f,list)and len(f)>=2,'malformed formula')
    if f[0]=='const':require(len(f)==2 and f[1]in(0,1),'bad constant')
    elif f[0]=='var':require(len(f)==2 and f[1]in('A','B'),'bad variable')
    else:
        require(f[0]in('I','U')and len(f)==3,'bad constructor')
        form(f[1]);form(f[2])
def axiom(tag,args):
    if tag=='K':
        require(len(args)==2,'K arity');a,b=args;return imp(a,imp(b,a))
    if tag=='S':
        require(len(args)==3,'S arity');a,b,c=args
        return imp(imp(a,imp(b,c)),imp(imp(a,b),imp(a,c)))
    if tag=='Peirce':
        require(len(args)==2,'Peirce arity');a,b=args;return imp(imp(imp(a,b),a),a)
    if tag=='h1':
        require(len(args)==2,'h1 arity');d,h=args;return imp(neg(uni(d,neg(uni(d,h)))),h)
    raise ValueError('unauthorized rule '+str(tag))
def audit(path):
    data=json.loads(path.read_text())
    fused=neg(imp(A,B))
    goals={'join':imp(A,imp(neg(B),fused)),
           'left_projection':imp(fused,A),'right_projection':imp(fused,neg(B))}
    require(set(data)==set(goals),'wrong certificate families')
    result={}
    for name,goal in goals.items():
        item=data[name];rows=item['proof'];counts={}
        for i,row in enumerate(rows):
            require(isinstance(row,list)and len(row)==3,'bad proof row')
            formula,rule,args=row;form(formula)
            if rule=='MP':
                require(len(args)==2 and all(type(x)is int and 0<=x<i for x in args),'bad references')
                minor,major=args
                require(rows[major][0]==imp(rows[minor][0],formula),'MP formula mismatch')
            else:require(formula==axiom(rule,args),'axiom instance mismatch')
            counts[rule]=counts.get(rule,0)+1
        require(rows[-1][0]==goal and item['goal']==goal,'wrong target formula')
        require(item['lines']==len(rows),'wrong stated line count')
        result[name]={'lines':len(rows),'rules':counts,'goal':goal}
    return {'status':'PASS','serialized_certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'certificates':result,
        'scope':'Universal formal formula certificates in the K/S/Peirce/h1 object calculus. The inherited restricted-rho8 basis supplies K, S and Peirce; no h4/h5 axiom is used by these certificate templates.'}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('certificate',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    r=audit(a.certificate);txt=json.dumps(r,indent=2)+'\n'
    if a.output:a.output.write_text(txt)
    print(json.dumps({k:v for k,v in r.items()if k!='certificates'},indent=2))
