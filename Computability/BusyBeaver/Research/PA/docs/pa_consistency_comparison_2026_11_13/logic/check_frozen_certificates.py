#!/usr/bin/env python3
"""Check the serialized proofs without importing the proof generator."""
from pathlib import Path
import json

def imp(a,b): return (a,b)
def freeze(x): return tuple(map(freeze,x)) if isinstance(x,list) else x
def require(p,msg):
    if not p: raise ValueError(msg)

f,H,X,A,Y='f','H','X','A','Y'
old=imp(imp(X,f),H);new=imp(imp(H,f),X)
old_a=imp(imp(Y,f),A)
expected={
    'new_to_old':({new,imp(f,H)},old),
    'old_to_new':({old,imp(f,X)},new),
    'old_to_explosion':({old_a},imp(f,A)),
}
data=json.loads(Path(__file__).with_name('split_head_certificates.json').read_text())
require(set(data)==set(expected),'Certificate inventory differs')
for name,(hypotheses,goal) in expected.items():
    cert=data[name];forms=[]
    for i,node in enumerate(cert['nodes']):
        formula=freeze(node['formula']);rule=node['rule'];args=freeze(node['args'])
        if rule=='hyp':
            require(not args and formula in hypotheses,f'{name}:{i}: bad assumption')
        elif rule=='K':
            require(len(args)==2,f'{name}:{i}: K arity')
            a,b=args;require(formula==imp(a,imp(b,a)),f'{name}:{i}: bad K')
        elif rule=='S':
            require(len(args)==3,f'{name}:{i}: S arity')
            a,b,c=args
            require(formula==imp(imp(a,imp(b,c)),imp(imp(a,b),imp(a,c))),f'{name}:{i}: bad S')
        elif rule=='Peirce':
            require(len(args)==2,f'{name}:{i}: Peirce arity')
            a,b=args;require(formula==imp(imp(imp(a,b),a),a),f'{name}:{i}: bad Peirce')
        elif rule=='MP':
            require(len(args)==2 and all(type(j)is int and 0<=j<i for j in args),f'{name}:{i}: bad premise index')
            minor,major=map(forms.__getitem__,args)
            require(major==imp(minor,formula),f'{name}:{i}: bad MP')
        else: raise ValueError(f'{name}:{i}: unknown rule')
        forms.append(formula)
    root=cert['root']
    require(type(root)is int and 0<=root<len(forms),f'{name}: bad root')
    require(forms[root]==goal,f'{name}: wrong endpoint')
print('PASS: all 171 serialized Hilbert DAG nodes and the three stated endpoints.')
