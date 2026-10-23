#!/usr/bin/env python3
"""Exact sparse polynomial elimination over Z; no external dependencies.

Every elimination is solved using an integer coefficient +1 or -1.  Source
variables are unrestricted, so a triangular polynomial substitution induces
a bijection of integer zero sets.  Search success is a construction; search
failure is not a lower bound.
"""
import ast, json, hashlib, sys
from pathlib import Path
from collections import defaultdict

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'upstream/quartic45.json'
packet=json.loads(SOURCE.read_text())
VARS=packet['variables']
PORTS=packet['fixed_numerals']
NAMES=VARS+PORTS
IDX={v:i for i,v in enumerate(NAMES)}
ZERO=(0,)*len(NAMES)

def clean(a):return {m:c for m,c in a.items() if c}
def const(c):return {ZERO:c} if c else {}
def var(v):
    m=list(ZERO);m[IDX[v]]=1;return {tuple(m):1}
def add(a,b):
    c=dict(a)
    for m,z in b.items():c[m]=c.get(m,0)+z
    return clean(c)
def scale(a,k):return clean({m:z*k for m,z in a.items()})
def sub(a,b):return add(a,scale(b,-1))
def mul(a,b):
    c=defaultdict(int)
    for m,x in a.items():
      for n,y in b.items():
        c[tuple(u+v for u,v in zip(m,n))]+=x*y
    return clean(c)
def power(a,n):
    if n<0:raise ValueError('negative exponent')
    out=const(1)
    while n:
      if n&1:out=mul(out,a)
      n//=2
      if n:a=mul(a,a)
    return out
def parse(text):
    def rec(n):
      if isinstance(n,ast.Constant) and isinstance(n.value,int):return const(n.value)
      if isinstance(n,ast.Name):return var(n.id)
      if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return scale(rec(n.operand),-1)
      if isinstance(n,ast.BinOp):
        if isinstance(n.op,ast.Add):return add(rec(n.left),rec(n.right))
        if isinstance(n.op,ast.Sub):return sub(rec(n.left),rec(n.right))
        if isinstance(n.op,ast.Mult):return mul(rec(n.left),rec(n.right))
        if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant):return power(rec(n.left),n.right.value)
      raise ValueError(ast.dump(n))
    return rec(ast.parse(text,mode='eval').body)
def degree(a):return max((sum(m[:len(VARS)]) for m in a),default=0)
def substitute(a,name,b):
    j=IDX[name];powers={0:const(1),1:b};out={}
    for mon,c in a.items():
      p=mon[j]
      if not p:
        out[mon]=out.get(mon,0)+c
        continue
      if p not in powers:powers[p]=power(b,p)
      rest=list(mon);rest[j]=0
      out=add(out,mul({tuple(rest):c},powers[p]))
    return clean(out)
def solve(a,name):
    j=IDX[name];lead=ZERO[:j]+(1,)+ZERO[j+1:]
    c=a.get(lead,0)
    if c not in (-1,1):return None
    if any(m[j] and m!=lead for m in a):return None
    return scale({m:z for m,z in a.items() if m!=lead},-c)
def fmt(a):
    terms=[]
    for mon,c in sorted(a.items(),key=lambda t:(-sum(t[0]),t[0])):
      p='*'.join(v if e==1 else f'{v}**{e}' for v,e in zip(NAMES,mon) if e)
      term=str(abs(c))+(('*'+p) if p else '') if abs(c)!=1 or not p else p
      terms.append(('+' if c>0 else '-')+term)
    out=''.join(terms)
    return out[1:] if out.startswith('+') else out or '0'
def equations(shear=False):
    es=[parse(x) for x in packet['residuals']]
    if shear:es=[substitute(e,'tau',add(var('tau'),var('P'))) for e in es]
    return es
def eliminate(es,name,index):
    rhs=solve(es[index],name)
    if rhs is None:raise ValueError('Not a unit linear equation')
    out=[substitute(e,name,rhs) for i,e in enumerate(es) if i!=index]
    return out,rhs
def apply_sequence(names,shear=False):
    es=equations(shear);history=[]
    for name in names:
      candidates=[(i,solve(e,name)) for i,e in enumerate(es)]
      candidates=[(i,r) for i,r in candidates if r is not None]
      if not candidates:raise ValueError('No definition for '+name)
      i,rhs=min(candidates,key=lambda t:(degree(t[1]),len(t[1])))
      es,rhs=eliminate(es,name,i)
      history.append({'variable':name,'equation_index':i,'definition':fmt(rhs),'max_residual_degree':max(map(degree,es))})
    return es,history
def key(es,names):
    return tuple(sorted(names))
def search(budget=3,beam=300,shear=False):
    current=[(equations(shear),[],[])]
    alllevels=[]
    while current:
      candidates={}
      for es,names,hist in current:
        live=[v for v in VARS if v not in names]
        for v in live:
          for i,e in enumerate(es):
            rhs=solve(e,v)
            if rhs is None:continue
            out,_=eliminate(es,v,i)
            ds=list(map(degree,out))
            if max(ds)>budget:continue
            newnames=names+[v]
            h=hist+[{'variable':v,'equation_index':i,'definition':fmt(rhs)}]
            score=(sum(len(e) for e in out),sum(ds),tuple(newnames))
            k=key(out,newnames)
            if k not in candidates or score<candidates[k][0]:candidates[k]=(score,out,newnames,h)
      if not candidates:break
      vals=sorted(candidates.values())[:beam]
      current=[(e,n,h) for _,e,n,h in vals]
      best=current[0]
      alllevels.append({'eliminated':len(best[1]),'states':len(candidates),'retained':len(current),'best':best[1]})
      print(json.dumps(alllevels[-1]),flush=True)
    es,names,hist=current[0]
    return {'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            'source_variables':len(VARS),'variables':[v for v in VARS if v not in names],
            'variable_count':len(VARS)-len(names),'residual_count':len(es),
            'max_residual_degree':max(map(degree,es)),
            'single_equation_degree':2*max(map(degree,es)),
            'tau_shear':shear,'history':hist,'residuals':[fmt(e) for e in es],
            'residual_degrees':list(map(degree,es)),'search_levels':alllevels}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--budget',type=int,default=3)
    p.add_argument('--beam',type=int,default=200);p.add_argument('--shear',action='store_true')
    p.add_argument('--sequence',nargs='*');a=p.parse_args()
    if a.sequence:
      es,h=apply_sequence(a.sequence,a.shear)
      out={'variable_count':len(VARS)-len(h),'history':h,'residuals':[fmt(e) for e in es],'degrees':list(map(degree,es))}
    else:out=search(a.budget,a.beam,a.shear)
    file=ROOT/f'elimination_{a.budget}_{"shear" if a.shear else "direct"}.json'
    file.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
