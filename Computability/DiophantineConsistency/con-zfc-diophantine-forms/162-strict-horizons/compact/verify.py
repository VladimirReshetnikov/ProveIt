#!/usr/bin/env python3
"""Exact literal-circuit checks. Polynomial-ring implementation adapted from the retained parent verifier; no producer is imported."""
from __future__ import annotations
import argparse
import ast
from collections import Counter
from copy import deepcopy
from dataclasses import dataclass
import gzip
import hashlib
import json
from pathlib import Path



ROOT = Path(__file__).resolve().parent
INPUTS = ["J","F","alpha","i","T","w","s","n","eta","zeta"]
PORTS = ["beta","K0","MC","MF"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Ring:
    def __init__(self, names):
        self.names = list(names)
        self.index = {x:i for i,x in enumerate(names)}
        self.zero = (0,)*len(names)

    def constant(self, value):
        return Poly(self, {} if value == 0 else {self.zero:value})

    def variable(self, name):
        key=list(self.zero);key[self.index[name]]=1
        return Poly(self,{tuple(key):1})


class Poly:
    def __init__(self, ring, terms):
        self.ring=ring
        self.terms={m:c for m,c in terms.items() if c}

    def coerce(self, other):
        return self.ring.constant(other) if isinstance(other,int) else other

    def __add__(self, other):
        other=self.coerce(other);out=self.terms.copy()
        for mon,c in other.terms.items(): out[mon]=out.get(mon,0)+c
        return Poly(self.ring,out)
    __radd__=__add__

    def __neg__(self):
        return Poly(self.ring,{m:-c for m,c in self.terms.items()})

    def __sub__(self, other): return self + (-self.coerce(other))
    def __rsub__(self, other): return self.coerce(other) + (-self)

    def __mul__(self, other):
        other=self.coerce(other);out={}
        for a,ac in self.terms.items():
            for b,bc in other.terms.items():
                mon=tuple(x+y for x,y in zip(a,b))
                out[mon]=out.get(mon,0)+ac*bc
        return Poly(self.ring,out)
    __rmul__=__mul__

    def __pow__(self, exponent):
        require(isinstance(exponent,int) and exponent>=0,"Bad polynomial exponent")
        out=self.ring.constant(1);base=self
        while exponent:
            if exponent & 1: out=out*base
            exponent//=2
            if exponent: base=base*base
        return out

    def __eq__(self, other):
        return self.terms==self.coerce(other).terms


def expression(text, ring):
    def visit(node):
        if isinstance(node,ast.Name):return ring.variable(node.id)
        if isinstance(node,ast.Constant) and isinstance(node.value,int):return ring.constant(node.value)
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return -visit(node.operand)
        if isinstance(node,ast.BinOp):
            a=visit(node.left)
            if isinstance(node.op,ast.Pow):
                require(isinstance(node.right,ast.Constant),"Only constant powers are allowed")
                return a**node.right.value
            b=visit(node.right)
            if isinstance(node.op,ast.Add):return a+b
            if isinstance(node.op,ast.Sub):return a-b
            if isinstance(node.op,ast.Mult):return a*b
        raise ValueError("Unsupported symbolic expression")
    return visit(ast.parse(text,mode="eval").body)


def cuts_for(mode):
    corrected=mode=='corrected'
    ds='sixq7' if corrected else 'D'
    cuts=[
      ('q',['beta','J'],'beta*J+1'),
      ('qY',['q','s'],'q*s'),
      ('C',['q','F','alpha'],'q-F-alpha'),
      ('X',['q','w'],'q*w' if corrected else 'q**2*w'),
      ('k',['eta','zeta'],'eta+zeta'),
      ('c',['k','s','eta'],'k*s+eta'),
      ('Am1',['X','q','s'],'q*s*(X+1)'),
      ('Hp',['Am1'],'4*Am1-1'),
      ('Delta',['Am1'],'Am1*(Am1+2)'),
      (ds,['q'],'6*q**7' if corrected else 'q**7'),
      ('Dtau',['X','q','s','k'],'1+(X*q**2*s**2)*(X*q**2*s**2+1)*k**2'),
      ('R',['bJ','q','F','alpha','MC','MF','J'],
       '(bJ*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*J'),
      ('Bt',['K0','w','q','C','F'],'(K0+w)*C-F' if corrected else '(K0+q*w)*C-F'),
      ('U',['i','c'],'i*c**2'),
      ('DpI2',['Delta','U','Dtau'],'Delta*U**2*Dtau'),
      ('Df',['DpI2'],'1+DpI2'),
      ('Fsqr',['DpI2'],'1+4*DpI2*(1+DpI2)'),
      ('Q',['Delta','DpI2'],'4*Delta*DpI2*(1+DpI2)'),
      ('cTR',['c','T','alpha','R'],'c*(T+alpha)-R'),
      ('V',['Fsqr','cTR','c'],'Fsqr*cTR-c'),
      ('Kpos',['X','c'],'X*(3*c-2*X)+2'),
      ('Dg',['Dtau','Df'],'Dtau*Df'),
      ('Mtot',['bJ',ds,'Hp'],f'bJ*{ds}*Hp'),
      ('RG',['Mtot','Dg'],'Mtot**2*Dg'),
      ('N',['Q','Znum','Mtot','Dg','V'],
       'Q*(Znum**2-Mtot**2*Dg*V**2)+(Mtot**2*Dg-Znum**2)')]
    if corrected:
        cuts += [
          ('v0',['X','q','s'],'X*q**2*s**2'),
          ('eclear',['k','R','v0','q','s'],
           '6*(k-R-1-s*q**4)-v0*(R+1)*(R-1)*(R+3)'),
          ('Znum',['bJ',ds,'Hp','n','Bt','Kpos','eclear','V','cTR'],
           f'bJ*{ds}*(Hp*(n-cTR*V*Bt)+Kpos)-Hp*({ds}*Bt+bJ*eclear)')]
    else:
        cuts += [
          ('e',['k','R'],'k-R-1'),
          ('eclear',['e','s','q'],'e-s*q**4'),
          ('Znum',['bJ',ds,'Hp','n','Bt','Kpos','eclear','V','cTR'],
           f'bJ*{ds}*(Hp*(n-cTR*V*Bt)+Kpos)-Hp*({ds}*Bt+bJ*eclear)')]
    return cuts


@dataclass
class Leading:
    degree:int
    form:Poly


def verify_graph(data,mode):
    target_ops=83 if mode=='plain' else 89
    target_degree=312 if mode=='plain' else 278
    require(data['witnesses']==INPUTS,'Independent coordinates changed')
    require(data['fixed_numerals']==PORTS,'Fixed ports changed')
    require(data['domain']=='strictly positive integers','Domain changed')
    table={};known=set(INPUTS+PORTS)
    for name,op,a,b in data['source']:
        require(name not in known,'Register collision')
        require(op in ['+','-','*'],'Unsupported gate')
        for x in [a,b]:require(type(x) is int or x in known,'Forward/unknown operand')
        table[name]=(op,a,b);known.add(name)
    live=set()
    def mark(x):
        if type(x) is int or x in live:return
        live.add(x)
        if x in table:
            _,a,b=table[x];mark(a);mark(b)
    mark('N')
    require(live==known,'Dead input, port or gate')
    counts=dict(sorted(Counter(row[1] for row in data['source']).items()))
    require(len(table)==data['operations']==target_ops,'Cost mismatch')
    require(counts==data['operation_breakdown'],'Operation classes mismatch')
    covered=set()
    for name,cuts,formula in cuts_for(mode):
        ring=Ring(cuts);memo={x:ring.variable(x) for x in cuts}
        def expand(x):
            if type(x) is int:return ring.constant(x)
            if x in memo:return memo[x]
            require(x in table,'Unstated independent cut input: '+x)
            covered.add(x)
            op,a,b=table[x];a,b=expand(a),expand(b)
            memo[x]=a+b if op=='+' else a-b if op=='-' else a*b
            return memo[x]
        require(expand(name)==expression(formula,ring),'Exact cut failed: '+name)
    require(covered==set(table),'Not all gates covered by exact cuts')

    ring=Ring(INPUTS+PORTS)
    leading={x:Leading(1 if x in INPUTS else 0,ring.variable(x)) for x in INPUTS+PORTS}
    def get(x):return Leading(0,ring.constant(x)) if type(x) is int else leading[x]
    for name,op,a,b in data['source']:
        a,b=get(a),get(b)
        if op=='*':v=Leading(a.degree+b.degree,a.form*b.form)
        elif a.degree==b.degree:v=Leading(a.degree,a.form+b.form if op=='+' else a.form-b.form)
        elif a.degree>b.degree:v=a
        else:v=Leading(b.degree,b.form if op=='+' else -b.form)
        require(bool(v.form.terms),'Leading cancellation needs refinement at '+name)
        leading[name]=v
    exponent=140 if mode=='plain' else 106
    coefficient=-1024 if mode=='plain' else -36864
    expected=f'{coefficient}*(beta*J)**{exponent}*w**34*s**78*i**14*(eta+zeta)**44*(beta*J-F)**2'
    require(leading['N'].degree==data['exact_degree']==target_degree,'Exact degree mismatch')
    require(leading['N'].form==expression(expected,ring),'Full leading homogeneous polynomial mismatch')
    mon={'beta':exponent,'J':exponent,'w':34,'s':78,'i':14,'eta':44,'F':2}
    key=tuple(mon.get(x,0) for x in ring.names)
    require(leading['N'].form.terms.get(key)==coefficient,'Nonzero exact leading coefficient missing')
    return {'operations':target_ops,'operation_breakdown':counts,'exact_degree':target_degree,
        'independent_variables':10,'exact_cut_identities':len(cuts_for(mode)),
        'covered_gates':len(covered),'whole_leading_form':expected,
        'leading_monomials':len(leading['N'].form.terms),
        'register_degrees':{x:leading[x].degree for x in ['X','qY','c','Am1','Delta','Dtau','U','DpI2','Fsqr','Q','Dg','cTR','V','Mtot','Bt','Znum','N']}}


def check_mutations(data,mode):
    ds='D' if mode=='plain' else 'sixq7'
    cases=[('kY',3,'qY'),('Am1',3,'s'),('Tshift',1,'-'),
        ('Q',1,'+'),('cTR',1,'+'),('Kpos',3,3),('eclear',1,'+'),
        ('Znum',1,'+'),('N',1,'-'),(ds,3,'q4')]
    rejected=[]
    for name,index,value in cases:
        bad=deepcopy(data)
        row=next(r for r in bad['source'] if r[0]==name);row[index]=value
        bad['operation_breakdown']=dict(sorted(Counter(r[1] for r in bad['source']).items()))
        try:verify_graph(bad,mode)
        except (ValueError,KeyError):rejected.append(name)
        else:raise ValueError('Accepted actual corruption '+name)
    return rejected


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt');args=ap.parse_args()
    out={'equations':{},'status':'PASS'}
    for mode,filename in [('plain','equation_83_degree312.json'),('corrected','equation_89_degree278.json')]:
        data=json.loads((ROOT/filename).read_text())
        parent=data['parent']
        require(hashlib.sha256((ROOT/parent['path']).read_bytes()).hexdigest()==parent['sha256'],'Parent identity mismatch')
        binding=data['coefficient_binding']
        for name,meta in binding['ports'].items():
            path=ROOT/binding['path']/meta['file'];raw=path.read_bytes()
            require(hashlib.sha256(raw).hexdigest()==meta['gzip_sha256'],'Compressed numeral changed: '+name)
            decoded=gzip.decompress(raw)
            require(hashlib.sha256(decoded).hexdigest()==meta['raw_sha256'],'Numeral changed: '+name)
            require(int.from_bytes(decoded,'little').bit_length()==meta['bits'],'Numeral bit length changed')
        rec=verify_graph(data,mode);rec['rejected_corruptions']=check_mutations(data,mode)
        rec['sha256']=hashlib.sha256((ROOT/filename).read_bytes()).hexdigest()
        out['equations'][filename]=rec
    out['scope']='Exact finite circuits, full polynomial cuts, leading forms, counts, coefficient hashes and actual corruptions. Unbounded equivalence is an ordinary proof in PROOF.md.'
    text=json.dumps(out,indent=2)+'\n'
    if args.receipt:Path(args.receipt).write_text(text)
    print(text,end='')


if __name__=='__main__':main()


