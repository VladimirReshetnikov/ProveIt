#!/usr/bin/env python3
"""Independent exact source-restoration and fixed-numeral audit.

This checker imports no builder. It uses SymPy for exact polynomial identities
and a separate AST interpreter for finite actual-coefficient diagnostics.
The finite diagnostics are not the proof of consistency equivalence.
"""
import ast
import gzip
import hashlib
import json
import random
from pathlib import Path
import sympy as s

ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']

def need(ok,msg):
    if not ok:
        raise RuntimeError(msg)

def load(rel):
    return json.loads((ROOT/rel).read_text())

names=set(PORTS)
for f in (ROOT/'forms').glob('*.json'):
    names.update(json.loads(f.read_text())['variables'])
names.update(['F','alpha','c','V','tau','y','eta','a','E','I'])
sy={x:s.Symbol(x) for x in names}

def ex(text):
    tree=ast.parse(text,mode='eval')
    allowed=(ast.Expression,ast.BinOp,ast.UnaryOp,ast.Name,ast.Load,ast.Constant,
             ast.Add,ast.Sub,ast.Mult,ast.Pow,ast.UAdd,ast.USub)
    for node in ast.walk(tree):
        need(isinstance(node,allowed),'restricted polynomial syntax')
        if isinstance(node,ast.Name):need(node.id in sy,'declared symbol '+node.id)
        if isinstance(node,ast.Constant):need(type(node.value) is int,'integer literal')
        if isinstance(node,ast.BinOp) and isinstance(node.op,ast.Pow):
            need(isinstance(node.right,ast.Constant) and type(node.right.value) is int
                 and node.right.value>=0,'fixed nonnegative exponent')
    return s.sympify(text,locals=sy)

def exact_zero(expression,msg):
    need(s.expand(expression)==0,msg)

def mod_eval(expr,env,p):
    def ev(n):
        if isinstance(n,ast.Expression): return ev(n.body)
        if isinstance(n,ast.Constant) and isinstance(n.value,int): return n.value%p
        if isinstance(n,ast.Name): return env[n.id]%p
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub): return -ev(n.operand)%p
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Add): return (ev(n.left)+ev(n.right))%p
            if isinstance(n.op,ast.Sub): return (ev(n.left)-ev(n.right))%p
            if isinstance(n.op,ast.Mult): return ev(n.left)*ev(n.right)%p
            if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant) and isinstance(n.right.value,int) and n.right.value>=0:
                return pow(ev(n.left),n.right.value,p)
        raise ValueError('Disallowed polynomial syntax')
    return ev(ast.parse(expr,mode='eval'))

def degree_bound(expr,vs):
    def d(n):
        if isinstance(n,ast.Expression):return d(n.body)
        if isinstance(n,ast.Constant):return 0
        if isinstance(n,ast.Name):return int(n.id in vs)
        if isinstance(n,ast.UnaryOp):return d(n.operand)
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,(ast.Add,ast.Sub)):return max(d(n.left),d(n.right))
            if isinstance(n.op,ast.Mult):return d(n.left)+d(n.right)
            if isinstance(n.op,ast.Pow):return d(n.left)*n.right.value
        raise ValueError('Degree syntax')
    return d(ast.parse(expr,mode='eval'))

def main():
    ledger=load('SOURCE_PINS.json')
    for row in ledger['files']:
        need(hashlib.sha256((ROOT/row['local_path']).read_bytes()).hexdigest()==row['sha256'],'source digest: '+row['local_path'])
    bind=load('BINDING.json')
    values={}
    for name,row in bind['payloads'].items():
        raw=gzip.decompress((ROOT/row['path']).read_bytes())
        need(hashlib.sha256(raw).hexdigest()==row['raw_sha256'],'fixed numeral: '+name)
        need(len(raw)==row['raw_bytes'],'fixed length: '+name)
        values[name]=int.from_bytes(raw,'little')
        need(values[name].bit_length()==row['bits'],'fixed bits: '+name)
    need(values['beta']==2**1064921-1,'exact beta')
    need(values['cone_A']==2**1113 and values['cone_B']==2**666104,'exact determinant scales')
    need(0<values['MC']<values['beta']<values['MF']<2*values['beta'],'source numeral bounds')

    # Independently derive the double-centering reduction from the literal
    # thirteen-row parent, including all nontrivial row multiples.
    p=load('upstream/joint__joint25_octic.json')
    out=load('forms/centered23_degree10.json')
    rr=[ex(x) for x in out['residuals']]
    eta,zeta,E,a,tau,nu,f,o=map(sy.get,['eta','zeta','E','a','tau','nu','f','o'])
    k=eta+zeta
    cc=(a-E)*k+eta
    vv=f*o-cc
    TT=E*(cc-eta)
    mp={sy['c']:cc,sy['V']:vv,sy['tau']:tau+TT,sy['y']:vv+nu}
    restored=[ex(x).xreplace(mp) for x in p['residuals']]
    expected=[rr[0],rr[1],(a-E)*rr[9],rr[2]+TT*rr[9],rr[3],
              rr[4]-rr[9],rr[5],s.Integer(0),rr[6],rr[7],rr[8],rr[9],rr[10]]
    for i,(left,right) in enumerate(zip(restored,expected)):
        exact_zero(left-right,'centering parent row '+str(i))
    need(len(out['variables'])==23 and len(rr)==11,'23/11 dimensions')
    need(max(s.Poly(r,*[sy[v] for v in out['variables']]).total_degree() for r in rr)==5,'decic residual degree')
    need([i for i,r in enumerate(rr) if sy['r'] in r.free_symbols]==[6],'private strong parameter r')
    coef=s.Poly(s.expand(rr[6]**2),*[sy[v] for v in out['variables']]).coeff_monomial(sy['r']**2*sy['a']**4*sy['eta']**4)
    need(coef==4,'decic degree certificate')

    reports=[{'name':out['name'],'variables':23,'degree':10,'source_identities':13}]
    jobs=[('joint22_degree16','pivot21_degree16'),('joint21_degree20','pivot20_degree20'),
          ('joint20_degree32','pivot19_degree32'),('joint19_degree88','pivot18_degree88')]
    rng=random.Random(101511)
    for old,new in jobs:
        parent=load('upstream/joint__'+old+'.json')
        result=load('forms/'+new+'.json')
        q=ex('beta*(3*J3+1)+1'); W=ex('4*(3*w3+1)')
        FF=(sy['K0']+W)*sy['C']-sy['z']*(q-1)
        aa=q-FF-sy['C']
        trans={sy['F']:FF,sy['alpha']:aa}
        index=[i for i,x in enumerate(parent['residuals']) if 'K0' in x]
        need(len(index)==1,'unique source transport row')
        index=index[0]
        exact_zero(ex(parent['residuals'][index]).xreplace(trans),'transport deleted identity')
        oldrows=[ex(x).xreplace(trans) for i,x in enumerate(parent['residuals']) if i!=index]
        newrows=[ex(x) for x in result['residuals']]
        # Equality of canonical polynomial expression trees is already an exact
        # identity certificate. This avoids a gratuitous giant expansion.
        for i,(left,right) in enumerate(zip(oldrows,newrows)):
            need(left==right or s.factor_terms(left)==s.factor_terms(right),
                 'literal pivot identity '+new+' row '+str(i))
        need(len(newrows)==len(parent['residuals'])-1,'one deleted residual')
        need(len(result['variables'])==len(parent['variables'])-1,'one deleted coordinate')
        need(set(result['variables'])==(set(parent['variables'])-{'F','alpha'})|{'C'},'coordinate pivot list')
        degree=max(degree_bound(x,set(result['variables'])) for x in result['residuals'])*2
        need(degree<=result['exact_degree'],'literal degree upper bound')
        # The exact leading coefficients are inherited from rows unaffected by
        # F,alpha (21/16 and 20/20), or from the same dominating T register
        # (19/32 and 18/88). PROOF.md supplies the full universal arguments.
        expected_coefs={'pivot21_degree16':'1','pivot20_degree20':'2**4*3**12*beta**12',
                        'pivot19_degree32':'2**12*3**20*beta**16','pivot18_degree88':'2**32*3**64*beta**56'}
        exact_zero(ex(result['degree_certificate']['coefficient'])-ex(expected_coefs[new]),'fixed positive degree coefficient')
        for prime in [1000000007,2305843009213693951]:
            for _ in range(12):
                env={v:rng.randrange(-100,101) for v in result['variables']}
                env.update({v:values[v]%prime for v in PORTS})
                oldenv=dict(env)
                oldenv['F']=mod_eval(str(FF),env,prime)
                oldenv['alpha']=mod_eval(str(aa),env,prime)
                need(mod_eval(parent['residuals'][index],oldenv,prime)==0,'finite transport diagnostic')
                for oldrow,newrow in zip([x for i,x in enumerate(parent['residuals']) if i!=index],result['residuals']):
                    need(mod_eval(oldrow,oldenv,prime)==mod_eval(newrow,env,prime),'actual numeral diagnostic')
        reports.append({'name':new,'variables':len(result['variables']),'degree':result['exact_degree'],
                        'exact_literal_pivot_identities':len(newrows)+1,'actual_numeral_modular_assignments':24})
    record={'status':'PASS','six_actual_numerals_authenticated':True,'source_files_authenticated':len(ledger['files']),
            'forms':reports,'proof_boundary':'Unbounded calibration is inherited; finite diagnostics only check transcription.'}
    (ROOT/'INDEPENDENT_CHECKS.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':
    main()
