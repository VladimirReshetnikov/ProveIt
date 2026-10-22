#!/usr/bin/env python3
"""Explicit fixed-input Diophantine circuits and reproducible arithmetic checks.

Python standard library only. The checks verify the finite arithmetic, not the
absence of a ZFC refutation and not the inherited Pell/compiler theorems.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[1]
WITNESSES = ['Jrep', 'F', 'alpha', 'transport_quotient', 'f', 'h', 'i',
             'auxiliary_quotient', 's', 'w', 'tau_root', 'eta', 'zeta',
             'y_aux', 'Z', 'gamma']
NORMS = ['norm_first', 'norm_main', 'norm_aux', 'norm_index',
         'norm_transport', 'norm_strong']
SIGNED_ROOTS = {'tau_root', 'y_aux'}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def read_sources():
    return json.loads((ROOT/'data/fixed_input_linear_guard_sources.json').read_text())

def closure(rows, outputs):
    need = set(outputs)
    keep = []
    for row in reversed(rows):
        name, op, a, b = row
        if name in need:
            keep.append(row)
            need.update(x for x in (a,b) if isinstance(x,str))
    return list(reversed(keep))

def source_system():
    return closure(read_sources()['source74'], NORMS+['W'])

def source_sos():
    rows = [r[:] for r in source_system()]
    squares=[]
    for n,name in enumerate(NORMS+['W']):
        rhs = 'W0' if name == 'W' else 1
        residual, square = f'residual_{n}', f'residual_square_{n}'
        rows.extend([[residual,'-',name,rhs],[square,'*',residual,residual]])
        squares.append(square)
    last=squares[0]
    for n,square in enumerate(squares[1:],1):
        name=f'sum_{n}'
        rows.append([name,'+',last,square]); last=name
    return rows,last

def interface(rows):
    made=set()
    ports=set()
    for name,op,a,b in rows:
        require(name not in made and op in ('+','-','*'),'invalid instruction')
        for v in (a,b):
            if isinstance(v,str) and v not in made: ports.add(v)
        made.add(name)
    require(not (ports & made),'forward or cyclic reference')
    return sorted(ports)

def ledger(rows):
    c=Counter(r[1] for r in rows)
    return {'operations':len(rows),'multiplications':c['*'],
            'additions_subtractions':c['+']+c['-']}

def evaluate(rows, values, modulus=None):
    v=dict(values)
    for name,op,a,b in rows:
        x=v[a] if isinstance(a,str) else a
        y=v[b] if isinstance(b,str) else b
        z=x+y if op=='+' else x-y if op=='-' else x*y
        v[name]=z if modulus is None else z%modulus
    return v

def ptrim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a

def pop(a,b,op,p):
    if op=='*':
        z=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): z[i+j]=(z[i+j]+x*y)%p
    else:
        z=[0]*max(len(a),len(b))
        for i in range(len(z)):
            x=a[i] if i<len(a) else 0
            y=b[i] if i<len(b) else 0
            z[i]=(x+y if op=='+' else x-y)%p
    return ptrim(z)

def polynomial_evaluate(rows,values,p):
    v={k:(x[:] if isinstance(x,list) else [x%p]) for k,x in values.items()}
    for name,op,a,b in rows:
        x=v[a] if isinstance(a,str) else [a%p]
        y=v[b] if isinstance(b,str) else [b%p]
        v[name]=pop(x,y,op,p)
    return v

def emitted_packets():
    src=read_sources()
    packets={}
    for count,degree in [(73,156),(74,144)]:
        rows=src[f'source{count}']
        packets[f'polynomial{count}.json']={
            'domain':'16 strictly positive integer variables',
            'witnesses':WITNESSES,'fixed_numerals':[x for x in interface(rows) if x not in WITNESSES],
            'source':rows,'output':'polynomial','equation':'polynomial = 0',
            'ledger':ledger(rows),'exact_degree':degree,
            'constant_specification':'data/constants_recipe.json',
            'proof_status':'mathematical proof; new endpoint not kernel formalized'}
    rows=source_system()
    packets['system65.json']={'domain':'16 strictly positive integer variables',
        'witnesses':WITNESSES,'source':rows,
        'comparisons':[[n,'W0' if n=='W' else 1] for n in NORMS+['W']],
        'ledger':ledger(rows),'equations':7,'maximum_residual_degree':60,
        'constant_specification':'data/constants_recipe.json'}
    sos,out=source_sos()
    packets['sos85.json']={'domain':'16 strictly positive integer variables',
        'witnesses':WITNESSES,'source':sos,'output':out,
        'ledger':ledger(sos),'exact_degree':120}
    prefix=[]
    integer_inputs=[]
    for name in WITNESSES:
        if name in SIGNED_ROOTS:
            integer_inputs.append(name)
            continue
        a,b,c=(name+'__'+s for s in ('a','b','c'))
        integer_inputs.extend([a,b,c])
        aa,bb,cp,cc,ab,abc=(name+'__'+s for s in ('aa','bb','cp','cc','ab','abc'))
        prefix.extend([[aa,'*',a,a],[bb,'*',b,b],[cp,'+',c,1],
                       [cc,'*',c,cp],[ab,'+',aa,bb],[abc,'+',ab,cc],
                       [name,'+',abc,1]])
    integer_rows=prefix+src['source73']
    require(len(integer_inputs)==44 and len(integer_rows)==171,'integer conversion counts')
    packets['integer44.json']={'domain':'44 unrestricted integer variables',
        'variables':integer_inputs,'source':integer_rows,'output':'polynomial',
        'fixed_numerals':[x for x in interface(integer_rows) if x not in integer_inputs],
        'ledger':ledger(integer_rows),'exact_degree':312,
        'proof':'Each positive coordinate is 1+a^2+b^2+c(c+1); tau_root and y_aux may be signed because only their squares occur and neither can vanish on the zero set.',
        'constant_specification':'data/constants_recipe.json'}
    return packets

def verify():
    src=read_sources(); rows73,rows74=src['source73'],src['source74']
    rows65=source_system(); sos,sosout=source_sos()
    expected=[(rows73,73,41,32),(rows74,74,42,32),(rows65,65,35,30),(sos,85,42,43)]
    for rows,n,m,a in expected:
        require(ledger(rows)=={'operations':n,'multiplications':m,'additions_subtractions':a},'ledger')
        outputs=['polynomial'] if n in (73,74) else NORMS+['W'] if n==65 else [sosout]
        require(closure(rows,outputs)==rows,'dead gates')
        require(set(WITNESSES) <= set(interface(rows)),'unused witness')
    # Delta-scaled equality is an all-integer polynomial identity. Numerical
    # fixtures supplement the explicit coefficient-sharing identity in the paper.
    rng=random.Random(20261022)
    count=0
    for signed in (False,True):
        for _ in range(40):
            vals={k:rng.randint(-5,5) if signed else rng.randint(1,5) for k in WITNESSES}
            vals.update(Bm1=31,Kconstant=113,twice_cell_bits=10,MC=10,MF=59,W0=128)
            vals['input_unit_constant']=1-3*vals['W0']
            a=evaluate(rows74,vals); b=evaluate(rows73,vals); c=evaluate(sos,vals)
            require(b['polynomial']==a['A']*a['polynomial'],'scaled polynomial identity')
            residuals=[c[n]-1 for n in NORMS]+[c['W']-vals['W0']]
            require(c[sosout]==sum(z*z for z in residuals),'SOS identity')
            require((a['norm_input']-1)%3==0,'affine input congruence')
            count+=1
    diagnostics=[]
    for p in (1000000007,1000000009):
        vals={k:[rng.randrange(1,19),rng.randrange(1,19)] for k in WITNESSES}
        vals.update(Bm1=31,Kconstant=113,twice_cell_bits=10,MC=10,MF=59,W0=128,input_unit_constant=-383)
        a=polynomial_evaluate(rows74,vals,p); b=polynomial_evaluate(rows73,vals,p)
        c=polynomial_evaluate(sos,vals,p)
        require(len(a['polynomial'])-1==144,'unscaled exact degree diagnostic')
        require(len(b['polynomial'])-1==156,'scaled exact degree diagnostic')
        require(len(c[sosout])-1==120,'SOS exact degree diagnostic')
        require(b['polynomial']==pop(a['A'],a['polynomial'],'*',p),'coefficientwise identity')
        diagnostics.append({'prime':p,'unscaled_degree':144,'scaled_degree':156,'sos_degree':120,
                            'scaled_top_coefficient':b['polynomial'][-1]})
    # This checks the domain converter on bounded examples; the complete proof
    # uses the three-square theorem, as explained in the paper.
    represented={a*a+b*b+c*(c+1) for a in range(33) for b in range(33) for c in range(33)}
    require(set(range(1001))<=represented,'positive parametrization fixtures')
    integer=emitted_packets()['integer44.json']
    integer_rows=integer['source']
    require(ledger(integer_rows)=={'operations':171,'multiplications':83,'additions_subtractions':88},'integer ledger')
    require(closure(integer_rows,['polynomial'])==integer_rows,'dead integer gates')
    require(set(integer['variables']) <= set(interface(integer_rows)),'unused integer variable')
    vals={k:[rng.randrange(1,19),rng.randrange(1,19)] for k in integer['variables']}
    vals.update(Bm1=31,Kconstant=113,twice_cell_bits=10,MC=10,MF=59,input_unit_constant=-383)
    integer_polynomial=polynomial_evaluate(integer_rows,vals,1000000007)['polynomial']
    require(len(integer_polynomial)-1==312,'integer exact degree diagnostic')
    return {'status':'PASS','arithmetic_evaluation_fixtures':count,
            'degree_coefficient_diagnostics':diagnostics,
            'positive_parameter_fixtures':1001,
            'ledgers':{str(len(r)):ledger(r) for r,_,_,_ in expected},
            'integer_variables':44,'integer_degree_diagnostic':312,
            'integer_ledger':ledger(integer_rows),
            'scope':'Finite circuit checks and algebra diagnostics only. Diagnostic numeral ports are not claimed to encode a program. No ZFC halting or nonhalting search, and no full Pell witness, is used.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--emit',action='store_true')
    ap.add_argument('--verify',action='store_true')
    args=ap.parse_args()
    if args.emit:
        for name,packet in emitted_packets().items():
            (ROOT/'data'/name).write_text(json.dumps(packet,indent=2)+'\n')
    if args.verify or not args.emit:
        report=verify()
        (ROOT/'verification/arithmetic.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report,indent=2))

if __name__=='__main__': main()
