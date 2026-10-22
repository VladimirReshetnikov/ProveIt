#!/usr/bin/env python3
"""Emit and audit ordinary-strong inputless variants; Python stdlib only.

The input ordinary_blank_system_61.json is literal circuit data. The checks
are algebra/ledger checks, not a compiler or logical consistency test.
"""
import ast
import collections
import copy
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[1]
CIRCUITS = ROOT / 'circuits'

def dump(name, data):
    path = ROOT / name if '/' in name else CIRCUITS / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')

def ledger(source, free, outputs):
    known=set(free); producers={}; count=collections.Counter()
    for name,op,a,b in source:
        assert name not in known and op in '+-*'
        assert all(type(x) is int or x in known for x in (a,b))
        known.add(name); producers[name]=(a,b);count[op]+=1
    need=set(x for x in outputs if isinstance(x,str))
    for name,op,a,b in reversed(source):
        if name in need: need.update(x for x in (a,b) if isinstance(x,str))
    assert set(producers)<=need and set(free)<=need
    return dict(operations=len(source),M=count['*'],A=count['+']+count['-'],all_live=True)

def evaluate(source, supplied):
    v=dict(supplied)
    for name,op,a,b in source:
        a=a if type(a) is int else v[a]; b=b if type(b) is int else v[b]
        v[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return v

def get(v,a): return a if type(a) is int else v[a]

def finish_system(packet, filename):
    p=copy.deepcopy(packet)
    p['ledger']=ledger(p['source'],p['witnesses']+p['fixed_numerals'],sum(p['comparisons'],[]))
    dump(filename,p)
    sos=copy.deepcopy(p)
    for j,(a,b) in enumerate(p['comparisons']):
        sos['source'] += [[f'r{j}','-',a,b],[f'r{j}_square','*',f'r{j}',f'r{j}']]
    out='r0_square'
    for j in range(1,len(p['comparisons'])):
        sos['source'].append([f'sos{j}','+',out,f'r{j}_square']);out=f'sos{j}'
    sos['output']=out
    sos_filename = {'ordinary_blank_system_61.json': 'ordinary_blank_sos_78.json',
                    'ordinary_blank_four_system_63.json': 'ordinary_blank_four_sos_74.json'}[filename]
    sos['name']=sos_filename.removesuffix('.json')
    sos['degree']=2*max(p['residual_exact_degrees'])
    sos['scope']='Single sum-of-squares polynomial, equivalent to the declared ordinary system on its positive domain.'
    sos['ledger']=ledger(sos['source'],sos['witnesses']+sos['fixed_numerals'],[out])
    sos.pop('comparisons')
    dump(sos_filename,sos)
    return p,sos

base=json.loads((CIRCUITS/'ordinary_blank_system_61.json').read_text())
base.pop('ledger',None)
base,sixsos=finish_system(base,'ordinary_blank_system_61.json')
four=copy.deepcopy(base)
four['name']='ordinary_blank_four_system_63'
four['source'] += [['first_transport','*','norm_first','norm_transport'],['main_index','*','norm_main','norm_index']]
four['comparisons']=[['first_transport',1],['main_index',1],['norm_aux',1],['R16','auxiliary_reduced_coefficient']]
four['residual_exact_degrees']=[24,25,28,22]
four['scope']='Four equations, tuplewise equivalent to the ordinary six equations on positive integers by norm sign arguments.'
four,foursos=finish_system(four,'ordinary_blank_four_system_63.json')
product=copy.deepcopy(base)
product['source'] += [['strong_difference','-','R16','auxiliary_reduced_coefficient'],['strong_unit','+','strong_difference',1]]
out='norm_first'
for j,factor in enumerate(['norm_main','norm_aux','norm_index','norm_transport','strong_unit']):
    product['source'].append([f'prod{j}','*',out,factor]);out=f'prod{j}'
product['source'].append(['polynomial','-',out,1])
product.update(name='ordinary_blank_product69',output='polynomial',degree=99)
product['scope']='Single unit-factor product; positive zero-set equivalence uses the signed bootstrap in proofs/ORDINARY_REDUCTION.md.'
product.pop('comparisons')
product['ledger']=ledger(product['source'],product['witnesses']+product['fixed_numerals'],['polynomial'])
dump('ordinary_blank_product69.json',product)

# Literal quadratic residuals, with every abbreviation affine.
primary='J F alpha z f h i T s w tau eta zeta y gamma'.split()
registers='N E P c a X D C2 G L R F2 V0 V g I Baux Delta'.split()
ports='beta K0 MC MF'.split()
variables=primary+registers
residual_text=[
 'L-(q*q-1)',
 'N-q*(L+1)',
 'X-w*q',
 'a-E-s*N',
 'E-X*(a-E)',
 'c-k*(a-E)-eta',
 'P-E*(c-eta)-k',
 'tau*tau-P*(P-k)-1',
 'D-X-a*c-gamma*H',
 'Delta-a*a-H',
 'C2-c*c',
 'D*D-Delta*C2-1',
 'k-R-1-h*E',
 'G-(q-1)*(q-F)-alpha',
 'R-L*G-(MC+q*MF)*J',
 '(K0+w)*C+q-F-z*(q-1)-1',
 'F2-f*f',
 'V0-T*f+1',
 'V-c*V0+R*F2',
 'g-y*y+V*V',
 'I-i*C2',
 'Baux-I*I',
 'Baux-Delta*(F2-1)',
 'y*y-Baux*g-1',
]
allnames=variables+ports
zero=(0,)*len(allnames)
def pconst(n): return {} if n==0 else {zero:n}
def padd(p,q,sign=1):
    z=dict(p)
    for m,c in q.items():
        z[m]=z.get(m,0)+sign*c
        if not z[m]: del z[m]
    return z
def pmul(p,q):
    z={}
    for a,ca in p.items():
        for b,cb in q.items():
            m=tuple(x+y for x,y in zip(a,b));z[m]=z.get(m,0)+ca*cb
    return {m:c for m,c in z.items() if c}
env={}
for j,name in enumerate(allnames):
    t=list(zero);t[j]=1;env[name]={tuple(t):1}
def parse(text):
    def visit(x):
        if isinstance(x,ast.Constant):return pconst(x.value)
        if isinstance(x,ast.Name):return env[x.id]
        if isinstance(x,ast.UnaryOp) and isinstance(x.op,ast.USub):return {m:-c for m,c in visit(x.operand).items()}
        assert isinstance(x,ast.BinOp)
        a,b=visit(x.left),visit(x.right)
        if isinstance(x.op,ast.Add):return padd(a,b)
        if isinstance(x.op,ast.Sub):return padd(a,b,-1)
        assert isinstance(x.op,ast.Mult)
        return pmul(a,b)
    return visit(ast.parse(text,mode='eval').body)
for name,text in [('q','beta*J+1'),('k','eta+zeta'),('H','4*a+3'),('C','q-F-alpha')]:env[name]=parse(text)
residuals=[parse(t) for t in residual_text]
degree=lambda p:max((sum(m[:len(variables)]) for m in p),default=-1)
assert len(variables)==33 and len(residuals)==24
assert all(degree(p)<=2 for p in residuals)
quartic={}
for p in residuals:quartic=padd(quartic,pmul(p,p))
assert degree(quartic)==4
tau4=list(zero);tau4[variables.index('tau')]=4
assert quartic[tuple(tau4)]==1
def sparse(p):
    return [{'coefficient':c,'powers':{n:e for n,e in zip(allnames,m) if e}} for m,c in sorted(p.items())]
quad={'name':'ordinary_quartic33','domain':'strictly positive integers','variables':variables,
      'fixed_ports':ports,'affine_abbreviations':{'q':'beta*J+1','k':'eta+zeta','H':'4*a+3','C':'q-F-alpha'},
      'residual_expressions':residual_text,'expanded_residuals':[sparse(p) for p in residuals],
      'single_polynomial':'sum of squares of the 24 listed residuals',
      'expanded_quartic':sparse(quartic),'degree':4,'quartic_term_count':len(quartic),
      'degree_certificate':'coefficient of tau^4 equals 1; no residual exceeds degree 2'}
dump('ordinary_quartic33.json',quad)

# Compare literal source with independently specified arithmetic on arbitrary
# signed diagnostic assignments. These inputs are not machine coefficients.
rng=random.Random(20261022)
for case in range(96):
    v={n:rng.randrange(-3,6) for n in base['witnesses']}
    v.update(dict(zip(base['fixed_numerals'],[31,127,10,45])))
    b=evaluate(base['source'],v)
    q=31*v['Jrep']+1; X=v['w']*q;Y=v['s']*q**3;E=X*Y;k=v['eta']+v['zeta']
    c=k*Y+v['eta'];a=E+Y;H=4*a+3;Delta=a*a+H;D=X+a*c+v['gamma']*H
    C=q-v['F']-v['alpha'];R=((q-1)*(q-v['F'])+v['alpha'])*(q*q-1)+(10+q*45)*v['Jrep']
    V=c*(v['auxiliary_quotient']*v['f']-1)-R*v['f']**2;I=v['i']*c*c;A0=Delta*(v['f']**2-1)
    expected=[v['tau_root']**2-(E*k*Y)*(E*k*Y+k)-1,D*D-Delta*c*c-1,
              A0*(V*V-v['y_aux']**2)+v['y_aux']**2-1,k-v['h']*E-R-1,
              (127+v['w'])*C+q-v['F']-v['transport_quotient']*(q-1)-1,I*I-A0]
    assert [get(b,a)-get(b,c) for a,c in base['comparisons']]==expected
    f=evaluate(four['source'],v)
    fr=[get(f,a)-get(f,b) for a,b in four['comparisons']]
    assert fr==[(expected[0]+1)*(expected[4]+1)-1,(expected[1]+1)*(expected[3]+1)-1,expected[2],expected[5]]
    assert evaluate(foursos['source'],v)[foursos['output']]==sum(t*t for t in fr)
    assert evaluate(sixsos['source'],v)[sixsos['output']]==sum(t*t for t in expected)
    z=1
    for t in expected:z*=t+1
    assert evaluate(product['source'],v)['polynomial']==z-1

receipt={'diagnostic_identity_cases':96,'six_system_ledger':base['ledger'],
         'four_system_ledger':four['ledger'],'six_SOS_ledger':sixsos['ledger'],
         'four_SOS_ledger':foursos['ledger'],'product69_ledger':product['ledger'],
         'quartic_unknowns':33,'quadratic_equations':24,'quartic_degree':4,
         'quartic_tau4_coefficient':1,'quartic_expanded_terms':len(quartic),
         'scope':'Algebraic transcription, exact sparse quadratic expansion, positivity proved in proofs/ORDINARY_REDUCTION.md; no full Pell witness or formal compiler build.'}
dump('verification/ordinary.json',receipt)
print(json.dumps(receipt,indent=2))
