#!/usr/bin/env python3
"""Independent structural and exact polynomial audit of AQ22-to-AQ17."""
import copy,gzip,hashlib,json,sys
from collections import Counter
from functools import lru_cache
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
ROOT=Path(__file__).resolve().parents[2];RESEARCH=ROOT/'research';REV=ROOT/'reviews'
D=RESEARCH/'aq22-positive-binding-survey';P=RESEARCH/'adaptive-square-sums22-degree10/candidate.json';C=D/'candidate17.json'
PORT=REV/'aq22-pdf-historical-lean-binding-independent/receipt.json'
POLY=ROOT/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
parent=J(P);child=J(C);carrier=J(POLY);ports=J(PORT)
inputs=[Path(__file__),P,C,D/'survey.py',D/'verify_candidate17.py',POLY,PORT]
for name in child['fixed_numerals']:
    inputs.append(POLY.parent/'coefficients'/carrier['coefficient_binding']['ports'][name]['file'])
before={str(p.resolve()):H(p) for p in inputs}
assert H(P)=='1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106'
assert H(C)=='760b9e7babbb559b7175344915456fdc3d9bd8ce85382873d4915faf2cd76d81'
repl={'scaleVariable':'M','mainScaleVariable':'U','ellVariable':'ell','cSquareVariable':'c2','deltaVariable':'DeltaComputed'}
removed={'scaleDifference','mainScaleDifference','ellDifference','cSquareDifference','deltaDifference'}
assert child['eliminated_bindings']==repl and child['parent_sha256']==H(P)
assert child['witnesses']==[x for x in parent['witnesses'] if x not in repl]
assert len(child['witnesses'])==len(set(child['witnesses']))==17
assert child['fixed_numerals']==parent['fixed_numerals']==['beta','K0','MC','MF']
assert not set(child['witnesses'])&set(child['fixed_numerals'])

def validate_graph(g,expected):
    inputs=set(g['witnesses']+g['fixed_numerals']); rows={};live=set(inputs)
    assert len(g['source'])==expected
    for name,op,a,b in g['source']:
        assert name not in live and op in ('+','-','*')
        assert all(isinstance(x,int) or x in live for x in (a,b))
        rows[name]=(op,a,b);live.add(name)
    assert g['output'] in rows
    return rows
pr=validate_graph(parent,114);cr=validate_graph(child,99)
live=set();pending=[child['output']]
while pending:
    node=pending.pop()
    if not isinstance(node,str) or node in live:continue
    live.add(node)
    if node in cr:pending.extend(cr[node][1:])
assert set(cr)<=live and set(child['witnesses']+child['fixed_numerals'])<=live
# Structural identity after substitution is stronger than equality after
# polynomial simplification: each surviving residual has the same expression
# tree. Hash-consed tuples prevent exponential duplication.
def expressions(rows, substitutions):
    @lru_cache(None)
    def walk(name):
        if isinstance(name,int):return ('constant',name)
        if name in substitutions:return walk(substitutions[name])
        if name not in rows:return ('input',name)
        op,a,b=rows[name];return (op,walk(a),walk(b))
    return walk
orig=expressions(pr,repl);new=expressions(cr,{})
factors=['A0','A1','auxResidual','g72','scaleDifference','mainScaleDifference','rankDifference','ellDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference']
assert child['residuals']==[x for x in factors if x not in removed]
for factor in child['residuals']:assert orig(factor)==new(factor),factor
for binding,difference in [('scaleVariable','scaleDifference'),('mainScaleVariable','mainScaleDifference'),('ellVariable','ellDifference'),('cSquareVariable','cSquareDifference'),('deltaVariable','deltaDifference')]:
    assert pr[difference]==('-',binding,repl[binding])
    _,left,right=orig(difference);assert left==right
# Check actual output trees in both graphs consist exactly of the listed squares.
def check_squares(rows,output,expected):
    def leaves(name):
        op,a,b=rows[name]
        if op=='+':return leaves(a)+leaves(b)
        assert op=='*' and a==b and a in expected
        return [a]
    assert Counter(leaves(output))==Counter(expected)
check_squares(pr,parent['output'],factors);check_squares(cr,child['output'],child['residuals'])
# Bind the five claimed positive right-hand sides to exact graph operations.
positive={
 'qm':('*','J','beta'),'q':('+',1,'qm'),'q2':('*','q','q'),'q3':('*','q','q2'),
 'M':('*','q3','qm'),'U':('*','Y','q2'),'E':('*','X','Y'),'k':('+','eta','zeta'),
 'kY':('*','Y','k'),'ell':('*','E','kY'),'c':('+','eta','kY'),'c2':('*','c','c'),
 'a':('+','E','Y'),'g15':('*',4,'a'),'H':('+',3,'g15'),'g17':('*','a','a'),
 'DeltaComputed':('+','H','g17')}
for name,row in positive.items():assert pr[name]==row,(name,pr[name],row)
# Check right-hand sides depend exclusively on surviving witnesses/ports.
def deps(name):
    if isinstance(name,int):return set()
    if name not in pr:return {name}
    _,a,b=pr[name];return deps(a)|deps(b)
for name in repl.values():assert deps(name)<=set(child['witnesses']+child['fixed_numerals'])
assert ports['status']=='PASS_INDEPENDENT_AQ22_FINITE_BINDING_REVIEW'
assert [r['name'] for r in ports['ports']]==child['fixed_numerals']
actual=[]
for i,name in enumerate(child['fixed_numerals']):
    meta=carrier['coefficient_binding']['ports'][name]; packed=(POLY.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(packed).hexdigest()==meta['gzip_sha256']
    raw=gzip.decompress(packed);digest=hashlib.sha256(raw).hexdigest();assert digest==meta['raw_sha256']==ports['ports'][i]['integer_sha256']
    actual.append(int.from_bytes(raw,'big'))
beta=actual[0];assert beta>0
# Exercise the reconstruction in both directions on nonsolution assignments,
# comparing every residual; positivity itself follows from the graph above.
def reconstruction(witness_values,port_values):
    assert set(witness_values)==set(child['witnesses'])
    assert all(v>0 for v in witness_values.values()) and port_values['beta']>0
    def run(rows,initial):
        env=dict(initial)
        for name,(op,a,b) in rows.items():
            x=a if isinstance(a,int) else env[a];y=b if isinstance(b,int) else env[b]
            env[name]=x+y if op=='+' else x-y if op=='-' else x*y
        return env
    current=run(cr,dict(witness_values,**port_values))
    reconstructed={name:current[node] for name,node in repl.items()}
    assert all(value>0 for value in reconstructed.values())
    old=run(pr,dict(witness_values,**reconstructed,**port_values))
    assert all(old[n]==current[n] for n in child['residuals'])
    assert all(old[n]==0 for n in removed)
    assert old[parent['output']]==current[child['output']]
    return reconstructed
ones={name:1 for name in child['witnesses']}
reconstruction(ones,dict(beta=1,K0=2,MC=3,MF=4))
reconstruction({name:i+1 for i,name in enumerate(child['witnesses'])},dict(beta=2,K0=-1,MC=0,MF=4))
for bad_w,bad_p in ((dict(ones,J=0),dict(beta=1,K0=1,MC=1,MF=1)),
                    (ones,dict(beta=0,K0=1,MC=1,MF=1))):
    try:reconstruction(bad_w,bad_p)
    except AssertionError:pass
    else:raise AssertionError('nonpositive premise accepted')
# Sparse polynomial coefficients with monomials represented as sorted tuples
# of variable indices, independently of the author's fixed-length exponent
# representation. Witness degree ignores indices 17..20 (fixed ports).
allvars=child['witnesses']+child['fixed_numerals'];zero=()
def plus(a,b,sign=1):
    c=a.copy()
    for m,v in b.items():c[m]=c.get(m,0)+sign*v
    return {m:v for m,v in c.items() if v}
def times(a,b):
    c={}
    for x,u in a.items():
        for y,v in b.items():
            m=tuple(sorted(x+y));c[m]=c.get(m,0)+u*v
    return {m:v for m,v in c.items() if v}
@lru_cache(None)
def evaluate(n):
    if isinstance(n,int):return {zero:n} if n else {}
    if n in allvars:return {(allvars.index(n),):1}
    op,a,b=cr[n];x=evaluate(a);y=evaluate(b)
    return plus(x,y) if op=='+' else plus(x,y,-1) if op=='-' else times(x,y)
degrees={name:max((sum(i<17 for i in mon) for mon in evaluate(name)),default=-1) for name in child['residuals']}
assert max(degrees.values())==degrees['A0']==16
witness=tuple(sorted([allvars.index('J')]*8+[allvars.index('X')]*2+[allvars.index('Y')]*4+[allvars.index('eta')]*2))
matching={tuple(i for i in mon if i>=17):coeff for mon,coeff in evaluate('A0').items() if tuple(i for i in mon if i<17)==witness}
assert matching=={(17,)*8:-1}
# The exact specialized coefficient is -beta^8, proven nonzero by beta>0.
coefficient_magnitude=beta**8
assert coefficient_magnitude>0
coeff_hash=hashlib.sha256(coefficient_magnitude.to_bytes((coefficient_magnitude.bit_length()+7)//8,'big')).hexdigest()
# For a sum of squares over real/integer coefficients the leading homogeneous
# sum cannot cancel, so the equation has exactly degree 2*16 = 32.
# Controlled corruptions must fail independent structural checks.
mut=copy.deepcopy(cr);op,a,b=mut['g64'];assert op=='+';mut['g64']=('-',a,b)
assert expressions(mut,{})('A0')!=orig('A0') or any(expressions(mut,{})(n)!=orig(n) for n in child['residuals'])
mut=copy.deepcopy(cr);_,a,b=mut['bindingSurveySum0'];mut['bindingSurveySum0']=('-',a,b)
try:check_squares(mut,child['output'],child['residuals'])
except AssertionError:pass
else:raise AssertionError('output sign mutation accepted')
mut_repl=dict(repl);mut_repl['scaleVariable']='U'
assert expressions(pr,mut_repl)('A0')!=new('A0')
assert {str(p.resolve()):H(p) for p in inputs}==before
result={'status':'PASS_AQ17_INDEPENDENT_FINITE_AUDIT','inputs_sha256':before,'variables':17,'gates':99,
 'parent_residuals':13,'kept_residuals':8,'eliminated_bindings':repl,'residual_degrees':degrees,
 'actual_beta_positive':True,'specialized_A0_coefficient':'-beta^8','absolute_coefficient_sha256':coeff_hash,
 'absolute_coefficient_bits':coefficient_magnitude.bit_length(),'total_degree':32,
 'scope':'Ordinary exact algebra for positive integer assignments and the recorded actual port bytes; no Lean AQ17 proof, no PDF claim, no global minimum. AQ22 historical PDF binding retains its manually transcribed decoder boundary.'}
out=Path(__file__).resolve().parent/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(result['status'],H(out))
