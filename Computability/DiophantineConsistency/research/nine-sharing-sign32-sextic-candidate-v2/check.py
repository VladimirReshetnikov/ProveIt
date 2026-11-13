#!/usr/bin/env python3
"""External structural, degree and numerical checks of the q² substitution."""
import gzip,hashlib,json,random,sys
from collections import defaultdict
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1]
oldraw=(D/'research/nine-sharing-quartic65-sign33-candidate/seed.json').read_bytes();assert hashlib.sha256(oldraw).hexdigest()=='a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75'
raw=(P/'seed.json').read_bytes();assert hashlib.sha256(raw).hexdigest()=='f26172a2cad6e6a8fda042c67821f2fa7651426a62e980173eb5fac07cd835ab'
old=json.loads(oldraw);new=json.loads(raw);assert new['witness_count']==32 and new['total_coordinates']==33 and len(new['residuals'])==23
binding=new['coefficient_binding'];directory=(P/binding['path']).resolve();assert directory==(D/'candidates/one-page-padding-staircase-carrier65-2011/coefficients').resolve()
for name,record in binding['ports'].items():
    compressed=(directory/record['file']).read_bytes();plain=gzip.decompress(compressed)
    assert hashlib.sha256(compressed).hexdigest()==record['gzip_sha256']
    assert hashlib.sha256(plain).hexdigest()==record['raw_sha256'] and len(plain)==record['raw_bytes']
    value=int.from_bytes(plain,'big');assert value>0 and value.bit_length()==record['bits']

q2=old['residuals'][0]['expr'][2]
def degree(t):
    op=t[0]
    if op=='var':assert len(t)==2 and 1<=t[1]<=32;return 1
    if op in ('num','port'):return 0
    assert op in ('add','sub','mul') and len(t)==3
    a,b=degree(t[1]),degree(t[2]);return a+b if op=='mul' else max(a,b)
def substitute(t):
    if t[0]=='var':
        i=t[1];return q2 if i==15 else ['var',i-(i>15)]
    if t[0] in ('num','port'):return t
    return [t[0],substitute(t[1]),substitute(t[2])]
for x,y in zip(old['residuals'][1:],new['residuals']):
    assert x['gate']==y['gate'] and x['kind']==y['kind'] and substitute(x['expr'])==y['expr']
degrees=[degree(x['expr']) for x in new['residuals']];assert max(degrees)==3
cubic=[x['gate'] for x,d in zip(new['residuals'],degrees) if d==3]
assert cubic==['q3','tau','cTminusR']
def eval_ast(t,vs,ports):
    op=t[0]
    if op=='var':return vs[t[1]]
    if op=='num':return t[1]
    if op=='port':return ports[t[1]]
    a=eval_ast(t[1],vs,ports);b=eval_ast(t[2],vs,ports)
    return a+b if op=='add' else a-b if op=='sub' else a*b
rng=random.Random(20261106)
for _ in range(16):
    vs=[rng.randint(-2,3) for _ in range(33)];ports={k:rng.randint(1,5) for k in new['fixed_ports']}
    q=ports['beta']*(vs[1]+1)+1
    oldvs=vs[:15]+[q*q]+vs[15:]
    assert len(oldvs)==34 and eval_ast(old['residuals'][0]['expr'],oldvs,ports)==0
    for x,y in zip(old['residuals'][1:],new['residuals']):assert eval_ast(x['expr'],oldvs,ports)==eval_ast(y['expr'],vs,ports)
# For the first retained q3 residual only, compute a polynomial in X=var1 and B=beta,
# with every other variable set to zero; no other port occurs in this residual.
def poly_add(a,b,sign=1):
    out=defaultdict(int,a)
    for k,v in b.items():out[k]+=sign*v
    return {k:v for k,v in out.items() if v}
def poly_mul(a,b):
    out=defaultdict(int)
    for (x1,b1),v1 in a.items():
        for (x2,b2),v2 in b.items():out[(x1+x2,b1+b2)]+=v1*v2
    return {k:v for k,v in out.items() if v}
def symbolic(t):
    op=t[0]
    if op=='num':return {(0,0):t[1]} if t[1] else {}
    if op=='var':return {(1,0):1} if t[1]==1 else {}
    if op=='port':assert t[1]=='beta';return {(0,1):1}
    a,b=symbolic(t[1]),symbolic(t[2]);return poly_add(a,b) if op=='add' else poly_add(a,b,-1) if op=='sub' else poly_mul(a,b)
f=symbolic(new['residuals'][0]['expr'])
assert {b:v for (x,b),v in f.items() if x==0}=={0:-1,1:-3,2:-3,3:-1}
assert {b:v for (x,b),v in f.items() if x==3}=={3:-1}
out={'status':'PASS_EXTERNAL_SUBSTITUTION_STRUCTURE_AND_CONTROLS','witness_count':32,'residual_count':23,'max_residual_degree':3,'sum_of_squares_degree_upper':6,'cubic_residuals':cubic,'first_zero_witness':'-(beta+1)^3','first_residual_pure_x1_cubic_coefficient':'-beta^3','structural_comparison':'all 23 transformed ASTs match independent recursive substitution and index map','numerical_controls':16,'verified_coefficient_files':4,'seed_sha256':hashlib.sha256(raw).hexdigest(),'scope':'External AST substitution and finite controls only; exact degree and all-model equivalence are mathematical arguments needing independent review and formal proof. No higher-degree Jones or endpoint theorem.'}
print(json.dumps(out,indent=2,sort_keys=True))
