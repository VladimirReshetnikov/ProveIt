#!/usr/bin/env python3
"""Independent symbolic audit of the new integer sextic.

Does not import the sextic builder, its verifier, or upstream arithmetic code.
"""
import ast,hashlib,json,sys
from pathlib import Path

OUT=Path(__file__).resolve().parent
ROOT=Path(sys.argv[1]) if len(sys.argv)>1 else OUT
parent=json.loads((ROOT/'upstream/quartic41.json').read_text())
child=json.loads((ROOT/'sextic34.json').read_text())
names=child['variables']+child['fixed_numerals']; n=len(names)
Z=(0,)*n
def const(c): return {Z:c} if c else {}
def add(a,b):
    out=dict(a)
    for m,c in b.items():
        x=out.get(m,0)+c
        if x: out[m]=x
        else: out.pop(m,None)
    return out
def neg(a):return {m:-c for m,c in a.items()}
def mul(a,b):
    out={}
    for m,c in a.items():
        for k,d in b.items():
            e=tuple(x+y for x,y in zip(m,k)); out[e]=out.get(e,0)+c*d
    return {m:c for m,c in out.items() if c}
def power(a,k):
    out=const(1)
    for _ in range(k):out=mul(out,a)
    return out
env={}
for j,name in enumerate(names):
    v=[0]*n;v[j]=1;env[name]={tuple(v):1}
def parse(text,context):
    def visit(node):
        if isinstance(node,ast.Name):return context[node.id]
        if isinstance(node,ast.Constant) and isinstance(node.value,int):return const(node.value)
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return neg(visit(node.operand))
        if isinstance(node,ast.BinOp):
            if isinstance(node.op,ast.Pow):
                if not isinstance(node.right,ast.Constant) or not isinstance(node.right.value,int):raise ValueError('Exponent')
                return power(visit(node.left),node.right.value)
            a,b=visit(node.left),visit(node.right)
            if isinstance(node.op,ast.Add):return add(a,b)
            if isinstance(node.op,ast.Sub):return add(a,neg(b))
            if isinstance(node.op,ast.Mult):return mul(a,b)
        raise ValueError('Non-polynomial expression')
    return visit(ast.parse(text,mode='eval').body)

# Written independently from the mathematical projection/reconstruction.
restoration={
 'N':'(beta*J+1)*(L+1)', 'P':'eta+zeta+E*(c-eta)',
 'X':'2*u**2','C2':'c**2','Delta':'a*a+4*a+3','V':'f*o-c',
 'Baux':'I**2','tau':'tau+E*(c-eta)','D':'D+a*c'}
restored=dict(env)
for name,formula in restoration.items():restored[name]=parse(formula,env)
deleted={1,6,9,10,15,19,22}
rows=[parse(x,env) for x in child['residuals']]
index=0;facts=[]
for j,expr in enumerate(parent['residuals']):
    old=parse(expr,restored)
    if j in deleted:
        if old:raise RuntimeError('Deleted row not identically zero '+str(j))
        facts.append({'old_row':j,'result':'identically zero'})
    else:
        difference=add(rows[index],neg(old))
        expected=parse('o**2*(F2-f**2)',env) if j==17 else {}
        if difference!=expected:raise RuntimeError('Restored residual mismatch '+str(j))
        facts.append({'old_row':j,'new_row':index,'correction':j==17})
        index+=1
if index!=19 or len(child['variables'])!=34:raise RuntimeError('Dimensions')
degrees=[max(sum(e[:34]) for e in row) for row in rows]
if max(degrees)!=3:raise RuntimeError('Residual degree')
sos={}
for row in rows:sos=add(sos,mul(row,row))
ex=[0]*n;ex[names.index('I')]=4;ex[names.index('g')]=2
if sos.get(tuple(ex))!=1:raise RuntimeError('Degree witness')
if max(sum(e[:34]) for e in sos)!=6:raise RuntimeError('Exact degree')
packet=json.loads((ROOT/'sextic34_expanded.json').read_text())
if packet['symbols']!=names:raise RuntimeError('Expansion symbol order')
supplied={tuple(t['exponents']):t['coefficient'] for t in packet['terms']}
if supplied!=sos:raise RuntimeError('Supplied full expansion differs')
live={names[i] for row in rows for m in row for i,e in enumerate(m) if e}
if live!=set(names):raise RuntimeError('Unused witness/coefficient')
receipt={'status':'PASS','method':'Independent AST parser and tuple-exponent sparse ring; no import of the source builder or its arithmetic implementation.',
 'parent_sha256':hashlib.sha256((ROOT/'upstream/quartic41.json').read_bytes()).hexdigest(),
 'child_sha256':hashlib.sha256((ROOT/'sextic34.json').read_bytes()).hexdigest(),
 'parent_variables':41,'child_variables':34,'deleted_definitions':7,'residuals':19,
 'residual_degrees':degrees,'expanded_terms':len(sos),'exact_degree':6,
 'selected_coefficient':{'monomial':'I^4*g^2','coefficient':1},
 'all_forward_row_identities':facts,
 'scope':'Local all-integer polynomial zero-set bijection and exact degree. Inherited Q41/native/Pell/ZFC calibration is not re-proved by these finite calculations.'}
(OUT/'SEXTIC34_INDEPENDENT_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='all_forward_row_identities'},indent=2))
