#!/usr/bin/env python3
"""Independent exact audit of Q42X, sextic35 and octic30; no builder imports."""
from pathlib import Path
import ast, hashlib, json, sys
ROOT=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent
def require(ok,msg):
    if not ok:raise ValueError(msg)
def read(path):return json.loads(path.read_text())
q42=read(ROOT.parent/'quartic42.json');parent=read(ROOT/'quartic42_x_square.json')
ports=parent['fixed_numerals'];names=parent['variables']+['tau_tail','q_half_root']+ports
require(len(names)==len(set(names)),'Unique names')
idx={name:i for i,name in enumerate(names)};zero=(0,)*len(names)
def lit(c):return {zero:c} if c else {}
def var(name):return {tuple(int(i==idx[name]) for i in range(len(names))):1}
def add(a,b,sign=1):
    z=dict(a)
    for m,c in b.items():
        z[m]=z.get(m,0)+sign*c
        if not z[m]:del z[m]
    return z
def scale(a,c):return {m:c*v for m,v in a.items() if c*v}
def mul(a,b):
    z={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(x+y for x,y in zip(m,n));z[key]=z.get(key,0)+c*d
    return {m:c for m,c in z.items() if c}
def power(a,n):
    z=lit(1)
    for _ in range(n):z=mul(z,a)
    return z
def parse(expr):
    def rec(t):
        if isinstance(t,ast.Constant) and type(t.value) is int:return lit(t.value)
        if isinstance(t,ast.Name):require(t.id in idx,'Known formal symbol');return var(t.id)
        if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return scale(rec(t.operand),-1)
        require(isinstance(t,ast.BinOp),'Polynomial AST')
        if isinstance(t.op,ast.Pow):
            require(isinstance(t.right,ast.Constant) and type(t.right.value) is int and 0<=t.right.value<=8,'Fixed small power')
            return power(rec(t.left),t.right.value)
        a,b=rec(t.left),rec(t.right)
        if isinstance(t.op,ast.Add):return add(a,b)
        if isinstance(t.op,ast.Sub):return add(a,b,-1)
        require(isinstance(t.op,ast.Mult),'Only polynomial arithmetic');return mul(a,b)
    return rec(ast.parse(expr,mode='eval').body)
def subst(poly,mapping):
    out={};cache={}
    for mon,c in poly.items():
        term=lit(c)
        for i,e in enumerate(mon):
            if not e:continue
            key=(i,e)
            if key not in cache:cache[key]=power(mapping.get(names[i],var(names[i])),e)
            term=mul(term,cache[key])
        out=add(out,term)
    return out
def used(poly):return {names[i] for m in poly for i,e in enumerate(m) if e}
def degree(poly):return max((sum(e for i,e in enumerate(m) if names[i] not in ports) for m in poly),default=-1)

original=[parse(s) for s in q42['residuals']];base=[parse(s) for s in parent['residuals']]
changes=[i for i,(a,b) in enumerate(zip(original,base)) if a!=b]
require(len(changes)==1,'Exactly one square guard changed')
guard=changes[0]
require(original[guard]==parse('beta*J+1-2*q_half_root**2'),'Original square guard')
require(base[guard]==parse('X-8*rho**2'),'Relocated square guard')
require(parent['source_sha256']==hashlib.sha256((ROOT.parent/'quartic42.json').read_bytes()).hexdigest(),'Parent pin')
receipts=[]
for filename,nvar,neq,dmax,mon,coef in [
    ('sextic35.json',35,20,3,{'r':2,'c':4},4),
    ('octic30.json',30,15,4,{'a':4,'f':4},1)]:
    child=read(ROOT/filename);rows=list(base);rest={n:var(n) for n in parent['variables']};remaining=set(parent['variables'])
    if filename=='sextic35.json':
        change={'tau':parse('tau_tail+P-eta-zeta')}
        rows=[subst(p,change) for p in rows];rest={n:subst(p,change) for n,p in rest.items()}
        remaining.remove('tau');remaining.add('tau_tail')
    for step in child['eliminations']:
        name=step['variable'];f=parse(step['restoration']);r=step['row_before_elimination']-1;sign=step['row_sign']
        require(name in remaining and name not in used(f),'Valid monic elimination variable')
        require(used(f)<=((remaining-{name})|set(ports)),'Triangular restoration')
        require(sign in (-1,1) and rows[r]==scale(add(var(name),f,-1),sign),'Exact monic defining residual')
        rows=[subst(p,{name:f}) for i,p in enumerate(rows) if i!=r]
        rest={n:subst(p,{name:f}) for n,p in rest.items()};remaining.remove(name)
    finals=[parse(s) for s in child['residuals']]
    require(rows==finals,'Exact sequential elimination output')
    require(remaining==set(child['variables']) and len(remaining)==nvar,'Variable count')
    require(len(finals)==neq and max(map(degree,finals))==dmax,'Residual count and degree')
    require(child['fixed_numerals']==ports,'Unchanged fixed ports')
    require(set(child['full_parent_restorations'])==set(rest),'Complete restoration domain')
    require(all(parse(child['full_parent_restorations'][n])==p for n,p in rest.items()),'Exact composed restoration')
    mapping=child['parent_residual_maps_to_child_row_or_zero']
    require(len(mapping)==27 and sorted(x for x in mapping if x)==list(range(1,neq+1)),'One-to-one row map')
    for p,m in zip(base,mapping):
        require(subst(p,rest)==(finals[m-1] if m else {}),'Full parent residual restoration')
    total={}
    for p in finals:total=add(total,mul(p,p))
    expanded=read(ROOT/filename.replace('.json','_expanded.json'))
    archived={}
    for coefficient,monomial in expanded['terms']:
        key=[0]*len(names)
        for name,exponent in monomial:key[idx[name]]=exponent
        key=tuple(key);require(key not in archived,'Unique archived monomial');archived[key]=coefficient
    require(archived==total,'Complete archived sum-of-squares expansion')
    target=tuple(mon.get(n,0) for n in names)
    cert={m[-4:]:c for m,c in total.items() if m[:-4]==target[:-4]}
    require(cert=={(0,0,0,0):coef},'Fixed-slice exact coefficient')
    require(degree(total)==2*dmax,'Exact sum-of-squares degree')
    require(set().union(*(used(p) for p in finals))-set(ports)==remaining,'All witnesses used')
    for key in ('manifest','compiler_manifest','transfer_proof'):
        require((ROOT/child['coefficient_binding'][key]).resolve()==(ROOT.parent/q42['coefficient_binding'][key]).resolve(),'Same complete coefficient binding')
    receipts.append({'packet':filename,'variables':nvar,'residuals':neq,'eliminations':len(child['eliminations']),
        'maximum_residual_degree':dmax,'exact_degree':2*dmax,'monomial':mon,'coefficient':coef,
        'parent_restoration_identities':27,'expanded_SOS_terms':len(total),
        'sha256':hashlib.sha256((ROOT/filename).read_bytes()).hexdigest()})
receipt={'status':'PASS','builder_imports':False,'single_guard_change_row':guard+1,'companions':receipts,
 'scope':'Exact monic eliminations, composed restoration, dimensions and degree. Square-guard divisibility proof reviewed separately.'}
out=ROOT/'INDEPENDENT_CHECK.json';out.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
