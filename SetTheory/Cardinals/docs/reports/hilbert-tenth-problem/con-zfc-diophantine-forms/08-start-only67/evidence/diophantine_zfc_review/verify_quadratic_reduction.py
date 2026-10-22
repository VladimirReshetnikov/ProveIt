"""Independent exact sparse-polynomial audit, authored for this deliverable.
Uses Python AST as a restricted data parser, never eval, SymPy, repository code,
or the separate worker's reducer. Replays and verifies each elimination.
"""
import ast,json,hashlib
from pathlib import Path
from collections import Counter
P=Path(__file__).resolve().parent
srcpath=P/'start_only_system61.json'
qpath=P.parent/'diophantine_zfc_encoding/noinput_quadratic_reduced.json'
src=json.loads(srcpath.read_text());q=json.loads(qpath.read_text())
def tidy(a):return {m:c for m,c in a.items() if c}
def add(a,b,s=1):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,0)+s*c
    return tidy(r)
def mul(a,b):
    r={}
    for m,c in a.items():
        for n,d in b.items():
            t=tuple(sorted(m+n));r[t]=r.get(t,0)+c*d
    return tidy(r)
def neg(a):return {m:-c for m,c in a.items()}
def power(a,n):
    r={():1}
    for _ in range(n):r=mul(r,a)
    return r
def term(x):return {():x} if type(x) is int and x else {} if x==0 else {(x,):1}
allowed=set(src['witnesses']+src['fixed_numerals']+[r[0] for r in src['source']])
def parse(expr):
    def visit(n):
        if isinstance(n,ast.Name):
            assert n.id in allowed
            return term(n.id)
        if isinstance(n,ast.Constant):
            assert type(n.value) is int
            return term(n.value)
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return neg(visit(n.operand))
        assert isinstance(n,ast.BinOp)
        if isinstance(n.op,ast.Add):return add(visit(n.left),visit(n.right))
        if isinstance(n.op,ast.Sub):return add(visit(n.left),visit(n.right),-1)
        if isinstance(n.op,ast.Mult):return mul(visit(n.left),visit(n.right))
        if isinstance(n.op,ast.Pow):
            assert isinstance(n.right,ast.Constant) and type(n.right.value) is int and 0<=n.right.value<=4
            return power(visit(n.left),n.right.value)
        raise AssertionError(n)
    return visit(ast.parse(expr,mode='eval').body)
def substitute(p,var,rhs):
    out={}
    for m,c in p.items():
        count=m.count(var);rem=tuple(x for x in m if x!=var)
        out=add(out,mul({rem:c},power(rhs,count)))
    return out
def fingerprint(p):return tuple(sorted(p.items()))
rows=[list(r) for r in src['source']]
for r in rows:
    if r[0]=='aux_square_gap':r[:]=['aux_square_gap','-','aux_y2','H2']
    if r[0]=='norm_aux':r[:]=['norm_aux','-','aux_y2','L17']
eq=[]
for out,op,a,b in rows:
    rhs=mul(term(a),term(b)) if op=='*' else add(term(a),term(b),1 if op=='+' else -1)
    eq.append(add(term(out),rhs,-1))
for a,b in src['comparisons']:eq.append(add(term(a),term(b),-1))
assert len(eq)==67
variables=set(src['witnesses']+[r[0] for r in rows])
log=[]
for step in q['eliminations']:
    var=step['variable'];rhs=parse(step['value'])
    assert var in variables and var not in src['witnesses']
    assert all(var not in m for m in rhs)
    proof=add(term(var),rhs,-1)
    hits=[i for i,e in enumerate(eq) if e==proof or e==neg(proof)]
    assert hits,(var,'No defining equation of coefficient +/-1')
    hit=hits[0];variables.remove(var)
    eq=[substitute(e,var,rhs) for i,e in enumerate(eq) if i!=hit]
    maxdeg=max(sum(v in variables for v in m) for e in eq for m in e)
    assert maxdeg<=2,(var,maxdeg)
    log.append({'eliminated':var,'degree_bound_after':maxdeg})
assert Counter(map(fingerprint,eq))==Counter(fingerprint(parse(s.removesuffix(' = 0'))) for s in q['equations'])
assert variables==set(q['variables'])
assert len(variables)==q['variable_count']==35
assert len(eq)==q['equation_count']==26
assert len(q['register_witnesses'])==20
assert set(q['original_witnesses'])==set(src['witnesses'])
assert all(max(sum(v in variables for v in m) for m in e)==2 for e in eq)
report={'source_sha256':hashlib.sha256(srcpath.read_bytes()).hexdigest(),'reduced_sha256':hashlib.sha256(qpath.read_bytes()).hexdigest(),'variable_count':35,'equation_count':26,'retained_positive_registers':20,'exact_equation_degrees':[2]*26,'sum_of_squares_degree':4,'exact_defining_equation_substitutions_verified':len(log),'independent_implementation':'Python integer sparse polynomials; restricted AST data parser; no eval, SymPy, or worker-script imports.','positivity_status':'Retained gate positivity uses the separate source-kernel proof, not this algebraic checker.'}
(P/'quadratic_reduction_independent_audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
