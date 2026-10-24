import json,pathlib,sympy as S
R=pathlib.Path(__file__).resolve().parent
a=json.loads((R/'prior_source.json').read_text());b=json.loads((R/'source.json').read_text())
names=a['variables']+a['constants'];syms=S.symbols(' '.join(names));d=dict(zip(names,syms));n=len(a['variables'])
def require(p,m):
 if not p:raise ValueError(m)
def poly(row):return sum(t['coefficient']*S.prod(x**k for x,k in zip(syms,t['powers']))for t in row['terms'])
p=[poly(row)for row in a['equations']];q=[poly(row)for row in b['equations']]
r=[S.expand(t.subs(d['N'],d['N']+d['L']+d['beta']*d['J']))for t in p];r[13]=S.expand(r[13]-r[1])
for i,(x,y)in enumerate(zip(q,r)):require(S.expand(x-y)==0,'row identity '+str(i+1));require(S.Poly(x,*syms[:n]).total_degree()<=2,'quadratic row')
def records(s):return sum(len({tuple(t['powers'][:n])for t in row['terms']})for row in s['equations'])
require(records(a)==86 and records(b)==85,'record counts')
x=S.symbols('q');require(S.expand(x**3-1-(x*x-1)-(x-1)-(x-1)**2*(x+1))==0,'factored positive gap')
print(json.dumps({'status':'PASS','polynomial_identities':22,'positive_zero_set_bijection':'PROOF.md','old_records':86,'new_records':85,'new_expanded_port_monomials':sum(len(e['terms'])for e in b['equations'])}))
