from pathlib import Path
import sympy as s,json,hashlib
R=Path(__file__).resolve().parents[2]; G=R/'guards';O=Path(__file__).parent
old=R/'sources/con-zfc-structural-reductions-2026-10-23/con-zfc-structural-reductions/integer41/quartic41.json'
a=json.loads(old.read_text());b=json.loads((G/'signed40_sextic.json').read_text());c=json.loads((G/'signed34_sextic.json').read_text())
sy={n:s.Symbol(n) for n in set(a['variables']+b['variables']+c['variables']+a['fixed_numerals'])};q=sy['beta']*sy['J']+1
parse=lambda rows:[s.sympify(e,locals=sy) for e in rows]
need=lambda cond: cond or (_ for _ in ()).throw(ValueError('Independent identity failed'))
ra=parse(a['residuals']); rb=parse(b['residuals']); rc=parse(c['residuals']); X,u,F,alpha,Z,K0=[sy[x] for x in ['X','u','F','alpha','Z','K0']]
# Locate modifications by their formulas, rather than trusting builder row numbers.
oldscale=X-4*q*sy['w_scale']; oldsquare=X-2*u*u
scale=next(i for i,e in enumerate(ra) if s.expand(e-oldscale)==0)
square=next(i for i,e in enumerate(ra) if s.expand(e-oldsquare)==0)
transport=next(i for i,e in enumerate(ra) if e.has(sy['z']))
newtransport=(K0*q+X)*(q-F-alpha)-q*F-Z*(q-1)
expected=[s.expand(newtransport if i==transport else X-4*q*u*u if i==square else e) for i,e in enumerate(ra) if i!=scale]
need(len(expected)==len(rb)==25);need(all(s.expand(x-y)==0 for x,y in zip(expected,rb)))
# q times old transport equals new transport after w_scale=u² and Z=qz,
# modulo the new X guard.
rem=s.expand(newtransport.subs(Z,q*sy['z'])-q*ra[transport].subs(sy['w_scale'],u*u))
need(s.rem(rem,X-4*q*u*u,X)==0)
rest=json.loads((G/'SEXTIC_RESTORATION.json').read_text());sub={sy[k]:s.sympify(v,locals=sy) for k,v in rest.items() if k!='tau_old'}
sub[sy['tau']]=s.sympify(rest['tau_old'],locals=sy)
rr=[s.expand(e.subs(sub,simultaneous=True)) for e in rb]; rr=[e for e in rr if e!=0]
need(len(rr)==len(rc)==19);need(all(s.expand(x-y)==0 for x,y in zip(rr,rc)))
vs=[sy[x] for x in c['variables']];need(len(vs)==len(set(vs))==34)
need(all(s.Poly(e,*vs).total_degree()<=3 for e in rc)); pol=s.Poly(s.expand(sum(e*e for e in rc)),*vs); mon=sy['r']**2*sy['c']**4;need(pol.coeff_monomial(mon)==4);need(pol.total_degree()==6)
# Universal positive-coefficient growth certificate after x=64+v,z=5+w.
v,w=s.symbols('v w',nonnegative=True); x,z=s.symbols('x z');gap=(2*(x-1)*z-5)**2-(x-3)*(4*x*z*z-2)
pg=s.Poly(s.expand(gap.subs({x:v+64,z:w+5})),v,w);need(all(t>0 for t in pg.coeffs()))
files=[old,G/'PROOF.md',G/'signed40_sextic.json',G/'signed34_sextic.json',G/'SEXTIC_RESTORATION.json']
receipt={'status':'PASS','independent_graph_transport_and_six_eliminations':True,'variables':34,'residuals':19,'exact_degree':6,'degree_witness':'coefficient r^2*c^4 = 4','negative_X_base_gap_positive_coefficients':str(pg.as_expr()),'hashes':{str(f.relative_to(R)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files},'scope':'Exact symbolic checks and a universal polynomial positivity certificate. Unbounded Pell/compiler dependencies separately reviewed mathematically; no kernel certificate.'}
(O/'CHECK.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
