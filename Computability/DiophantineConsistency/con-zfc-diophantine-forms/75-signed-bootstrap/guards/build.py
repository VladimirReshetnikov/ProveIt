import json, pathlib, sympy as s
out=pathlib.Path(__file__).resolve().parent
def require(ok, message):
 if not ok: raise RuntimeError(message)
src=out/'upstream/q41/quartic41.json'
d=json.loads(src.read_text()); names=d['variables']+d['fixed_numerals']; sy=dict(zip(names,s.symbols(' '.join(names)))); sy['Z']=s.Symbol('Z'); q=sy['beta']*sy['J']+1
binding=json.loads(json.dumps(d['coefficient_binding']))
binding['ports']={k:'upstream/q41/'+v for k,v in binding['ports'].items()}
binding['inherited_manifest']='upstream/q41/'+binding['inherited_manifest']
binding['path_base']='directory containing this polynomial JSON'
rs=[s.sympify(x,locals=sy) for x in d['residuals']]; X,u,F,alpha,Z,K0=[sy[x] for x in ['X','u','F','alpha','Z','K0']]
rs[13]=(K0*q+X)*(q-F-alpha)-q*F-Z*(q-1)
rs[22]=X-4*q*u*u
rs.pop(2)
vs=[sy[x] for x in d['variables'] if x not in ('w_scale','z')]+[Z]
def pack(label,rows,vs):
 deg=[s.Poly(s.expand(e),*vs).total_degree() for e in rows]
 result={'name':label,'domain':'unrestricted integers','variables':[str(v) for v in vs],'variable_count':len(vs),'fixed_numerals':d['fixed_numerals'],'residuals':[str(s.expand(e)) for e in rows],'residual_degrees':deg,'equation_count':len(rows),'exact_degree':2*max(deg),'single_polynomial':'sum of squares of residuals','coefficient_binding':binding}
 (out/(label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(label,len(vs),len(rows),deg)
pack('signed40_sextic',rs,vs)
# Shift first Pell root before eliminating P.
rs6=[s.expand(e.subs(sy['tau'],sy['tau']+sy['P']-sy['eta']-sy['zeta'])) for e in rs]
repl6={sy['P']:sy['eta']+sy['zeta']+sy['E']*(sy['c']-sy['eta']),sy['F2']:sy['f']**2,sy['g']:sy['y']**2-sy['V']**2,sy['N']:q*(sy['L']+1),sy['C2']:sy['c']**2,sy['X']:sy['D']-sy['a']*sy['c']-sy['gamma']*(4*sy['a']+3)}
rr6=[s.expand(e.subs(repl6,simultaneous=True)) for e in rs6]
rr6=[e for e in rr6 if e!=0]; vv6=[v for v in vs if v not in repl6]
pack('signed34_sextic',rr6,vv6)
restoration6={str(k):str(s.expand(v)) for k,v in repl6.items()}
restoration6['tau_old']='tau+E*(c-eta)'
(out/'SEXTIC_RESTORATION.json').write_text(json.dumps(restoration6,indent=2)+'\n')
require(len(vv6)==34 and len(rr6)==19, 'sextic dimension')
require(max(s.Poly(e,*vv6).total_degree() for e in rr6)==3, 'sextic degree')
E,a,c,eta,V,j,h,I,f,y,gamma=[sy[x] for x in ['E','a','c','eta','V','j','h','I','f','y','gamma']]
k=1-V+j*c+h*E; B=E*(c-eta)
repl={sy['L']:q*q-1,sy['N']:q**3,sy['C2']:c*c,sy['F2']:f*f,sy['g']:y*y-V*V,sy['Baux']:I*I,sy['D']:X+a*c+gamma*(4*a+3),sy['Delta']:a*a+4*a+3,sy['P']:k+B,sy['zeta']:k-eta}
rr=[s.expand(e.subs(repl,simultaneous=True)) for e in rs]
rr=[e for e in rr if e!=0]; vv=[v for v in vs if v not in repl]
pack('absorbed30_octic',rr,vv)
require(len(vv)==30 and len(rr)==15, 'octic dimension')
require(max(s.Poly(e,*vv).total_degree() for e in rr)==4, 'octic degree')

(out/'CHECK.json').write_text(json.dumps({'algebra_verified':True,'new_sextic_variables':34,'new_sextic_residuals':19,'new_sextic_degree':6,'proof_status':'Independently reviewed ordinary mathematical proof relative to stated inherited results; not kernel checked.'},indent=2)+'\n')
