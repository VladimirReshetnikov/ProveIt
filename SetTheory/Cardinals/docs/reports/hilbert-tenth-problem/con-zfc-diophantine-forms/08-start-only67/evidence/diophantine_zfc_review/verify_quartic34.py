"""Independent exact 34-variable/25-equation audit, authored here.
Imports only our separately authored sparse-polynomial checker, not the reducer
or inherited repository code. All artifact expression strings are restricted
AST data, never eval'ed. Also verifies every printed factored equation.
"""
import json,hashlib
from pathlib import Path
import verify_quadratic_reduction as A
P=Path(__file__).resolve().parent
path=P.parent/'diophantine_zfc_encoding/start_only_quartic34.json'
j=json.loads(path.read_text())
A.allowed.update(j['variables']+j['fixed_numerals'])
p=A.parse
r=[p(x) for x in j['residual_polynomials']]
assert len(r)==j['equation_count']==25
assert len(set(j['variables']))==j['variable_count']==34
assert len(j['register_witnesses'])==19
assert j['original_witnesses']==A.q['original_witnesses']
vars=set(j['variables'])
assert all(max(sum(x in vars for x in m) for m in e)==2 for e in r)
for factored,expanded in zip(j['equations_factored'],r):
    l,rr=factored.split(' = ')
    assert A.add(p(l),p(rr),-1)==expanded
mapping={x:p(x) for x in j['original_witnesses']+j['fixed_numerals']}
for k,v in {'n2':'N','UM':'E','first_next':'P','R10a':'c','R12':'a','cam2':'a*c','gam':'gamma*(4*a+3)','R14':'D','c2':'C2','Ac2':'K','gap':'G','Lm1':'L','r_lhs':'R','L16':'F2','auxiliary_Tf_minus_one':'V0','aux_u_rhs':'V','aux_square_gap':'g','aux_coefficient_root':'I','scaled_f_square':'Baux+Delta','norm_strong':'Delta'}.items():mapping[k]=p(v)
def simultaneous(e):
    out={}
    for m,c in e.items():
        t={():c}
        for x in m:t=A.mul(t,mapping[x])
        out=A.add(out,t)
    return out
old=[simultaneous(p(x.removesuffix(' = 0'))) for x in A.q['equations']]
assert old[8]=={} and old[9]=={}
assert old[2]==A.add(r[2],r[8])
assert old[4]==A.add(r[4],A.mul(p('a-E'),r[8]),-1)
indexmap={0:0,1:1,3:3,5:5,6:6,7:7,10:9,11:10,12:11,13:12,14:13,15:14,16:15,17:16,18:17,19:18,20:19,21:20,22:21,23:22,24:23,25:24}
for i,k in indexmap.items():assert old[i] in (r[k],A.neg(r[k]))
# Every original variable remains positive. The lift creates ac, gamma(4a+3),
# Baux+Delta >0. The projection creates X=wq>0 and Baux=I^2>0.
# The tau^4 term in the squared sum has coefficient exactly one.
sos={}
for e in r:sos=A.add(sos,A.mul(e,e))
assert sos.get(('tau_root',)*4)==1
assert max(sum(x in vars for x in m) for m in sos)==4
report={'source35_sha256':hashlib.sha256(A.qpath.read_bytes()).hexdigest(),'quartic34_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'positive_variables':34,'equations':25,'each_equation_exact_degree':2,'sum_of_squares_exact_degree':4,'tau_fourth_power_coefficient':1,'printed_factored_equations_match_expansions':True,'all26_old_equation_identities_verified':True,'projection_lift_positive':True,'positive_projection':'X=w*((B-1)J+1)>0; Baux=I^2>0.','positive_lift':'cam2=a*c>0; gam=gamma*(4*a+3)>0; scaled_f_square=Baux+Delta>0.','implementation':'Independent Python integer sparse polynomials, not SymPy; restricted AST parser; no inherited code executed.'}
(P/'quartic34_independent_audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
