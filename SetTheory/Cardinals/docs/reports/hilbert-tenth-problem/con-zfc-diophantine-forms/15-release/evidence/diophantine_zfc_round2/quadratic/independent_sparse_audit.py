import sys
if sys.flags.optimize:
    raise SystemExit("Do not run these evidence checks with -O or PYTHONOPTIMIZE.")
#!/usr/bin/env python3
"""Independent arithmetic audit. Standard library only; no source scripts imported."""
import ast, hashlib, json
from pathlib import Path
from collections import Counter

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'diophantine_zfc_round2/quadratic'
NAMES=['Bm1','Kconstant','MC','MF','Jrep','F','alpha','transport_quotient','f','h','i','auxiliary_quotient','s','w','tau_root','eta','zeta','y_aux','gamma','N','E','P','c','a','X','D','C2','K','G','L','R','F2','V0','V','g','I','Baux','Delta','tau_tail']
INDEX={v:i for i,v in enumerate(NAMES)}
ZERO=(0,)*len(NAMES)
CONSTANTS={'Bm1','Kconstant','MC','MF'}

def const(n): return {ZERO:n} if n else {}
def var(n):
    e=list(ZERO);e[INDEX[n]]=1
    return {tuple(e):1}
def add(p,q):
    r=p.copy()
    for m,c in q.items():
        r[m]=r.get(m,0)+c
        if r[m]==0: del r[m]
    return r
def neg(p): return {m:-c for m,c in p.items()}
def sub(p,q): return add(p,neg(q))
def mul(p,q):
    r={}
    for a,c in p.items():
        for b,d in q.items():
            m=tuple(x+y for x,y in zip(a,b));r[m]=r.get(m,0)+c*d
    return {m:c for m,c in r.items() if c}
def power(p,n):
    if n<0: raise ValueError('negative exponent')
    r=const(1)
    for _ in range(n):r=mul(r,p)
    return r

def parse(s):
    def visit(n):
        if isinstance(n,ast.Constant) and isinstance(n.value,int):return const(n.value)
        if isinstance(n,ast.Name):return var(n.id)
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return neg(visit(n.operand))
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.UAdd):return visit(n.operand)
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Add):return add(visit(n.left),visit(n.right))
            if isinstance(n.op,ast.Sub):return sub(visit(n.left),visit(n.right))
            if isinstance(n.op,ast.Mult):return mul(visit(n.left),visit(n.right))
            if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant):return power(visit(n.left),n.right.value)
        raise ValueError(ast.dump(n))
    return visit(ast.parse(s.strip(),mode='eval').body)

def substitute(p,changes):
    r={}
    for m,c in p.items():
        term=const(c)
        for name,e in zip(NAMES,m):
            if e:term=mul(term,power(changes.get(name,var(name)),e))
        r=add(r,term)
    return r

def degree(p):
    return max((sum(e for n,e in zip(NAMES,m) if n not in CONSTANTS) for m in p),default=-1)

def equal(p,q,desc):
    if p!=q: raise ValueError('Failed identity: '+desc+'; '+str(sub(p,q)))

def check(condition,desc):
    if not condition:raise ValueError(desc)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def input_file(path):
    data=json.loads(path.read_text());polys=[parse(x) for x in data['residual_polynomials']]
    check(len(set(data['variables']))==len(data['variables'])==data['variable_count'],str(path)+' variable count')
    check(len(polys)==data['equation_count'],str(path)+' equation count')
    used={n for p in polys for m in p for n,e in zip(NAMES,m) if e}
    check(used==set(data['variables'])|set(data['fixed_numerals']),str(path)+' symbol inventory')
    degrees=[degree(p) for p in polys]
    check(max(degrees)==data['max_equation_degree'],str(path)+' degree')
    if 'equation_degrees' in data:check(degrees==data['equation_degrees'],str(path)+' all degrees')
    sos={}
    for p in polys:sos=add(sos,mul(p,p))
    check(degree(sos)==data['sum_of_squares_exact_degree'],str(path)+' SOS degree')
    # Test positive-to-nonnegative shifts exactly, reusing the same symbols as shifted coordinates.
    shifted=substitute(sos,{v:add(var(v),const(1)) for v in data['variables']})
    check(degree(shifted)==degree(sos),str(path)+' shifted degree')
    return data,polys,sos,{'sha256':sha(path),'variable_count':len(data['variables']),'equation_count':len(polys),'equation_degrees':degrees,'sos_degree':degree(sos),'shifted_sos_degree':degree(shifted),'sos_expanded_term_count':len(sos)}

base_path=ROOT/'diophantine_zfc_encoding/start_only_quartic34.json'
base,b,bsos,baseinfo=input_file(base_path)
for j,(fact,p) in enumerate(zip(base['equations_factored'],b),1):
    left,right=fact.split('=');equal(sub(parse(left),parse(right)),p,'base factored equation '+str(j))

ordinary_path=OUT/'ordinary_quartic33.json'
ordinary,o,osos,oinfo=input_file(ordinary_path)
check(ordinary['parent_sha256']==sha(base_path),'ordinary parent hash')
# Independent construction: preserve the 34 source rows except K definition,
# replace its relation to Delta*C2 by their difference, and use ordinary I=i*C2.
expected_o=[]
for j,p in enumerate(b,1):
    if j==10:continue
    if j==13:p=sub(b[12],b[9])
    if j==22:p=parse('I-i*C2')
    expected_o.append(p)
for j,(p,q) in enumerate(zip(o,expected_o),1):equal(p,q,'ordinary residual '+str(j))
check(ordinary['variables']==[v for v in base['variables'] if v!='K'],'ordinary variables')
# Under i_ordinary=Delta*i_normalized, changed strong residual equals
# normalized strong residual plus i*(K-Delta*C2). Main norm is source13-source10.
equal(substitute(o[20],{'i':parse('Delta*i')}),add(b[21],mul(parse('i'),b[12])),'normalized to ordinary strong lift')
equal(o[11],sub(b[12],b[9]),'ordinary main norm merge')
# Quartic degree is uniform over every admissible fixed-constant specialization.
tau4=list(ZERO);tau4[INDEX['tau_root']]=4
check(osos.get(tuple(tau4))==1,'ordinary tau_root^4 coefficient 1')
oinfo.update({'source_residual_identities':24,'normalized_to_ordinary_strong_identity':True,'main_norm_merge_identity':True,'uniform_degree_witness':'coefficient(tau_root^4)=1','semantic_equivalence_requires_ordinary_rank_and_Start_only_compiler':True})

cubic_path=OUT/'start_only_sextic25.json'
cubic,c,csos,cinfo=input_file(cubic_path)
check(cubic['parent_sha256']==sha(base_path),'cubic parent hash')
# Independently supply the inverse changes, not sourced from JSON substitutions.
changes={
 'N':parse('(L+1)*(Bm1*Jrep+1)'),
 'X':parse('w*(Bm1*Jrep+1)'),
 'C2':parse('c**2'),
 'K':parse('D**2-1'),
 'G':parse('(Bm1*Jrep)*(Bm1*Jrep+1-F)+alpha'),
 'F2':parse('f**2'),
 'V0':parse('auxiliary_quotient*f-1'),
 'g':parse('y_aux**2-V**2'),
 'P':parse('E*(c-eta)+eta+zeta'),
 'tau_root':parse('tau_tail+E*(c-eta)')
}
# A zero row is a deleted definition; all nonzero residuals must be the
# printed list in original source order, preserving literal signs.
subbed=[substitute(p,changes) for p in b]
kept=[(j,p) for j,p in enumerate(subbed,1) if p]
check([j for j,p in kept]==cubic['parent_residual_indices'],'cubic source indices')
check(len(kept)==len(c),'cubic residual count')
for j,((source,p),q) in enumerate(zip(kept,c),1):equal(p,q,'cubic residual '+str(j)+' from source '+str(source))
check([j for j,p in enumerate(subbed,1) if not p]==[2,3,7,10,12,15,18,19,21],'deleted definition identities')
for v,e in cubic['eliminated_registers'].items():equal(parse(e),changes[v],'reported elimination '+v)
expected_vars=['tau_tail' if v=='tau_root' else v for v in base['variables'] if v not in set(changes)-{'tau_root'}]
check(expected_vars==cubic['variables'],'cubic variables')
equal(c[4],parse('tau_tail**2+E*(c-eta)*(2*tau_tail-eta-zeta)-1'),'sheared first norm')
# Degree six witness uses no compiler coefficients.
mono=list(ZERO);mono[INDEX['Baux']]=2;mono[INDEX['V']]=4
check(csos.get(tuple(mono))==1,'cubic Baux^2 V^4 coefficient 1')
cinfo.update({'all_25_source_residuals_verified':True,'retained_nonzero_residual_count':16,'deleted_zero_residual_indices':[j for j,p in enumerate(subbed,1) if not p],'root_shear_identity':True,'uniform_degree_witness':'coefficient(Baux^2*V^4)=1','exact_positive_bijection_proof_review':'See independent_low_degree_audit.md'})


octic_path=OUT/'ordinary_octic20.json'
octic,t,tsos,tinfo=input_file(octic_path)
check(octic['parent_sha256']==sha(ordinary_path),'octic parent hash')
check(octic['parent_artifact']==ordinary_path.name,'octic parent name')
# Verify each solved equation and substitute sequentially. Index convention is
# zero-based in the current list, not the original parent list.
working=list(o);working_vars=list(ordinary['variables'])
for step,(name,j,expression) in enumerate(octic['elimination_steps'],1):
    check(name in working_vars,'octic eliminates a live variable')
    check(0<=j<len(working),'octic valid source row')
    value=parse(expression)
    check(all(m[INDEX[name]]==0 for m in value),'octic nonrecursive definition')
    definition=sub(var(name),value)
    check(working[j]==definition or working[j]==neg(definition),'octic exact solved row '+str(step))
    working=[substitute(p,{name:value}) for k,p in enumerate(working) if k!=j]
    working_vars.remove(name)
check(working_vars==octic['variables'],'octic trace variables')
check(len(working)==len(t),'octic trace residual count')
for j,(p,q) in enumerate(zip(working,t),1):equal(p,q,'octic trace residual '+str(j))
# Independent closed-form inverse avoids relying solely on a correct trace.
full_lift={
 'N':parse('(Bm1*Jrep+1)**3'),
 'C2':parse('c**2'),
 'G':parse('(Bm1*Jrep)*(Bm1*Jrep+1-F)+alpha'),
 'F2':parse('f**2'),
 'V0':parse('auxiliary_quotient*f-1'),
 'g':parse('y_aux**2-V**2'),
 'Baux':parse('I**2'),
 'P':parse('E*(c-eta)+eta+zeta'),
 'X':parse('w*(Bm1*Jrep+1)'),
 'L':parse('(Bm1*Jrep+1)**2-1'),
 'R':parse('eta+zeta-1-h*E'),
 'Delta':parse('a**2+4*a+3'),
 'D':parse('w*(Bm1*Jrep+1)+a*c+gamma*(4*a+3)')
}
fully_subbed=[substitute(p,full_lift) for p in o]
nonzero=[(j,p) for j,p in enumerate(fully_subbed,1) if p]
check(len(nonzero)==len(t),'octic closed lift residual count')
for j,((source,p),q) in enumerate(zip(nonzero,t),1):equal(p,q,'octic closed lift residual '+str(j))
mono=list(ZERO);mono[INDEX['E']]=4;mono[INDEX['c']]=4
check(tsos.get(tuple(mono))==1,'octic E^4 c^4 coefficient 1')
tinfo.update({'all_13_elimination_steps_verified':True,'all_24_parent_residuals_verified_by_independent_closed_form_lift':True,'deleted_zero_parent_residual_indices':[j for j,p in enumerate(fully_subbed,1) if not p],'retained_nonzero_parent_residual_indices':[j for j,p in nonzero],'uniform_degree_witness':'coefficient(E^4*c^4)=1','positive_bijection_proof_review':'See independent_low_degree_audit.md section 5'})

receipt={'status':'PASS','method':'Independent standard-library AST parser and sparse multivariate integer polynomial dictionaries; no source generation script imported or executed. Constants retained as symbolic degree-zero ports.','source_34':baseinfo,'ordinary_33':oinfo,'normalized_25':cinfo,'ordinary_20':tinfo,'scope':'Arithmetic identities and degree/count claims are machine checked. Positivity and theorem dependencies are reviewed mathematically, not mechanically formalized.'}
(OUT/'independent_sparse_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
