"""Independent read-only validation of the saved HF/EFQ constructor DAG."""
from pathlib import Path
import json,hashlib,collections
P=Path('/tmp/k218-hf-efq')
OUT=Path(__file__).parent
repo=Path('/home/codex/.codex/worktrees/ec20/Proofs')
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
T=('T',)
def atom(k,a,b):return(k,a,b)
def imp(a,b):return T if a==b==T else('I',a,b)
def v(n):return('v',n)
F=atom('R',T,T)
def neg(a):return imp(a,F)
def qall(a,b):return atom('Q',a,b)
def req(a,b):return atom('E',a,b)
def rel(a,b):return atom('R',a,b)
def ex(a,b):return neg(qall(a,neg(b)))
a,b,c=map(v,range(3))
axioms={'truth':T,'EFQ':imp(F,a),'restricted_rho8_F':imp(imp(neg(c),a),imp(imp(a,c),imp(b,c))),'rho1':ex(a,req(a,b)),'rho2':imp(qall(a,imp(b,c)),imp(qall(a,b),qall(a,c))),'rho3':imp(req(a,b),imp(rel(c,a),rel(c,b))),'rho4':imp(qall(a,qall(b,c)),qall(b,qall(a,c))),'rho5':imp(req(c,a),imp(rel(c,b),rel(a,b))),'rho6':imp(ex(a,qall(a,b)),b),'G':imp(req(c,a),imp(req(c,b),qall(rel(a,b),req(a,b))))}
def variables(t):
 if t[0]=='v':assert isinstance(t[1],int)and t[1]>=0;return{t[1]}
 if t==T:return set()
 assert len(t)==3 and t[0]in('I','Q','R','E')
 return variables(t[1])|variables(t[2])
def size(t):return 1 if len(t)!=3 else 1+size(t[1])+size(t[2])
def rename(t,off):
 if t[0]=='v':return v(t[1]+off)
 if len(t)==3:return(t[0],rename(t[1],off),rename(t[2],off))
 return t
def normal(t,env,seen=frozenset()):
 if t[0]=='v'and t[1]in env:
  assert t[1]not in seen
  return normal(env[t[1]],env,seen|{t[1]})
 if len(t)==3:
  l,r=normal(t[1],env,seen),normal(t[2],env,seen)
  return imp(l,r)if t[0]=='I'else(t[0],l,r)
 return t
def canonical(t):
 names={}
 def rec(z):
  if z[0]=='v':return v(names.setdefault(z[1],len(names)))
  if len(z)==3:return(z[0],rec(z[1]),rec(z[2]))
  return z
 return rec(t)
rows=json.loads((P/'modal-proof.json').read_text());forms=[];counts=collections.Counter()
for i,row in enumerate(rows):
 f=tup(row['formula']);vs=variables(f);assert size(f)<=55
 assert not vs or max(vs)<999
 rule=row['rule'];counts[rule]+=1
 if rule in axioms:assert f==axioms[rule]
 elif rule=='gen':
  j=row['parent'];assert 0<=j<i
  label=tup(row['label']);assert label==v(999)and999not in variables(forms[j])
  assert f==canonical(qall(label,forms[j]))
 else:
  assert rule=='condensed_mp'
  j,k=row['major'],row['minor'];assert 0<=j<i and0<=k<i
  assert row['minor_rename_offset']==1000
  minor0=rename(forms[k],1000);assert variables(forms[j]).isdisjoint(variables(minor0))
  env={int(k):tup(z)for k,z in row['substitution'].items()}
  major=normal(forms[j],env);minor=normal(minor0,env)
  assert major==tup(row['instantiated_major'])and minor==tup(row['instantiated_minor'])
  if major==T:assert minor==T and f==T
  else:assert major[0]=='I'and major[1]==minor and f==canonical(major[2])
 forms.append(f)
res=json.loads((P/'modal-result.json').read_text());val=json.loads((P/'validation.json').read_text())
assert len(forms)==res['nodes']==val['derivations']['modal']['nodes']==1699
assert res['processed']==1120 and res['pairs']==1554830 and res['found']=={}
assert (res['max_nodes'],res['max_term_size'],res['seconds_cap'])==(2500,55,15)
# Check the recorded explicit seven-node derivation without executing author code.
z=qall(a,neg(qall(a,F)))
expected=[neg(neg(z)),imp(neg(neg(z)),imp(imp(F,z),imp(T,z))),imp(imp(F,z),imp(T,z)),imp(F,z),imp(T,z),T,z]
assert [tup(x)for x in val['closed_modal_bootstrap']['nodes']]==expected
assert tup(val['closed_modal_bootstrap']['formula'])==z
assert expected[0]==imp(ex(a,qall(a,F)),F)
for major,minor,result in [(1,0,2),(2,3,4),(4,5,6)]:
 assert expected[major]==imp(expected[minor],expected[result])
assert val['closed_modal_bootstrap']['GEN_uses']==0
paths=[p for p in P.rglob('*')if p.is_file()]+[Path(__file__),repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean',repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean']
r={'status':'INDEPENDENT_SOURCE_API_AND_SAVED_DAG_REVIEW_PASS','reviewer':'review_upstream_reflection','role':'Independent reviewer; did not author or run this search or its validator. Own read-only saved-DAG parser only.','findings':[],'source_read':['Complete findings.md, condense.py, validate.py, prior-validator repair and failure, exact Code254 rho1-rho6/rho8 and KCode222 growG definitions.'],'ordinary_proof_review':['Four-family propositional MP closure checked for every major/minor family using native implication injectivity and N(c)>0; native0=I(0,0) retained.','Closed-theorem DNE and arbitrary B weakening follow by exact HF(F,B,C), EFQ(C), MP; no formula DNE or deduction theorem inferred.','rho6(i,F)=NN(Q_i N(Q_i F)) gives the seven-node closed bootstrap.'],'own_data_checks':{'saved_nodes':len(forms),'rule_counts':dict(counts),'all_parent_edges_backward':True,'all_renamed_metavariable_sets_disjoint':True,'all_GEN_labels_fresh_as_numeric_metavariables':True,'all_witnessed_instantiations_and_MP_conclusions_exact':True,'closed_bootstrap_nodes':7},'bounded_run':res,'scope_limits':['No search rerun, Lean/compiler invocation, full-calculus calibration or countermodel.','The four-family theorem is for truth/HF/EFQ/MP only.','The saved search omits the gated bundle and uses an incomplete constructor unifier; absence of targets is only a bounded observation.','Reported elapsed time/pair counts are taken from the held run record, not independently reexecuted.','Canonical metavariable renaming expresses universality of proved numeric schemata; it is not arbitrary substitution of native formulas or labels.'],'history':'Author validator first rejected an identity mapping as a unifier cycle; exact failed source/log and repair retained. Search DAG unchanged.','inputs':[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in sorted(paths)]}
(OUT/'review.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':r['status'],'nodes':len(forms),'rules':dict(counts),'review_sha256':hashlib.sha256((OUT/'review.json').read_bytes()).hexdigest()}))
