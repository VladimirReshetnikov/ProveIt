"""Measure a partial-functional subset-closure alternative with explicit Union.

This is a negative fixed-layout compiler experiment, not a calibrated machine.
The ordinary candidate proof and exact scope are in functional_subset_closure.md.
It retains the complete original equality logic and uses pinned Wade helpers.
All generated tables/evidence are written outside the checkout.
"""
from pathlib import Path
import sys,tempfile,importlib,json,itertools,time,argparse,hashlib
root=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(root/'Computability/BusyBeaver/Research/ZFC'))
import theory_backend_experiment as t
import recover_wade_dag as r
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();p=a.output.resolve()
if p==root or root in p.parents:ap.error('output must be outside the checkout')
if not __debug__:ap.error('run without -O: executable contracts use assertions')
p.mkdir(parents=True,exist_ok=True)
for n in ['TMBuilder.py','tm.py','tmdb.py','LICENSE.wade']:(p/n).write_bytes(r.git_bytes(None,'ZF/generator/'+n))
sys.path.insert(0,str(p));backend=importlib.import_module('TMBuilder')
nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode());_,logical,old=t.old_contract(nodes)
I,R,E,A,EX,AND,OR,IFF=t.Imp,t.Rel,t.Eq,t.All,t.Ex,t.And,t.Or,t.Iff
c='c';phi=c
ext=A(0,A(1,I(A(c,IFF(R(c,0),R(c,1))),E(0,1))))
union=A(0,EX(1,A(c,IFF(R(c,1),EX(1,AND(R(1,0),R(c,1)))))))
seed=A(c,I(R(c,0),R(c,1)))
supported=A(1,I(R(1,c),EX(0,phi)))
closed=A(0,I(OR(seed,R(0,c)),A(1,I(phi,R(1,c)))))
old_bound=A(0,EX(c,A(1,I(phi,A(0,I(R(0,1),R(0,c)))))))
fun_bound=A(0,EX(c,A(1,I(phi,E(1,c)))))
psc=I(old_bound,A(1,EX(c,AND(closed,supported))))
fpsc=I(fun_bound,A(1,EX(c,AND(closed,supported))))
vr=I(R('a','b'),A(c,R('a','b')));ve=I(E('a','b'),A(c,E('a','b')));vacuity=AND(vr,ve)
variants={'point_subset_bound_PSC_control':t.theory_rows()[0],'subset_bound_subset_PSC':AND(ext,psc),'equality_bound_subset_PSC_plus_Union':AND(ext,AND(union,fpsc))}
results=[]
for name,f in variants.items():
 assert t.symbolic(t.emit(f))[0]==['old_top',f]
 t.theory_rows=lambda f=f:(f,vacuity)
 start=time.monotonic();builder=t.build_variant(backend,nodes,names,logical,'fixed_PSC_separate_vacuity');builder.generate();builder.tm.gc();states={q for q,_ in builder.tm.states};builder.tm.save(str(p/(name+'.tm')))
 results.append({'variant':name,'whole_theory_constructor_macros':len(t.emit(f)),'logical_prefix_macros':len(logical),'vacuity_macros':len(t.emit(vacuity)),'working_states':len(states),'decision_states':sum(not q[0].isdigit() for q in states),'framework_states':sum(q[0].isdigit() for q in states),'transition_rows':len(builder.tm.states),'seconds':time.monotonic()-start,'equality_helper_retained':any(q.startswith('weq(') for q in states),'symbolic_RPN_exact':True})
print(json.dumps(results,indent=2))
(p/'results.json').write_text(json.dumps({'scope':'Three fixed unoptimized compile comparisons, full original equality logic and base4/backend retained, local c>=2 and original c!=a,b gates retained; no full frontend/calibration or binary runtime claim.','source':str(Path(__file__)),'upstream':r.COMMIT,'results':results,'formula_ASTs':variants,'freshness':'c is a fresh variable label distinct from fixed0,1; no parameter-renaming compiler is added','driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'missing_rows_scope':'Tables are named compiler controls, before any separate blank initialization certificate; no complete literal blank-machine claim','logical_engine':'Full original GEN plus all eight equality/logical schemas, base4 constructors retained'},indent=2)+'\n')
print(p)

forms=variants;counts={k:0 for k in forms}
def evaluate(f,e,M,phi,domain):
 if f=='c':return phi(e[0],e[1])
 if f==1:return M(e[0],e[0])
 k,a,b=f
 if k=='rel':return M(e[a],e[b])
 if k=='eq':return e[a]==e[b]
 if k=='imp':return not evaluate(a,e,M,phi,domain) or evaluate(b,e,M,phi,domain)
 if k=='all':return all(evaluate(b,e|{a:x},M,phi,domain) for x in domain)
 raise ValueError(k)
for n in (1,2):
 D=range(n);edges=[(x,y) for x in D for y in D if x!=y]
 for bits in range(1<<len(edges)):
  relation={e for i,e in enumerate(edges) if bits>>i&1};M=lambda x,y:(x,y) in relation
  sub=lambda x,y:all(not M(z,x) or M(z,y) for z in D)
  ext=all(not all(M(z,x)==M(z,y) for z in D) or x==y for x in D for y in D)
  union=all(any(all(M(y,b)==any(M(x,a) and M(y,x) for x in D) for y in D) for b in D) for a in D)
  for truth in range(1<<(n*n)):
   phi=lambda x,y:bool(truth>>(x*n+y)&1)
   sb=all(any(all(not phi(x,y) or sub(y,b) for y in D) for b in D) for x in D)
   eb=all(any(all(not phi(x,y) or y==b for y in D) for b in D) for x in D)
   functional=all(not(phi(x,y) and phi(x,z)) or y==z for x in D for y in D for z in D)
   assert eb==functional
   def hull(subsetseed):
    return all(any(all(not ((sub(x,a) if subsetseed else x==a) or M(x,c)) or all(not phi(x,y) or M(y,c) for y in D) for x in D) and all(not M(y,c) or any(phi(x,y) for x in D) for y in D) for c in D) for a in D)
   expected={'point_subset_bound_PSC_control':ext and (not sb or hull(False)),'subset_bound_subset_PSC':ext and (not sb or hull(True)),'equality_bound_subset_PSC_plus_Union':ext and union and (not eb or hull(True))}
   for name,f in forms.items():
    assert evaluate(f,{0:0,1:0,'c':0},M,phi,D)==expected[name],(n,bits,truth,name)
    counts[name]+=1
res={'status':'PASS','cases_by_variant':counts,'total_AST_vs_direct_cases':sum(counts.values()),'domain_sizes':[1,2],'irreflexive_relations_only':True,'all_relation_truth_matrices':True,'equality_bound_iff_partial_functional_checked':True,'scope':'Finite capture/AST regression, not equiconsistency or uniform numeric completeness.'}
(p/'finite.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
