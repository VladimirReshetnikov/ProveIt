from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path('research/ordinary13-fixed85-source-selection-plan/selection.json')
A=Path('research/ordinary13-fixed85-model-omega-triage/receipt.json')
B=Path('research/ordinary13-fixed85-model-omega-triage-slice2/receipt.json')
nodes=json.loads(P.read_text())['selected_modules'];prior1=json.loads(A.read_text())['records'];prior2=json.loads(B.read_text())['records']
targets={
'DiophantineConsistency.PRAParameterPackingIteration':([25,29,52,56,59,63,68,71,116,131],'natural arity n, Fin casts, and variable indices; semantic values may have type M'),
'DiophantineConsistency.PRAParameterPackingN':([12,28,32,39,53,54,58,67,76,85,93,99,111,116,217,231],'natural arity, Fin casts, and standard numeral indices; semantic values may have type M'),
'DiophantineConsistency.PRABoundedSearchUniversal':([126,127],'natural i and n in Fin index constructors for an M-valued environment'),
'DiophantineConsistency.PRABoundedSelector':([54],'natural j and n in an M-valued environment index'),
'DiophantineConsistency.PRAPositiveStrictCertificate':([49],'natural Fin index modulo a natural arity'),
'DiophantineConsistency.PRAPositivePackedNormal':([26],'natural free-variable index after Fin.append case split'),
'DiophantineConsistency.PRAStageCodedRemoval':([33,47,58],'natural code arities and stage indices, not model values'),
'DiophantineConsistency.PRAStagePredicateExtension':([10,18],'natural Fin projection bounds in predicate code arities'),
'DiophantineConsistency.PRAStageSelectedQ':([29,30,31,34,36],'natural Fin.val and challenge indices'),
'DiophantineConsistency.PRAUniversalInduction':([53],'natural free-variable indexing after environment case split'),
'DiophantineConsistency.PRACodeEncoding':([30,33],'standard natural pairing and unpairing inequalities'),
'DiophantineConsistency.PRAChallengePermutation':([12,32,46,49,55,56],'natural arities and Fin.val bounds in M-valued semantic environments'),
'DiophantineConsistency.PRAProofRewriting':([28],'standard natural free-variable support cap'),
'DiophantineConsistency.HerbrandChiRetainedStability':([20],'natural stage and free-variable support index'),
'DiophantineConsistency.HerbrandStageBodyEvaluation':([62],'natural free-variable index and support bound'),
'DiophantineConsistency.HerbrandSchedule':([15,24,30,61],'natural term encoding, stage and free-variable bounds'),
'DiophantineConsistency.HerbrandTupleSchedule':([14,38],'natural tuple stages, unpairing and free-variable bounds'),
'DiophantineConsistency.HerbrandStageSupport':([27,45,46,47,87,109],'natural stage indices and finite variable support'),
'DiophantineConsistency.HerbrandChiStageContext':([54,66,77,99,111],'natural list-stage and free-variable support indices'),
'DiophantineConsistency.HerbrandInteractiveFourTriple':([35,46,50,54,59,64,69,74,78],'natural term-support and free-variable indices'),
}
assert not (set(targets)&(set(prior1)|set(prior2)))
records={};total=0
for name,(nums,reason) in targets.items():
 r=nodes[name];p=Path(r['source_path']);raw=p.read_bytes();assert sha256(raw).hexdigest()==r['sha256'],name
 lines=raw.decode().splitlines();sites=[]
 for i in nums:
  line=lines[i-1];assert re.search(r'\bomega\b',line),(name,i,line)
  sites.append({'line':i,'text':line.strip()});total+=1
 records[name]={'path':str(p),'sha256':r['sha256'],'reviewed_sites':sites,'classification':reason}
anchors={
 'DiophantineConsistency.PRAParameterPackingIteration':['theorem align_eval {M : Type} [Structure language M] (n : ℕ)','(v : Fin (4+n) → M)'],
 'DiophantineConsistency.PRAParameterPackingN':['theorem modelPacking (n : ℕ)','def align (n : ℕ)'],
 'DiophantineConsistency.PRABoundedSelector':['let e : ℕ → M := fun j'],
 'DiophantineConsistency.PRAStagePredicateExtension':['def extendPredicate {m n : ℕ}'],
 'DiophantineConsistency.PRAChallengePermutation':['def reorderedIndex (n : ℕ) (i : Fin (n+3))'],
 'DiophantineConsistency.HerbrandSchedule':['theorem lt_bound (t : SyntacticTerm language) {i : ℕ}'],
 'DiophantineConsistency.HerbrandInteractiveFourTriple':['theorem term_support (r j : ℕ) (k : Fin 4) {i : ℕ}'],
}
for n,needles in anchors.items():
 text=Path(records[n]['path']).read_text()
 for needle in needles:assert needle in text,(n,needle)
print(json.dumps({'selection_sha256':sha256(P.read_bytes()).hexdigest(),
 'prior_slice_receipt_sha256':[sha256(A.read_bytes()).hexdigest(),sha256(B.read_bytes()).hexdigest()],
 'reviewed_module_count':len(records),'reviewed_omega_line_count':total,
 'records':records,'overlap_with_prior_modules':False,
 'finding':'No additional abstract-model omega hazard identified among the selected sites.',
 'lean_executed':False,'scope':'Bounded source-context triage only; uninspected sites, elaboration, providers, axioms, frontier and endpoint remain open.'},sort_keys=True,indent=2))
