from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path('research/ordinary13-fixed85-source-selection-plan/selection.json')
A=Path('research/ordinary13-fixed85-model-omega-triage/receipt.json')
selection=json.loads(P.read_text());nodes=selection['selected_modules'];prior=json.loads(A.read_text())
targets={
'DiophantineConsistency.ArithmeticControlFrame215':([65,189,269,270,271,272,290,298,308],'finite-control indices, list lengths and natural budgets, even where neighboring values are in V'),
'DiophantineConsistency.ArithmeticHome215':([25,49,50,98,109,113,114,122,125,139,141,142],'natural state, run, and scan-bound indices; model tape values are separate'),
'DiophantineConsistency.ArithmeticMachineTape215':([64],'natural sparse machine state q and finite table length'),
'DiophantineConsistency.ArithmeticRegisterBoxes215':([471,473,475,476],'natural list lengths and finite control offset'),
'DiophantineConsistency.ArithmeticSymbolicCore215':([394,412],'explicitly ordinary-Nat bitsCode and repeated-list equalities'),
'DiophantineConsistency.ArithmeticTilingTable':([93,235,240,242],'Fin or standard natural table indices, with casts to V outside the omega subgoal'),
'DiophantineConsistency.Compact44.CompactCellSizeBound':([21],'standard natural finite-support member n'),
'DiophantineConsistency.Compact44.CompactConcreteMask':([23,51],'standard natural finite mask support and coefficient'),
'DiophantineConsistency.Compact44.CompactConstructedCarryInput':([90,92],'Fin-index/position natural bounds inside exact_mod_cast'),
'DiophantineConsistency.Compact44.CompactConstructedWord':([58,64],'Fin-index/position natural bounds inside exact_mod_cast'),
'DiophantineConsistency.Compact44.CompactHighPhaseReduction':([30,33,35],'standard natural digit index and list-length comparisons'),
'DiophantineConsistency.Compact44.CompactListMask':([36,46,56,62,68,83],'standard natural base, index and digit arithmetic'),
'DiophantineConsistency.Compact44.CompactLowByteAssembly':([36,41,54,55,59,60,64,65,70,71,88],'standard natural byte indices and range predicates'),
'DiophantineConsistency.Compact44.CompactRelabelAssembly':([35,37],'natural list lengths and drop indices'),
'DiophantineConsistency.Compact44.CompactRelabelInverseAssembly':([34,36,94,95],'natural list lengths, finite range witnesses and indices'),
'DiophantineConsistency.Compact44.CompactRowComplete':([130,131,166,169,176,189],'natural tile colors and finite table/rail bounds, with model casts outside the selected goals'),
'DiophantineConsistency.Compact44.CompactTableLookup':([79,80],'natural list-range witnesses'),
'DiophantineConsistency.Compact44.CompactWordFieldCyclic':([40,41,42,58,59,60],'explicit natural offset u before casting into V'),
'DiophantineConsistency.Compact44.CompactWordProductColumn':([50,53],'Fin-index/position natural bounds in source_index arguments'),
'DiophantineConsistency.Compact44.SparseCountBound':([18,20],'natural list lengths, coefficients and bases'),
}
assert not (set(targets) & set(prior['records']))
records={};total=0
for name,(nums,reason) in targets.items():
 r=nodes[name];p=Path(r['source_path']);raw=p.read_bytes()
 assert sha256(raw).hexdigest()==r['sha256'],name
 lines=raw.decode().splitlines();sites=[]
 for i in nums:
  line=lines[i-1];assert re.search(r'\bomega\b',line),(name,i,line)
  sites.append({'line':i,'text':line.strip()});total+=1
 records[name]={'path':str(p),'sha256':r['sha256'],'reviewed_sites':sites,'classification':reason}
anchors={
'DiophantineConsistency.ArithmeticControlFrame215':['(P : List Bool) (overflow : Bool) (extra : Nat)','hP:P.length≤64'],
'DiophantineConsistency.ArithmeticHome215':['{xs : List Seg} {i bound j : Nat}'],
'DiophantineConsistency.ArithmeticMachineTape215':['theorem actual_row {q q\' : Nat}'],
'DiophantineConsistency.ArithmeticSymbolicCore215':['lemma bitsCode_prefix (b : Bool) (n : Nat)','lemma repeat3_nat (k : Nat)'],
'DiophantineConsistency.Compact44.CompactCellSizeBound':['theorem support_lt (n : ℕ)'],
'DiophantineConsistency.Compact44.CompactListMask':['theorem digits_length (B len special : ℕ)'],
'DiophantineConsistency.Compact44.CompactWordFieldCyclic':['(u : ℕ) (hu : u<8)'],
'DiophantineConsistency.Compact44.SparseCountBound':['(terms : List (ℕ × ℕ)) (j B : ℕ)'],
}
for n,needles in anchors.items():
 text=Path(records[n]['path']).read_text()
 for needle in needles:assert needle in text,(n,needle)
print(json.dumps({'selection_sha256':sha256(P.read_bytes()).hexdigest(),
 'prior_slice_receipt_sha256':sha256(A.read_bytes()).hexdigest(),
 'reviewed_module_count':len(records),'reviewed_omega_line_count':total,
 'records':records,'overlap_with_prior_modules':False,
 'finding':'No additional abstract-model omega hazard identified among the selected sites.',
 'lean_executed':False,'scope':'Bounded source-context triage only; other sites, elaboration, providers, axioms, frontier and endpoint remain open.'},sort_keys=True,indent=2))
