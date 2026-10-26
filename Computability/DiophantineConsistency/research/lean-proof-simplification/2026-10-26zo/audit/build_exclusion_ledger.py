from pathlib import Path
import json,re,hashlib
O=Path(__file__).resolve().parent
P='Computability/DiophantineConsistency/research/lean-proof-simplification/'
base=json.loads((O/'prior_exclusion_ledger_120.json').read_text())
entries=[]
for e in base['mechanisms']:
 item={'id':'E'+e['id'][1:].zfill(3),'legacy_id':e['id'],'idea':e['idea'],'status':'excluded_assumed_applied','provenance':'Prior 120-entry ledger from incoming Additional archive; cross-checked with primary placed manuscripts and targeted notes.'}
 for k in ('evidence','indexed_at','primary_source','note','source_label_map'):
  if k in e:item[k]=e[k]
 entries.append(item)
extra=[
('v','report/sections/04_encoding_action.tex','Identify the halt-last Option (Fin 215) stateNumber with finSuccEquivLast; derive injectivity by composition.'),
('v','report/sections/04_encoding_action.tex','Reflect actual action halting through stateNumber_injective and act_stateNumber while retaining target <216.'),
('v','report/sections/05_machine.tex','Split color_action only at the written tape cell; leave moved-head conditional symbolic away from write support.'),
('v','report/sections/07_pulse.tex','Represent west/east step-row edges by one bond pulse and derive horizontal matching by evaluation at one bond.'),
('w','report.tex','Treat the helix as a period lattice vector; derive integer multiples and seam-time invariance through period algebra.'),
('w','report.tex','Prove RefinedPair sign-invariant polynomial identities before evaluation instead of passing through complex square roots.'),
('w','report.tex','Centralize twisted-band indexing in an exact helical coordinate equivalence, normalization and inverse laws.'),
('w','report.tex','Construct matching rows from shared horizontal and vertical edge fields, with constructor-local tile equations.'),
('incoming:Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip','report/08-accounting.tex','Replace finite seam-wall enumeration by Fin 3 bounds and Nat.pow_le_pow_left.'),
('incoming:Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip','report/06-causality.tex','Prove every actual receive tile lies at the actual moved head from spatial matching alone; derive far_pass_or_finish and zero-edge clients.'),
('incoming:Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip','report/07-canonical.tex','Retain complete receiver tile equality and identify extraction with independently constructed stepTile on the open strip; project south_step.'),
('incoming:ProveIt_Additional_Lean_Simplifications_2026-10-26.zip','report/report.tex §A','Replace signed helical induction with a periodic orbit, including a reusable one-parameter orbit interface.'),
('incoming:ProveIt_Additional_Lean_Simplifications_2026-10-26.zip','report/report.tex §B','Derive coprime divisibility decomposition in RatioReparameterization through library divisibility cancellation, retaining degenerate cases.'),
('incoming:ProveIt_Additional_Lean_Simplifications_2026-10-26.zip','report/report.tex §C','Use the exact geometric-series identity to derive the PolynomialRangeBounds geometric inequality.'),
('incoming:ProveIt_Additional_Lean_Simplifications_2026-10-26.zip','report/report.tex §D','Read a positive quadratic margin as the exact centered interval via a square/absolute-value theorem.'),
('incoming:ProveIt_Additional_Lean_Simplifications_2026-10-26.zip','report/report.tex §E','Give finite signed borrow its whole-prefix quotient/remainder meaning, including negative prefixes and borrow-zero iff nonnegative sum.'),
('incoming:ProveIt_Additional_Lean_Simplifications_2026-10-26.zip','report/report.tex §F','Compare native ranks via the single scalar C+qF, with strict/weak/equality comparisons and exact actual-core adapters.'),
('incoming:diophantine-lean-further-deltas-2026-10-26.zip','report/report.tex §P1','Prove the endpoint span cutoff before inspecting most supports in the Sidon position argument.'),
('incoming:diophantine-lean-further-deltas-2026-10-26.zip','report/report.tex §P2','Use a two-dimensional helical period group law instead of induction.'),
('incoming:diophantine-lean-further-deltas-2026-10-26.zip','report/report.tex §P3','Derive the period lower bound from initial-strip width and geometry.'),
('incoming:diophantine-lean-further-deltas-2026-10-26.zip','report/report.tex §P4','Recover the pairing branch from the output square-shell threshold so only two cases remain.'),
('incoming:diophantine-lean-further-deltas-2026-10-26.zip','report/report.tex §P5','Use the list-code constructor equation directly for the list-head bound.'),
('incoming:diophantine-lean-further-deltas-2026-10-26.zip','report/report.tex §P6','Replace two local geometric-sum inductions by matching exact library identities and derive the bound without another induction.'),
('incoming:diophantine-lean-further-deltas-2026-10-26.zip','report/report.tex §P7','Build the internal-natural LinearOrder from its existing strict total order using linearOrderOfSTO, preserving definitional compatibility.'),
('incoming:diophantine-lean-further-deltas-2026-10-26.zip','report/report.tex Supplement','Use direct polarization for the Sidon argument after endpoint-sum equality.'),
('incoming:diophantine-lean-proof-refinements-2026-10-26.zip','report/lean-proof-refinements.tex §A','Derive formula-code thresholds from constructor minima rather than decode or enumerate smaller codes.'),
('incoming:diophantine-lean-proof-refinements-2026-10-26.zip','report/lean-proof-refinements.tex §B','Establish strict internal multiplication through a nonzero additive difference before successor discreteness; obtain Boolean roots from algebra.'),
('incoming:diophantine-lean-proof-refinements-2026-10-26.zip','report/lean-proof-refinements.tex §C','Expose period-one functions to replace helical and seam-time inductions.'),
('incoming:diophantine-lean-proof-refinements-2026-10-26.zip','report/lean-proof-refinements.tex §D','Preserve an exact witness before existential erasure so two existing clients share the stronger intermediate theorem.'),
('incoming:proveit-lean-structural-simplifications-2026-10-26.zip','report.tex §P1','Normalize helical orbits and seam-time invariance through the algebra of periods.'),
('incoming:proveit-lean-structural-simplifications-2026-10-26.zip','report.tex §P2','Replace the index-six Pell threshold with a fixed anchor, retaining monotonicity in the index and parameter rather than a new asymptotic estimate.'),
('incoming:proveit-lean-structural-simplifications-2026-10-26.zip','report.tex §P3','Certify signal-family masses through cardinality and four color-coordinate sums because packed weights are affine in those statistics.'),
('incoming:proveit-lean-structural-simplifications-2026-10-26.zip','report.tex §P4','Recognize operating rows by a canonical full-tile form, optionally using guarded three-color tile determinism.'),
('incoming:ProveIt_Additional_Lean_Simplifications_2026-10-26.zip','report/report.tex Further questions','Extend exact signed-prefix division to concatenation with a nonzero incoming borrow; this is already an announced direction.'),
('incoming:ProveIt_Additional_Lean_Simplifications_2026-10-26.zip','report/report.tex §D/Further questions','Expose both margin endpoints if new clients justify a shared centered-interval lemma.'),
]
for k,(packet,anchor,idea) in enumerate(extra,121):
 source=(P+'2026-10-26'+packet+'/'+anchor) if len(packet)==1 else ('docs/incoming/'+packet.removeprefix('incoming:')+' :: '+anchor)
 entries.append({'id':f'E{k:03}','idea':idea,'status':'excluded_assumed_applied','primary_source':source,'provenance':'Primary manuscript and relevant supporting text inspected in this audit.'})
result={'commit':'9f35798db4a63c25e435fca14d75931144657d7e','rule':'Exclude the same mathematical mechanism at the same target or explicitly announced consumer family, regardless of adoption/compilation status. Generic use of induction or library lemmas alone is not a duplicate. Do not count helper relocation, patch validation or profiling as new ideas.','entry_count':len(entries),'entries_may_overlap':True,'basis':'23 placed packets a-w plus all five current incoming ZIPs and the relevant current intake README; old source snapshots are evidence, not additional independent proposals.','entries':entries}
(O/'exclusion_ledger.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
md=['# Exclusion map', '', 'Pinned source: `'+result['commit']+'`.', '', result['rule'], '', 'All entries below are treated as already applied. Entry counts are bookkeeping counts; some entries overlap.', '']
for e in entries:
 md.extend(['## '+e['id'], '', e['idea'], '', 'Evidence: '+str(e.get('primary_source') or e.get('evidence') or ''), ''])
(O/'EXCLUSION_MAP.md').write_text('\n'.join(md))
print(json.dumps({'entries':len(entries),'outputs':['exclusion_ledger.json','EXCLUSION_MAP.md']}))
