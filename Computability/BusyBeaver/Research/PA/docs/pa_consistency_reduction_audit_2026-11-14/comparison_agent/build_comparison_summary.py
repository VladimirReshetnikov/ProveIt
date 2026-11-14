#!/usr/bin/env python3
"""Attach manuscript-level classifications to a full byte/table inventory."""
import json
from pathlib import Path
P=Path(__file__).resolve().parent
inventory=json.loads((P/'inventory.json').read_text())
# These descriptions report the papers' actual scope; they do not reclassify
# executable symbolic checks as exported PA/kernel proofs.
rows=[
('Below_U208_Research_2026-10-29.zip','208 analysis','Same two primary U208 graphs; conditional source pruning removes five primitive sites but grows DAG 197 to 200; local and seven-cell context searches. No validated smaller machine.'),
('ConPA_below208_research_2026-10-29.zip','208 analysis','Same two primary U208 graphs; 279,936 parameter permutations in seven emitter rows have minimum 197 source nodes; finite-model obstruction and broader local repairs. No sub-208 construction.'),
('PA_consistency_TM_research_2026-11-13.zip','196 reference; source improvements','Combined negation/MP program compressed to 157 source nodes at 3573 sites; original source represented with 159 nodes and maximum zero run five; explicit residual MP command compiler. Neither compressed source has a validated sub-196 implementation.'),
('U208_ConPA_2026-10-29.zip','208','Primary U208 local history fold, deleting native 211 into 172. Complete binary table, exact startup, 5084 symbolic instruction cases; mathematical local halting-equivalence proof with inherited consistency calibration.'),
('U208_ConPA_Conditional_Context_2026-10-29.zip','208','Two U208 layouts; four conditional predecessor-context cases give 1/3/7-step full-tape simulation. Same two primary graph classes, not additional stackable savings.'),
('U208_ConPA_Entry_Context_2026-10-29.zip','208','Two primary U208 classes presented by deleting native 172 into 211. Same state quotient up to names; exact startup and complete symbolic contracts.'),
('U208_ConPA_History_2026-10-29.zip','208','Two primary U208 classes with bounded predecessor-history proof; same fold as other primary packets.'),
('conpa_tm_comparison_and_reduction_search.zip','196 experimental variants','Two one-row MP changes: omit redundant zero push, or return successful consequent in H. Explicit adapted command compiler; source savings but still 196. Rejected Shift/combined layouts retained.'),
('conpa_tm_comparison_and_search.zip','196','A/D logical-register swap in same physical state count; two-rotation 195 candidate fails 93 primitive contracts. Includes scanner shortcut and other rejected attempts.'),
('conpa_tm_study_2026-11-13.zip','196;197 alternative','H-only Shift plus MP result in H gives 3788 sites,4928 contracts and 57922-step startup at 196 states. Direct-negation specialization has 3556 sites but 197 states. Repaired 157-node original CFG costs 207 physical states.'),
('pa196_research_2026-11-13.zip','196 reference; source157','Exact original 3812-site CFG represented with 157 internal nodes;158-node factorization loses a needed physical helper. Refined local folds and two-row repair screens; HA-strength native core and canonical proof-stack discussion.'),
('pa208_research_2026-10-29.zip','208','Eighteen additional pairwise nonisomorphic helper variants, all still 208; with two primary classes the U208 family checked for startup and primitive contracts has 20 graphs. Also direct 18-primitive negation, emitter and successful-MP simplifications.'),
('pa_below196_research.zip','196 reference; census','Earlier 23-archive census,15 selected 196 graphs, four rejected 195 constructions; exact equivalent separation-gate spellings and shortest implication-matrix calculation. No validated sub-196 table.'),
('pa_consistency_comparison_2026_11_13.zip','196 reference;198 alternative','Fresh combinations of source rewrites, split quantifier head with Hilbert certificates, countermodels to axiom deletions, and stronger local deletion searches. No sub-196 result.'),
('pa_consistency_comparison_and_new196_2026-11-13.zip','196 new logical variants','Diagonal-vacuity 191-macro/3700-site calculus compiled at 196; separate diagonal head 190-macro/3673-site calculus also at 196. Scanner-oriented variants preserve 196. The shortened-scanner 195 diagnostic has 96 reported unrestricted contract failures; its first-return tape mismatch alone is not an instruction-endpoint counterexample. The U208/PA196 hybrid fails blank startup.'),
('pa_consistency_reduction.zip','196;203 logical alternative','New exact-CFG rebracketing at 196, plus H-only Shift 3811-site 196 variant. Integrated equality-witness gate deletes one head and 67 sites (3745 total), but best verified table 203. Two 195 physical outputs have counterexamples/failing contracts.'),
('pa_consistency_research.zip','196','158-node source representation; compiled regrouping loses one reader but needs one extra scanner, hence 196. Exact 4959 contracts/startup. All 720 head permutations symbolically checked and 5760 order/antecedent variants grammar-screened; neither membership head is freely deletable.'),
('pa_consistency_research_2026-10-29.zip','208 analysis','Comparison of primary U208 family and source-zero pruning. Five fewer source primitives do not yield a physical reduction; calibration scopes retained.'),
('pa_consistency_research_2026-11-13 (2).zip','196;198 logical alternative','Twelve-rotation 196 source layout; diagonal-vacuity realization reduced 199 to 198; halt-at-last-MP command calculus and bounded physical experiments. No sub-196 table.'),
('pa_consistency_research_2026-11-13.zip','199;197 logical alternatives','Diagonal-vacuity gate B -> forall x_B B reduces 201 to 191 macros and 3812 to 3700 sites, first realized at 199 states. Direct-negation source 3596 realized at 197. Complete startup/symbolic cases, written calibration, no smaller table.'),
('pa_tm_comparison_and_reductions.zip','196;198 logical alternative','Two new rotated 196 reader layouts; equivalent distributed gate 199-macro/3773-site program and 67-rule grammar realized at 198. Countermodels and physical binding audit separate source from machine proof.'),
('pa_tm_extended_research_2026-11-13.zip','196','Four closing-decrement 196 variants; zero/positive and difference-bound invariant reduces 4959 generic cases to 4954 admitted cases. Generalized symbolic frame executor and wider searches, no sub-196 result.'),
('pa_tm_research_2026-11-13 (2).zip','196;202 incomplete alternative','Same-size zero-jump implementations; purported 195 quotient refuted by exact site 26 frame (wrong opcode in patched parent).202-state parity runtime has symbolic contracts but no certified blank startup.'),
('pa_tm_research_2026-11-13.zip','196','Shorter-path alternative 196 table; upstream 4959 primitive contracts and startup reportedly rerun in Lean 4.35.0; new variant independently symbolic-checked. Written native-to-PA reverse translation, no exported new PA endpoint.'),
('pa_unary_power_cover.zip','No literal TM','Unary power-covering schema mutually interpretable with PA via conventional proof translations; division-free polynomial emitter and eight-case theorem stream. No compiled state count.'),
('u208_comparison_research_2026-10-29.zip','208 analysis','Nine primary outputs=two graphs. Exact canonical-frame rejection of 207 reassociation: wrong source address/register after 538 steps versus correct parent 568. No sub-208 construction.'),
('u208_research_2026-10-29.zip','208','Compatibility-parent U208 history fold; one/three/seven-step local simulation,5084 symbolic contracts,48140-step startup plus 141-step bridge; second primary graph class.'),
]
by_archive={x['archive']:x for x in inventory['archives']}
assert {a for a,_,_ in rows}==set(by_archive)
out=[]
for a,b,c in rows:
 out.append({**by_archive[a],'design_scope':b,'comparison':c,'sub196_established_by_manuscript':False})
(P/'archive_comparison.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['# All 27 incoming archives at ProveIt 906367250a7f96c923147b10df392294bced7be5','',
       'This is a fresh classification from the actual archive bytes and main manuscripts. Counts include nested historical copies. No manuscript claims a validated machine below 196 working states. Symbolic verification is distinguished from an exported PA theorem.','',
       '| Archive | Main machine/source result | Comparison |','|---|---|---|']
for a,b,c in rows: lines.append(f'| `{a}` | {b} | {c} |')
(P/'archive_comparison.md').write_text('\n'.join(lines)+'\n')
diagnostics=[t for t in inventory['tables'] if t['states']==195]
(P/'diagnostics195.json').write_text(json.dumps(diagnostics,indent=2)+'\n')
summary={'snapshot':inventory['snapshot'],'top_level_archives':len(out),
 'table_occurrences':len(inventory['tables']),'raw_table_byte_strings':len({t['sha256'] for t in inventory['tables']}),
 'distinct_labeled_transition_functions':len({t['table_sha256'] for t in inventory['tables']}),
 'literal195_occurrences':len(diagnostics),'literal195_byte_strings':len({t['sha256'] for t in diagnostics}),
 'literal195_diagnostic_constructions':6,
 'diagnostic_class_note':'Native/dense two-rotation pair and scanner pair independently checked isomorphic with native start74,dense start0. Four other table byte strings each name a separate rejected diagnostic construction.',
 'all_manuscripts_sub196_result':False,
 'scope':'Counts recognize complete numeric binary tables in .tm/.txt members and repository .tm files. They include nested copies, rejected controls and baselines. They are not counts of correct PA consistency machines; arbitrary JSON/code-embedded tables are not counted.'}
(P/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
