# Current comparison of PA consistency machines

## Snapshot and scope

The inspected source is `VladimirReshetnikov/ProveIt` at
`1fe9b29810bfe3d0e507146d65f6b97692e7444a`. Its PA subtree is
`dc4d1ed9027c2b251ee751679d2690c6b1265b03`; its incoming subtree is
`19b0b7e26f84a3ebac927e8768c7a21067d03a06`. All 24 top-level incoming
ZIPs were inventoried, including nested ZIPs to arbitrary depth, deduplicating
identical archive bodies by SHA-256. The PA research directory was also
inventoried. This is a source comparison, not a claim that every experimental
table is correct.

The fresh inventory finds 37 distinct archive bodies, 65 archive references,
and maximum nesting depth 8. Across those distinct bodies and the PA directory
there are 23,699 file occurrences and 1,279 complete numeric binary-TM table
occurrences. They have 505 distinct byte forms and 382 action-preserving,
root-free graph classes. These counts include ancestors, rejected tables,
synthetic controls and duplicate encodings. Every classified graph has a
vertex reaching all its working states, as required by the canonicalizer.
Root-free classification intentionally ignores the chosen initial state.

The meaningful designated counts are much smaller:

* 27 designated U208 presentations form 20 rooted graph classes. The original
  nine form two classes; 18 later helper layouts add 18 classes.
* The selected 196-state catalogue contains 18 distinct rooted graphs:
  one published baseline, 13 report-positive candidate layouts, two explicitly
  experimental MP layouts, and two explicitly rejected blank-halting controls.
  The candidate status records the source manuscript's validation claim,
  not a new Lean endpoint.
* Five byte forms with 195 working states form four graph classes. Every one
  belongs to an explicitly rejected or diagnostic construction. No inspected
  archive supplies a validated sub-196 consistency machine.

The U208 classification was rerun from the current ZIP bytes. Seven explicit
state bijections satisfy all 2,912 transition-row equations identifying the
original duplicates. The current selected-196 classification was rerun from
the exact archive members, including Combined196, which is not in the
repository's earlier 17-table catalogue. Byte counts and source evidence are
in `inventory/`, `designated_comparison.json`, and `selected196_catalog.json`.

## Principal ancestry and metrics

| Construction | Working states | Source occurrences | Distinct internal source nodes | Maximum path | Blank startup |
|---|---:|---:|---:|---:|---:|
| Historical U208 A | 208 | 3,909 | 174 | 42 | 48,140 |
| Historical U208 B | 208 | 3,909 | 174 | 41 | 48,140 |
| James Chang PA209 | 209 | 3,948 | 173 | 33 | 58,210 |
| James Chang PA196 | 196 | 3,812 | 159 | 38 | 58,154 |
| Earlier shorter-path alternative196 | 196 | 3,812 | 159 | 36 | 58,154 |
| Latest Combined196 | 196 | 3,788 | — | — | 57,922 |

The source and startup metrics above are reported in the pinned source
manuscripts and reproduction receipts. This audit freshly checks table
structure and identity; it does not claim to have rerun every symbolic
runtime contract or every startup.

James Chang's imported PA196 snapshot is upstream revision
`407cdc356f6b586635e71ac92be394255f4bfea4`; PA209 is
`69d98241a721ead20b4f0b17df9062950b40fbfe`.
PA196's dense table SHA-256 is
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.
The historical Joint U209 ancestor of U208 is a different program from
James Chang's PA209. Native labels cannot be equated across these lineages.

PA196 changes the universal constructor to
`U(a,B) = 4 pair(B,a) + 2`, transposing the pair components. Its axiom
emitter omits the old seventh head, incorporates guarded equality vacuity,
changes head and antecedent order, and shares complementary reader contexts.
The physical census is 36 arithmetic-engine controls, 13 leaf routers and
147 reader controls. The 147 readers implement 159 internal source nodes.
The six AX reader folds are already included in 196.

The U208 reduction identifies native controls 172 and 211 in its own parent.
The four exceptional local simulations have lengths 7, 1, 3 and 1, giving
`T208 = T209 + 6 N(172,0) + 2 N(211,0)` at aligned steps. It is one
state saving with several presentations. PA196 has no state whose two
actions are `0 L q` and `1 R q` to the same working target, so the precise
mixed-entry motif cannot be transported merely by renaming states. This is
an obstruction to that motif, not a general reduction impossibility theorem.

## Every incoming archive

The filenames below are exact identities in the pinned incoming directory.
All stated state counts exclude the separate halt control.

| Archive | Main contribution | Limitation or relevant outcome |
|---|---|---|
| `Below_U208_Research_2026-10-29.zip` | Source-boundary windows, offset quotients and guarded source pruning | 3,909→3,904 sites; no validated machine at or below 207 |
| `ConPA_below208_research_2026-10-29.zip` | Comparative audit, finite-model obstruction to cover-role identification, bounded fold searches | No reduction below 208; restricted minima are not global bounds |
| `PA_consistency_TM_research_2026-11-13.zip` | Exact 159-node original source with zero-run bound 5; exact 157-node combined-negation/MP source; residual MP; broad local screens | No accepted sub-196 table; reader allocation and startup for the shorter scanner remain open |
| `U208_ConPA_2026-10-29.zip` | Three-cell history fold 172/211 | One original rooted U208 class; inherited theory calibration |
| `U208_ConPA_Conditional_Context_2026-10-29.zip` | Conditional-entry proof of the fold; two presentations | The original two U208 classes, not extra independent savings |
| `U208_ConPA_Entry_Context_2026-10-29.zip` | Complete entry-context proof and tables | Same primary/alternative rooted classes |
| `U208_ConPA_History_2026-10-29.zip` | Finite-history presentation and exact local simulation | Same two original U208 classes |
| `conpa_tm_comparison_and_reduction_search.zip` | MP without zero push and MP-result-in-H experimental 196 tables; register/layout catalogues | Two proposed Shift layouts actually halt after 43,563 blank steps; no sub-196 result |
| `conpa_tm_comparison_and_search.zip` | A/D-register-swap 196 layout; rejected 195 quotient; logical countermodel | Rejected195 fails 93 of 4,959 source contracts |
| `conpa_tm_study_2026-11-13.zip` | Combined196: H-only Shift and MP result in H; 3,788 sites and 4,928 contracts; direct-negation197 with 3,556 sites | Complete 196 intermediate, not a strict reduction; new logical endpoint is paper-level |
| `pa196_research_2026-11-13.zip` | Exact 157-node representation of all 3,812 original CFG rows; HA-strength reference calculus | No correct sub-196 physical allocation; source-node savings lose contextual readers |
| `pa208_research_2026-10-29.zip` | Eighteen additional same-size U208 helper variants, source/theory/compiler work | Gives 20 total designated U208 classes, not a machine below 208 |
| `pa_consistency_comparison_2026_11_13.zip` | Modal-B plus explosion split of quantifier head; finite Hilbert proofs; 12 composition experiments; 189-token joint gate | Composition tables remain 196–200; shortened emitter is not a smaller machine |
| `pa_consistency_reduction.zip` | Rebracketed196 and H-only196; integrated witness gate; ordinary internal-converse manuscript | Logical gate compiles to 203/206; rejected195 helper combination cycles |
| `pa_consistency_research.zip` | Two exact 158-node source representations; repaired 196 physical layout; logical-head search | Nominal195 requires an eighth-zero scanner and becomes196 |
| `pa_consistency_research_2026-10-29.zip` | Inductively certified 3,909→3,904 source specialization | No validated physical machine below208 |
| `pa_consistency_research_2026-11-13 (2).zip` | New rotated196; diagonal source improved199→198; halt-at-successful-MP source; joint register abstraction | No strict improvement below196; command source is not a new binary TM |
| `pa_consistency_research_2026-11-13.zip` | Diagonal-vacuity calculus, 3,700-site199 machine; short-negation197 | 4,815 symbolic contracts for199; no sub-196 result |
| `pa_tm_comparison_and_reductions.zip` | Rotated196 and rotated-macro62-196; distributed gate3,773 sites compiled198 | Grammar-rule and macro-token counts are not state counts |
| `pa_tm_extended_research_2026-11-13.zip` | Four closing-CD3/CD4/CD5/CD6 alternatives, stronger invariants, flexible symbolic checks | All196; all four replace the same row and cannot be stacked |
| `pa_tm_research_2026-11-13.zip` | Shorter-path196, independent symbolic checks, physical Lean subset, reverse-translation manuscript | Alternative lacks fresh full Lean endpoint; reverse arithmetic theorem remains manuscript-level |
| `pa_unary_power_cover.zip` | Unary weak-covering theory and mutual PA interpretation/proof templates | No newly compiled literal machine |
| `u208_comparison_research_2026-10-29.zip` | Original two-class census, weak/exact schema comparison, rejected207 frame witness | Does not include the later eighteen helper classes; no sub208 result |
| `u208_research_2026-10-29.zip` | Two U208 outputs and symbolic runtime evidence | Same original history-fold saving; no global minimum claim |

## The positive and experimental 196 layouts

The twelve previously curated report-positive/baseline graphs remain present.
They are PA196, shorter-path196, regrouped158-node196, rotated196,
rotated-macro62-196, rebracketed196, H-only196, A/D-swap196, and four
closing-decrement variants. The latest incoming files add a twelve-rotation196
and Combined196, giving fourteen report-positive/baseline graphs.

Two experimental graphs separately implement MP result in H and MP without
zero push. Two rejected graphs are included only as negative controls.
Their 18 exact hashes, rooted graph identities, member names and status
classes appear in `selected196_catalog.json`.

Combined196 is in
`conpa_tm_study_2026-11-13.zip!conpa_tm_study/machines/h_only_mp_h.tm`.
Its table SHA-256 is
`bd74754d75e7b8ba97fa7bfc104374de33ae603fc183ae7f08f053ab8c9ea592`.
It starts at0, has working labels0..195, and halts at196. This is a distinct
rooted graph, not a copy of the earlier MP-only experiment. Its report gives
3,788 source sites, 4,928 uniform instruction contracts and57,922-step startup.

The four closing-decrement variants all change native row `(1365,1)`, dense
row `(193,1)`, in mutually exclusive ways. A proved-zero register at source
occurrence3692 makes the selected decrement behave like the original closing
jump. Four such alternatives do not constitute four disjoint savings.

## What the supplied rejection evidence actually proves

* `conpa_tm_comparison_and_search` rejected195: a source reassociation invalidates
  the history-sensitive reader before an identical-row quotient is taken.
  Ninety-three of4,959 contracts fail. This rejects the proposed refinement,
  not every conceivable proof of that table's eventual behavior.
* `pa_consistency_research/data/rejected195.native.tm`: the source occurrence1003
  seven-zero path is mistaken for the marker. An extra scanner control repairs
  it at196.
* `pa_consistency_reduction/verification/candidates/warm_physical_61_8047.tm`:
  the intended source-frame simulation enters an exact four-step loop.
* The same archive's `extended_physical_61_12085.tm` is another diagnostic195
  allocation, explicitly rejected by its frame checks.
* The old dense45→160 merge with repair184/1=`1 L75` survives100 million blank
  steps but violates its claimed block refinement at parent step1,223,335,721:
  the checked continuation selects source615 instead of605. This is a concrete
  refutation of that proof contract, not a general halting-inequivalence proof.
* The two rejected196 Shift layouts have the stronger result: they actually
  first halt from blank at43,563. The current repository includes a Lean
  chunk certificate for that complete finite trace. The two tables differ
  only at115/1, a row unvisited by their common blank trace.

The last distinction matters. A bad macro simulation can sometimes indicate
an incomplete invariant; an actual finite blank halt directly refutes
nonhalting in the standard interpretation.

## Formal and mathematical proof levels

The imported theorem inventory and `PA196/Independence.lean` explicitly
export `PA ⊢ Nonhalt(PA196) → Con(PA)`. They also prove nonhalting in the
external Lean metatheory. This is not an exported internal biconditional.
The same distinction applies to imported PA209.

Several incoming manuscripts supply a substantial ordinary mathematical route
to the reverse implication: interpret membership as binary-bit membership,
translate the transposed quantifier directly, use a syntactic full-PA-induction
template for finite comprehension, accommodate coincident variable labels,
handle code0 as the truth alias, and carry proof certificates through command
execution. Positive nonhalt simulation blocks plus determinism can bound the
source trace needed to explain a literal halt. These arguments should be
assessed as mathematical proofs with explicit coding contracts; absence of a
new Lean certificate does not by itself refute them.

The current PA directory adds real prerequisites beyond the earlier audit:

* `reverse-cert-stack/CertificateStack.lean` proves the zero-alias/ghost-proof
  stack invariant over ordinary Nat.
* `UpstreamCommandAudit.lean` binds standalone command shapes to the actual
  imported command definitions and fixes a previous head3/head4 ordering error.
* `NativeChecker.lean` and `NativeCheckerBinding.lean` prove actual command-word
  halt→accepted numeric checker code1 without checker-constructor hypotheses.
* `CheckerRuleAudit.lean` binds a callback interpretation of extracted numeric
  checker-rule syntax to the direct implementation.

These remain standard-Nat results. The direct list table has not been
formally equated with Foundation's model-valued `Checker.verifyValue`.
The all-model literal-halt extraction and syntactic PA-proof translation still
need their internal proofs for an exported biconditional.

The new `ipra/` bridge also does not establish that endpoint. It gives a
primitive-recursive bounded literal simulator, a standard-model interpretation,
and a conditional iPRA theorem assuming both machine-specific reductions.
Substituting ConciseIPRA's smaller checker for the PA search without a new
PA-strength calibration would change the target problem.

## Search directions not exhausted by these results

The comparison identifies concrete remaining opportunities, not promised
reductions:

1. **Shorter scanner with coordinated reader/startup allocation.** The newest
   exact original-source witness has159 nodes, maximum path37 and maximum zero
   run5; its seed25 moves from100000 to10100000. A detector for six zeros could
   remove one scanner control if the dynamic extra-zero invariant, all reader
   aliases and the entire startup are rebuilt. The archive only rejects a
   naive root rewire and788 one-row repairs at69/0. It supplies no full physical
   allocation of the successful zero-five source. A seed-preserving zero-five
   witness or a compatible startup synthesis is a narrower concrete target
   than another broad fixed-table pair-merge search.
2. **Recoding constructor tags, jointly with head order.** Existing reported
   searches vary pairing orientation, antecedent order, head order, source
   bracketing and some formula parity conventions. Equality/universal tag
   exchange while retaining implication0 and membership1 is not among the
   described screens examined here. It changes the emitter's repeated words
   while preserving the special contradiction and truth aliases. Exact
   syntax transport and numeric guards still need proof; freshness cannot be
   assumed after a code change.
3. **Optimize newer semantics jointly with geometry.** Combined196's H-only
   test, MP-result-in-H, halt-at-successful-MP, diagonal vacuity and residual
   comparator are alternatives whose proof contracts differ. Full composition
   should price source sharing, register order, longest zero run and startup
   together. The 12 already supplied original/distributed/diagonal ×shortNeg
   ×MP combinations must not be repeated as a novel result.
4. **Change instruction/tape representation.** Local screens permit only
   bounded windows, bounded stuttering, a few repaired rows, and particular
   head-offset/neighbor-bit encodings. They do not cover a redesigned return
   address code, new delimiters, persistent control bits, or an arithmetic
   engine with a different frame convention. Such a change needs a complete
   new invariant and is more expensive to verify, but is not ruled out by
   billions of negative actions within the old template.

The newest local screens already test14 selected196 tables,535,080 ordered
state pairs and targeted third-row repairs. Their third stage is not an
exhaustive search over all three-row changes: the two-row pruning can exclude
a transformation requiring three interacting repairs. Enlarging only the
reported run count adds no mathematical lower bound.

## Reproduction and attribution

`audit_all_archives.py` and its parser are adapted from the earlier read-only
comparison work; this audit changes their snapshot pin and reruns them against
the new checkout. The source parser recognizes complete five-column numeric
binary tables. Other encodings and program descriptions are retained in the
file inventory but are not silently counted as extra tables. The U208
comparison checker is likewise inherited and rerun, not claimed as new
mathematics. Current source-manuscript claims are distinguished above from
fresh graph checks and from kernel-checked endpoints.
