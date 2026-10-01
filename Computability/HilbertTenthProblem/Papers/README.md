# Corrected editions of six articles on Diophantine representation

This directory holds the continuously revised corrected editions of six
articles by J. P. Jones and coauthors (1974–1984), their editorial notes and
their verification programs. The editorial notes compare each edition with
the journal scan and its raw Mathpix OCR, which they cite as
`original/<year>/jones<year>.pdf` and `original/<year>/jones<year>.tex`;
these inputs are not included here. The editions are modified in place as
further corrections are found; `EDITORIAL_NOTES.md` is their dated log.

## Layout

| Path | Contents |
|---|---|
| `<year>/jones<year>_corrected.tex`, `.pdf` | The corrected edition and its PDF (engines: pdfLaTeX; LuaLaTeX for 1978; XeLaTeX for 1982). The original journal pagination is marked in the margin (`\origpage{n}`, line accuracy, checked against the scans). |
| `<year>/jones<year>_editorial_notes.md` | The editorial notes for one article: every discrepancy between the naive Mathpix OCR of the scan and the edition, with its classification and justification; editorial additions; readings examined and retained; verification summary. **Start here** for one article. |
| `EDITORIAL_NOTES.md` | The dated log of revisions and checks: each change with its location in the original pagination, old and new text, classification and reason; checks that found nothing; findings fed back from the Lean formalization in `../Lean/`; the operation-count work on the 1980 Theorem 5; environment notes. |
| `verification/round4_<year>_checks.py` | Independent per-article checks; each writes `round4_<year>_results.json` next to itself. Run with `PYTHONUTF8=1 python verification/round4_<year>_checks.py`. |
| `verification/jones<year>_*`, `corpus_*` | Further per-article and cross-article checks, reading the current sources: `jones1974_verify_machines.py`, `jones1974_verify_counts.cpp`, `jones1976_verify_mathematics.py`, `jones1976_verify_87_operations.py` (which writes the 87-operation certificate `jones1976_primality87.json` and `.md`), `jones1978_validation.py`, `jones1982_verification.py`, `jones1984_verification.py`, `corpus_cross_review.py` and `corpus_review.py`. Each writes its results next to itself. |
| `verification/round4_1976_theorem39.wl` | Wolfram Language instantiation of Theorem 3.9 (1976) for `k = 1`. |
| `verification/round4_1982_lemma225.py` | Numerical instances of Lemma 2.25 (1982). |
| `verification/roundNN_1980_*`, `explore_*`, `audit_*` | Operation-count reconstruction and the straight-line certificates for the 1980 Theorem 5 (see below). |
| `1980/jones1980_theorem5_operations.tex`, `.pdf` | Satellite article on the operation count `o = 100` of the 1980 Theorem 5 and on explicit straight-line certificates; the generated tables `jones1980_theorem5_*schedule*.tex` and the sectional drafts `jones1980_theorem5_optimization.tex`, `jones1980_pell_optimization.tex`, `jones1980_theorem5_short_masks.tex` are its inputs. |
| `1980/*_PROOF.md`, `1980/EXPLORATION_*.md` | Standalone proofs of the equivalences used by the successive certificate reductions, and explorations of alternatives. |

## Findings

The [native-stream queue WIP handoff](research-wip/native-stream-queue/README.md)
preserves the conditional six/eight-operation stream component, portable
independent audits, unfinished controller research and archived scratch
evidence. Its [continuation prompt](research-wip/native-stream-queue/CONTINUATION_PROMPT.md)
records the current75-operation certificate and87-operation polynomial
frontiers alongside the historical handoff. The
[complete half-binomial75 proof](1980/FIXED_RAW_UNIVERSAL_75_PROOF.md)
supplies the comparison bound; the
[normalized strong87 proof](research-wip/native-stream-queue/complete75_normalized_strong87.md)
supplies the single-polynomial bound.

The latest explicit [shared-history U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_shared_history265.md)
gives **251 certificate /265=134M+131A polynomial operations**,
5 comparisons,43 positive witnesses, four positive program parameters
and degree **at most3853**. Reusing paid powers, a selector prefix and
the radix decrement removes2M+2A from269. The complete polynomial is
identical on every integer assignment; supplied coordinates and the
positive domain are unchanged. The same four-gate saving shifts the
inherited finite frontier to271/1094,272/1048,273/734,274/706 and275/608
with44 witnesses; the fixed43-witness family reaches272/1344. These
remain optima only for the stated finite propagated-degree objective.
The established75/87 frontier is unchanged.

The [paid queue sentinel fold](research-wip/native-stream-queue/queue_causality_sentinel_fold.md)
gives fixed-horizon cyclic-tag certificates with at most14T-2 operations
for T>=2, T+1 positive witnesses and degree at most2T. It retains the
first-failure guard and exact-execution uniqueness. The guard-free
10T+1-operation/T-witness family represents eventual halting only after
an existential choice of horizon. Input words and T are fixed compiler
data; this is not a fixed-arity universal bound. A two-schedule planner
retains the cheaper forward form when sentinel folding loses.

The preceding explicit [factored-port U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_factored_ports269.md)
gives **255 certificate /269=136M+133A polynomial operations**,
5 comparisons,43 positive witnesses and four positive program parameters,
with degree **at most3853**. Factoring the native packed index and folding
existing affine expressions saves six additions from275. The complete
polynomial is identical on every integer assignment, with unchanged
supplied coordinates and positive domain. The separate75/87 frontier is unchanged.

The [earlier grouped degree tradeoffs](research-wip/native-stream-queue/neary_woods_universal_computed_ports_partitions.md)
optimize all factor partitions and permitted anchors over16 inherited
strong-treatment/positive-scale bases after checksum specialization.
They give275/degree-at-most1094,276/1048,277/734,278/706 and279/608,
all with44 witnesses; the fixed43-witness family reaches276/1344.
These are exact optima of the stated finite propagated-degree objective.
The minimum bound608 is not a lower bound on exact degree or all circuits.
Regrouping preserves positive zeros within each fixed base; different
bases retain the same accepted relation on valid program slices.

The preceding [computed-port U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_computed_ports275.md)
gives **261 certificate /275=136M+139A polynomial operations**,
5 comparisons,43 positive witnesses and four positive program parameters,
with degree **at most3853**. Retained mask and history bounds make three
computed native fields positive at zeros. The one- and two-field modes are positive
zero-set graph bijections; eliminating the checksum preserves the accepted
outer relation through the parent's private sign normalization.
The mapped lower-degree option gives **285 operations / degree at most608**
with44 witnesses; the fixed43-witness alternative is282/1344. These are
specializations of twelve selected parent schedules, not a new partition
search or a global optimum. The separate75/87 frontier is unchanged.

The [duration-floor282 predecessor](research-wip/native-stream-queue/neary_woods_universal_duration_floor282.md)
gives282=139M+143A,262 certificate gates,7 comparisons,46 witnesses and
degree at most3980. Its input scale includes the duration, so one bound
is automatic; completeness retains valid-program synchronized padding.
The mask285 and loader288 parents remain reproducible.

The preceding [positive-mask-gap U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_mask_gap285.md)
gives **262 certificate /285=140M+145A polynomial operations**,
8 comparisons,47 positive witnesses and four positive program parameters,
with degree **at most3980**. Defining the mask above the quotient witness
removes one comparison and witness from the288 parent. The retained
mask-scale equation makes the restored bound slack positive at zeros;
the typed recoder proves the inverse mask gap positive. This is a positive
zero-set bijection with that parent, preserving its valid-program scope.
The low-degree option gives **295=140M+155A / degree at most608**,
257 certificate operations,13 comparisons and48 witnesses; keeping47
witnesses gives292/1344. The separate75/87 frontier is unchanged.

The preceding [loader-scale U9 polynomial](research-wip/native-stream-queue/neary_woods_universal_loader_scale288.md)
gives **262 certificate /288=141M+147A polynomial operations**,
9 comparisons,48 positive witnesses and four positive program parameters,
with degree **at most3980**. Defining the recoder scale from the paid
loader repunit removes one comparison and witness. Every positive new
tuple has a positive parent lift; completeness uses sufficiently long
leading-zero padding on valid U9 program slices. It is not an all-parent-zero
bijection or a completeness claim for arbitrary invalid program parameters.
The same rewrite gives **298=141M+157A / degree at most608**,257 certificate,
14 comparisons and49 witnesses; keeping48 witnesses gives295/1344.
The separate75/87 frontier is unchanged.

The [positive-scale291 parent](research-wip/native-stream-queue/neary_woods_universal_positive_scale291.md)
gives262 certificate / **291=142M+149A polynomial operations**,10 comparisons,
49 positive witnesses, four positive program parameters and degree at most3980.
Absorbing both native size bounds preserves positive zeros by an explicit
coordinate bijection, including the shifted joint-index branch.

The earlier [positive-scale grouping frontier](research-wip/native-stream-queue/neary_woods_universal_positive_scale_partitions.md)
adds **301=142M+159A / degree at most608**, with257 certificate operations,
15 comparisons and50 witnesses. Other50-witness choices include297/1142
and299/766. Keeping49 witnesses gives a separate frontier ending at
298/degree-at-most1344. The exact finite search optimizes operation count
and conservative degree bounds over sixteen bases; witness counts vary,
so this is not a three-objective optimum. All schedules preserve accepted
outer instances, not every supplied coupled-parent zero.

The [coupled297 parent](research-wip/native-stream-queue/neary_woods_universal_joint_and_coupled.md)
gives262 certificate / **297=144M+153A polynomial operations**,
12 comparisons,51 positive witnesses, four positive program parameters
and degree at most2311. It preserves the accepted outer relation through
sign recovery and a conditional positive restoration; the supplied
positive zero sets are not asserted identical. The earlier
[coupled partition frontier](research-wip/native-stream-queue/neary_woods_universal_joint_and_coupled_partitions.md)
includes301=142M+159A/degree-at-most1092,302=143M+159A/756 and
304=143M+161A/608, all with51 witnesses. The304 option has257 certificate
operations and16 comparisons; the subset search is exhaustive only for
its stated factor family and propagated degree bounds. The
[two-index301 parent](research-wip/native-stream-queue/neary_woods_universal_joint_and_arithmetic.md)
remains available at260 certificate operations,14 comparisons and degree
at most2475.
The earlier [grouped finalizers](research-wip/native-stream-queue/neary_woods_universal_joint_and_partitions.md)
give alternatives303=143M+160A with degree at most1522,
305=143M+162A with degree at most1144, and308=142M+166A with degree
at most1076, all with51 witnesses. The finite search optimizes the
propagated degree bounds only within its specified partition family.
The [earlier303 source](research-wip/native-stream-queue/neary_woods_universal_joint_and_units.md)
remains reproducible at degree at most2285. Its
[raw joint-AND parent](research-wip/native-stream-queue/neary_woods_universal_joint_and.md)
gives246 certificate /356=155M+201A,37 comparisons,64 witnesses and
degree at most580. These are upper bounds including all program coordinates.

A paid lower-output bound permits one native AND to replace the separate
recoder/history AND cores. Positive native extensions are rebuilt;
the complete outer relation is preserved without a bijection of all old
and new native tuples. The two remaining cores have one checksum.
The [377/379 predecessor](research-wip/native-stream-queue/neary_woods_universal_population377.md)
remains reproducible at66 witnesses and degree bounds2285/2241.

The [population-fusion obstruction](research-wip/native-stream-queue/native_population_and_fusion_obstruction.md)
shows why simply concatenating the remaining geometry index and truth
fields fails: excess field population compensates for the wrong width
on positive recoder tuples with x=1,z=2. Their full native extensions do
not supply an accepting fixed-tag history or false universal-polynomial zero.
The [Wang B tape component](research-wip/native-stream-queue/wang_b_single_and_tape.md)
provides a complete head/read/mark scalar graph in74 certificate /124
polynomial operations,24 witnesses and degree at most40. A finite-window
initialization of literal Wang input uses two gates after a paid initial
head/read predicate. The [packed tape successor](research-wip/native-stream-queue/wang_b_packed_tape.md)
pays arbitrary-duration chronological reads and optional marks in139
certificate /192 polynomial operations,18 comparisons,31 witnesses and
degree at most232. That packet does not pay head motion, control or TM
input coding.

The [Wang tape-and-motion batch](research-wip/native-stream-queue/wang_b_packed_motion.md) additionally pays
left/right/stay heads: **188 certificate /244=100M+144A polynomial**,
19 comparisons,35 witnesses and degree at most316. Its existential endpoint
projection is exactly non-erasing tape inclusion with dyadic initial/final
heads. That packet does not supply finite program control or TM-input coding.

The [chronological toggle-tape component](research-wip/native-stream-queue/langton_ant_packed_toggle_tape.md)
costs **105 certificate /158=66M+92A polynomial**,18 comparisons,28 witnesses
and degree at most124. A mixed native scale types both positive radices;
all free-head endpoint pairs are realizable. Ant turns/motion, its periodic
hardware background, the input perturbation and acceptance remain outside
the component. These paid histories do not establish universal bounds.

The [positive native-scale coordinate](research-wip/native-stream-queue/native_binary_positive_scale.md)
gives prescribed AND **64 certificate /108 polynomial**,15 comparisons,
21 witnesses and degree at most28. Its positive zero-set bijection gives
[Wang motion241](research-wip/native-stream-queue/wang_b_packed_motion_positive_scale.md)
with18 comparisons,34 witnesses and degree at most316, and
[toggle155](research-wip/native-stream-queue/langton_ant_packed_toggle_positive_scale.md)
with17 comparisons,27 witnesses and degree at most124; certificates stay188
and105. Computing [six already-paid native fields](research-wip/native-stream-queue/native_binary_computed_fields.md)
further gives **AND90/degree44**,9 comparisons,15 witnesses;
**motion223/degree-at-most696**,12 comparisons,28 witnesses; and
**toggle137/degree-at-most256**,11 comparisons,21 witnesses. Computing
four fields instead gives AND96/28, motion229/316 and toggle143/124.
All are complete component polynomials with the same endpoint relations;
no controller, ant geometry or ordinary-input interface is added.

The [normalized native-unit helper](research-wip/native-stream-queue/native_binary_norm_units.md)
further gives **AND83/degree-at-most124**,5 comparisons,15 witnesses;
**Wang motion216/2112**,8 comparisons,28 witnesses; and
**toggle130/778**,7 comparisons,21 witnesses. Ordinary-strong alternatives
84/86,217/1602 and131/584 preserve the root-coordinate zero-set bijection;
normalization instead rebuilds five native auxiliaries while preserving
all outer histories.

The [native index/coupled-unit successor](research-wip/native-stream-queue/native_binary_index_coupled_units.md)
gives complete **AND80=43M+37A**,72 certificate operations,3 comparisons,
15 witnesses and degree **at most124**. The same guarded rewrite gives
**motion213/degree-at-most2020**,6 comparisons,28 witnesses, and
**toggle127/748**,5 comparisons,21 witnesses. Index-only82 preserves the
parent positive zero set; coupling restores two private coordinates on
a negative index branch and preserves the outer relation. These are
complete components, with their control and geometry scope unchanged.

The [fixed-program Wang compiler](research-wip/native-stream-queue/wang_b_packed_program.md) now pays
chronological instruction selection, current-read jumps, both control
endpoints and the common duration. Its six-instruction example costs
**350=150M+200A**,13 comparisons,37 witnesses,degree at most3838 for
window endpoints. A two-gate literal binary-input loader and paid head
typing give **352=151M+201A**,13 comparisons,40 witnesses,degree at most5767.
These are complete fixed-program halting predicates. The example is not
a universal instruction table, and that packet does not instantiate a
TM-to-Wang input morphism; no new universal operation bound follows.

The [computed-action successor](research-wip/native-stream-queue/wang_b_computed_actions.md)
defines four action hats from the paid edge sums and folds their bound
contribution as2J-E_J+3. The positive graph bijection removes four
comparisons and four witnesses, preserving the same fixed-program relation.
The example now costs **331=146M+185A**,305 certificate operations,
9 comparisons,33 witnesses and degree at most3838 at window endpoints;
literal input gives **333=147M+186A**,307 certificate operations,
9 comparisons,36 witnesses and degree at most5767. No universal table or
TM-input encoding is added;350/352 remain the reproducible parent counts.

Applying the [native coupled-unit rewrite](research-wip/native-stream-queue/native_binary_index_coupled_units.md)
to that computed-action example gives literal-input **330=147M+183A**,
310 certificate operations,7 comparisons,36 witnesses and degree
**at most5503**. This is still an illustrative fixed Wang program.

The [non-erasing TM-to-Wang compiler](research-wip/native-stream-queue/wang_b_nonerasing_tm_compiler.md)
now pays the explicit Theorem7 instruction expansion and ordinary binary
input pair map for any fixed total non-erasing binary TM. Its example
with one nonhalting state gives **642=285M+357A**,566 certificate operations,25 comparisons,
83 positive witnesses and degree **at most16124**. The pair loader and
finite blank exterior are part of the complete theorem. This642 example
is not a universal bound; its non-erasing-machine scope remains unchanged.

The [finite erasing-TM record compiler](research-wip/native-stream-queue/wang_b_erasing_bridge_compiler.md)
now supplies the missing transition compiler for every fixed total binary
TM with a unique halt. It appends successive tape records using only
non-erasing writes and pays the exact framed ordinary-input loader.
The illustrative erasing machine produces1481 nonhalting binary states
and19254 Wang instructions; no fixed universal table/input slice is instantiated.

The [dependency-projection audit](research-wip/native-stream-queue/native_binary_dependency_projection.md)
materializes that complete illustrative polynomial at **312942=118706M+194236A**,
312866 certificate operations,25 comparisons,23763 positive witnesses and
degree **at most12092924**. Every emitted gate reaches the output.
Tracking only the dependency coordinates queried by two guards preserves
both guards and every returned arithmetic packet; it makes the literal
large build feasible. This actual source count supersedes the earlier
conservative312967 estimate for the example, not the universal75/87 bounds.

The [compact record compiler](research-wip/native-stream-queue/wang_b_erasing_bridge_compact.md)
now realizes the same illustrative machine at **41286=15648M+25638A**,
41210 certificate operations,25 comparisons,3153 witnesses and degree
**at most1581824**. Four-bit records, an exact control quotient and shorter
paired Wang macros give377 nonhalting binary states and2362 instructions.
The complete framed ordinary-input source is emitted and every gate
reaches its output. This improves the general finite compiler and example;
it does not instantiate a universal table or a new universal bound.

The [finite-game positive NOR compiler](research-wip/native-stream-queue/lattice_game_positive_nor.md)
forces exact Boolean outcomes on every fixed acyclic option graph with
one bilinear row per nonterminal. Its degree-at-most-four family grows
with the graph; no uniform lattice-game or ordinary-input bound follows.

That predecessor joins the [joint positive scale bound](research-wip/native-stream-queue/neary_woods_universal_population_joint_bound386.md),
[154-gate shared history](research-wip/native-stream-queue/neary_woods_universal_shared_history382.md)
and [padded checksum sign lemma](research-wip/native-stream-queue/neary_woods_universal_population_checksum387.md).
The [389-operation projections](research-wip/native-stream-queue/neary_woods_universal_population_projection389.md),
[395-operation bound deletion](research-wip/native-stream-queue/neary_woods_universal_population_bound395.md)
and [399-operation population parent](research-wip/native-stream-queue/neary_woods_universal_population_tag.md)
remain reproducible. The separate75/87 frontier is unchanged.
The [local target CRT theorem](research-wip/native-stream-queue/complete75_linear_strong87_target_crt.md)
realizes nearby wrong targets for a weakened auxiliary system, not full
polynomial zeros; the87-operation,degree183 candidate remains unresolved.
The [positive-index86 theorem](research-wip/native-stream-queue/complete75_weakened86_positive_index.md)
proves the unresolved86 candidate sound whenever its computed R>0,
without assuming alpha>Z. R=0 is impossible; the negative-R branch
remains unresolved. The [index-gap restrictions](research-wip/native-stream-queue/complete75_weakened86_index_gap.md)
prove the main Pell index p odd globally, with E<3p at zero wrap on
R<0,mu>0. The [gap-three exclusion](research-wip/native-stream-queue/complete75_weakened86_gap_three.md)
strengthens R<0,mu>0 to n<p<=2n-5 by excluding all237 necessary triples
at p=2n-3. The [gap-five successor](research-wip/native-stream-queue/complete75_weakened86_gap_five.md)
uses the exact main-root residue to force X=2^p and excludes all40
remaining triples, giving n<p<=2n-7. The
[gap-seven successor](research-wip/native-stream-queue/complete75_weakened86_gap_seven.md)
now gives **n<p<=2n-9**, excluding all96 power-of-two-X triples and all
three small-X lanes through exact input/main-root residues. The
[gap-nine successor](research-wip/native-stream-queue/complete75_weakened86_gap_nine.md) now gives
**n<p<=2n-11**:82 low-X lanes have uniform tail cutoffs;215 finite domains
leave one ratio-compatible case, excluded by all four wrap classes.
The [gap-eleven successor](research-wip/native-stream-queue/complete75_weakened86_gap_eleven.md)
now gives **n<p<=2n-13** on R<0,mu>0 by excluding all1,413 finite ratio
domains. Every fixed odd gap has a proved effective finite necessary-domain
reduction, but the gap remains unbounded. Gaps at least13 and mu<0 remain
unresolved;75/87 remain unchanged.
The [negative-input residue theorem](research-wip/native-stream-queue/complete75_weakened86_negative_input_residues.md)
classifies an exact finite subsystem for fixed main/first Pell data:
the negative input norm/discriminant, positive first-index slack, and
necessary auxiliary target congruence. Passing classes give subsystem
extensions, not full86 zeros. All20,160 necessary mask/offset/sign cases
at q=16,p=21,n=15,X=2^21,Y=8192 are excluded. That packet alone does
not reconstruct all candidate factors.
The [auxiliary-sign successor](research-wip/native-stream-queue/complete75_weakened86_auxiliary_sign_lift.md)
now proves that the exact allowed target residues are -p for p=1 mod4,
and +/-p for p=3 mod4, and constructs all five positive auxiliary fields.
Together with the CRT test, this gives a full negative-mu extension iff
for each fixed set of validated first/main and outer-transport data.
No passing actual outer tuple is supplied; those outer data remain
unbounded. No global mu<0 exclusion, new gap bound or universal86 proof
follows, and the86/19-witness/degree203 source is unchanged.

Native queue components retain their separate scope.

- Every displayed system, machine table and count of the six articles was
  re-derived by the checkers. The corrections to the printed articles are
  justified entry by entry in the editorial notes.
- The Lean 4 formalization in `../Lean/` (1974, 1976 §2–§3, 1978, 1982
  §2–§5, 1984 §2–§3) found no incorrect printed statement beyond those
  corrected; the proof details it had to supply are recorded as
  clarifications in the notes.
- The 1980 operation count `o = 100` is explained (the number of indicated
  `+`, `−`, `×` signs, exponentiation not counted), and Theorem 5 is given
  explicit, symbolically verified straight-line certificates. The satellite
  article reduces the count from 129 to 89 operations; the smallest complete
  certificate established since uses **75 operations (41 multiplications and
  34 additions/subtractions)**, with 30 positive existential witnesses and 19 equations
  ([`FIXED_RAW_UNIVERSAL_75_PROOF.md`](1980/FIXED_RAW_UNIVERSAL_75_PROOF.md),
  checked by `verification/explore_fixed_raw_universal_75.py`). The
  75-operation Rule 110 finite-history system still lacks a complete
  universal input and acceptance interface and is a separate component.

## Working rules

- Edit the `.tex` sources here in place.
- Record every change in `EDITORIAL_NOTES.md`, with the original pagination,
  before or with the commit that makes it, and bring the article's
  `jones<year>_editorial_notes.md` entry to the final state.
- Rebuild the PDF with the engine listed above (two passes) after any
  source change, and re-run the affected `round4_<year>_checks.py`.
- Keep the edition notice at the top of each `.tex` accurate.
