# Corrected conservative signal frontend: full review

Review conclusion: the corrected release preserves the reviewed valid formulas, repairs the three previous malformed-boundary defects, and passes every original author entrypoint. No new valid-domain mathematical defect was found. Its universal physical frontend and its external-horizon polynomial families must remain separate claims.

## Archive and scope

Arrival `aebfa386e` / `ef2fc7990`; archive `docs/incoming/Conservative_Signal_Frontend_Corrected.zip`, SHA-256 **`e2acf725fcf017e14b2705cc9097fa9e3eb8b02c2fc9faf8ce486d3614816990`**. All 45 members are individually pinned in the companion checker. Safe private extraction rejected absolute/traversing paths and symlinks; the original ZIP was never changed.

Read the complete article, proof/ledger, correction note, executable Python sources, source-provenance and replay/build scripts. Compared the entire archive with `Conservative_Signal_Diophantine_Frontend.zip` (`43eaf888d4d93942ab7cf311bcc2f53a1853efa0715805fb13cd14d706fa6f73`): 36 old members are byte-identical, two changed (`SHA256SUMS`, `code/quadratic_packet.py`), seven are new, and none were removed. The corrected evaluator SHA-256 is `96d4c2b634d465dfcd4df421d57d7f71da44efa201d00fa2518660e600507eef`, exactly the previously reviewed repair. The bundled patch SHA-256 `c811f6e552531f614e1fcaefffc9a296d313fe80a94a3e65aa4cf033306f2033` matches the preserved `conservative_signal_packet_domains.patch`.

The earlier complete review remains relevant: `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_conservative_signal_2a8a39599.md`. This review reread the source/proof rather than inferring correctness from that comparison.

## What is proved and what is not

The literal machine has 18 particles, 114 meta-signals and 445 binary collision rules; its source table has 62 transition quintuples. The report distinguishes accepting `(q1,b)`, the null `(q2,$)` pair, and 26 undefined cells. Reversibility does not make every undefined collision legal. Finite binary stack words are rational encodings with blank tails, not arbitrary real interval points or an infinite oracle word. The separate binary construction gives an existence bound of ten particles, not an emitted ten-particle literal universal table.

For the printed machine, the finite mode closure has 49,700 modes and 80,501 candidate branches. Mode reachability overapproximates geometric feasibility. The reported depth 321 is a breadth-first mode-graph statistic, not a runtime bound. Exact first-event guards exclude missed earlier collisions, include precisely the chosen simultaneous collisions, and rule out invalid neighboring selected pairs. Mode coding is checked at input and output; the source scalar multiplier is positive. Every active gap is an exact integer-scaled rational event result. Stationary endpoints imply the span scales by the positive pivot speed (at least 3 here); exact bounded target reachability and unbounded accepting-cone universality therefore do not conflict.

The original one-step certificate has 4,196,998 auxiliaries, 2,762,961 squared affine residuals and 80,501 products, degree two. Concatenation has `4,197,016 K − 18` witnesses for external horizon K. K is not an existential witness of one fixed-arity polynomial. No fully charged ordinary binary loader into this enormous event packet is supplied; no improvement over the universal 87-operation benchmark follows.

The source-dependent literature claims were checked against the previously audited primary sources and their explicit limitations. [Durand-Lose 2012](https://www.univ-orleans.fr/lifo/Members/Jerome.Durand-Lose/Recherche/Publications/2012_IJUC_UC_HC.pdf) supplies the conservative reversible rational signal-stack construction. The printed table is attributed to [Morita 2008](https://hiroshima.repo.nii.ac.jp/record/2008964/files/TCS_395_101.pdf); this review does not claim a newly retrieved independent visual transcription of that PDF. The [1989 publisher record](https://globals.ieice.org/en_transactions/transactions/10.1587/e72-e_3_223/_p) supports the cited binary existence result; its unavailable full text remains a qualification, as in the earlier review.

## Replays and correction

All ten original author entrypoints passed in an isolated copy: the seven `code/` scripts named in `run-replay.sh`, `numeric/compile_packet.py verify`, `numeric/test_exporter.py`, and `numeric/check_original_replays.py`. All 45 shipped members remained byte-identical. The three correction runs (normal, `python -O`, and comparison with the original evaluator) each passed: 1,200 full-formula preservation cases, 72 canonical sections, 66 malformed-call rejections, immutable snapshot and signed branch-algebra checks. The old identity packet wrongly accepted surplus output `(1,999)`, floating input `1.0`, and an extra `(None,)` slack row; the corrected evaluator rejects each.

The default review checker separately verifies every original member hash, reconstructs the complete numeric closure, checks one explicit integral event/section for **every** branch, checks 130 signed/natural local graph identities, and independently tests the corrected public boundary. It does not expand the trillion-term dense polynomial. The separate `--author` option reruns the full author entrypoints in temporary copies.

## A natural-domain guard projection with a paid schedule

Write `c_i=v_i−v_(i+1)`, choose pivot j with `c_j>0`, and let J be the selected collision edges. Keep the mode equality, all selected-edge tie equalities, `h_j>0`, and `c_j h_i−c_i h_j>0` for unselected edges with `c_i>=0`. Delete all `germ:i` rows, the span row, and unselected `first:i` rows with `c_i<0`.

This is a complete natural-zero projection, not an equality between the two polynomials on unchanged coordinates. The retained one-hot and complementarity rows still give one active copy and zero inactive copies. In the active copy: selected ties imply `h_i=(c_i/c_j)h_j>0`; retained first-event rows for other `c_i>=0` imply `h_i>0`; for `c_i<0`, the deleted first-event form is automatically positive since `h_i>=0,h_j>0`. The span is positive because `h_j>0`. Natural integrality makes every positive deleted form at least one. Restore its slack uniquely by `s=L(copy)−e`. In inactive branches both copy and selector vanish, so every restored slack is zero. Forgetting and restoring these coordinates are mutually inverse on complete natural zero sets. Over arbitrary signed tuples the same affine section makes the deleted squared residuals identically zero; the remaining complete polynomial is unchanged under that section.

This argument does **not** preserve nonnegative-real fibers: a selected gap may lie strictly between zero and one, giving a negative restored old `germ` slack. The checker saves an actual-branch rational counterexample. The real positivity argument still proves the physical guard, but does not prove the old integer-unit slack representation over reals.

Exactly 18 rows and slack coordinates disappear per branch: 1,233,405 germ rows, 80,501 span rows and 135,112 negative-closing-speed first-event rows. Consequently:

| Component | Original | Reduced |
|---|---:|---:|
| Strict rows / slacks | 2,667,479 | 1,218,461 |
| One-step witnesses | 4,196,998 | 2,747,980 |
| Squared affine rows | 2,762,961 | 1,313,943 |
| Complementarity products | 80,501 | 80,501 |
| Degree | 2 | 2 |

The reduced concatenation count is `2,747,998 K − 18`, still external-horizon.

A fully specified sparse-affine schedule computes each affine row once, using one multiplication for each coefficient with absolute value greater than one, unit coefficients by additions/subtractions, and one multiplication per square. Cache the selector sum E from the one-hot row. Each complementarity term costs 17 additions to sum its 18 copy coordinates, one subtraction `E−e`, and one multiplication. Accumulate every square and product with one fewer addition than the number of terms. Each literal row has a positive term, so no uncharged initial negation is needed. This schedule is charged from every actual emitted source coefficient; no exponentiation oracle or free coefficient scaling is used.

| Complete one-step schedule | M | A | M+A |
|---|---:|---:|---:|
| Original | 8,539,514 | 16,853,008 | 25,392,522 |
| Reduced | 6,820,272 | 11,082,826 | 17,903,098 |

The saving is **7,489,424 operations** in this explicit family/schedule. The checker audits 15,323,489→9,553,307 affine coefficient incidences and 5,696,052→5,425,828 nonunit coefficient multiplications. It has not stored a 25-million-gate straight-line file, optimized all sharing, or supplied an unbounded fixed-arity compiler.
