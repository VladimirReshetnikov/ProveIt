# Scoped review of batch-93 reciprocal notes and the Polish Lean-scope correction

The changed interfaces agree with the selected cited statements, subject to one missing hypothesis in a guide summary. The separate Polish correction accurately distinguishes characteristic-zero image/existence theorems from the field-general residue results and primitive definition. This is a publication/interface review, not certification of the complete manuscripts or their imported theorems.

## Immutable scope and evidence

Reviewed commits:

- `c70ced0ddd1e14e4116f6c5bef1f842ae99833fc`, parent `c127f4f637eb6353803df71ad15eda9563b28c90`: all 16 changed text-file raw diffs, including their before/after hunk context; eight changed PDF blobs authenticated only. This is eight changed article sources and eight guides spread across nine directories: the surcomplex analysis source changes without its guide, and the Hahn–Hilbert guide changes without its source.
- `b8bc36acc1f94bdc081b21a4d79b429b4f3acc27`, parent `a3932af19d04031cad57cafbedd0979d0401e801`: both changed text-file raw diffs and the PDF blob.

Together these are 27 changed files, 18 text files and nine PDFs, with 254 added and 21 removed text lines. The JSON pins each before/after Git blob, byte length and SHA256, the exact raw diff, all hunk ranges, and 100 human-read span records. The records include repeated/overlapping hunk context; they are not a count of distinct lines. Additional selected source reads are explicitly separated from whole-diff coverage. They include the relevant Polish and definable-surreal statement/proof interfaces, the complete first 290 lines of the Laurent-residue Lean file, and one complete formalization-ledger row. Search results outside these spans do not confer proof coverage.

The applicable `Algebra/SurrealNumbers/AGENTS.md` was read in full at c70; `docs/incoming/README.md` lines 421–440 supply the rebuild/retention rules. No supplied, archived, frozen, committed or copied predecessor program was executed or imported. Only the fresh metadata collector was run. No Lean, TeX, PDF or other build was run; no repository file was changed.

## Findings and retained correction

**R1 — restore the nonzero hypothesis in one guide summary.** At c70, `surreal/real-vector-space-structure/README.md` lines 258–262 summarizes the rank-one derivation as `aE` “with image `{g : ct(g/a) = 0}`” without restricting `a`. The changed article paragraph and the actual cited Polish Corollary `pma:bsd:cor:integration` (article lines 35767–35818) explicitly require `a != 0`. For `a = 0`, the derivation has image `{0}`, and the displayed division is undefined. The minimal repair is to insert “for nonzero a” before that image formula. This is a guide omission, not a defect in the cited theorem. The original omitted-hypothesis wording is retained here rather than silently discarded.

**R2 — b8 is a correct scope correction; retain the previous error and its counterexample.** The original guide said all five named items were “proved in Lean over every field.” The corresponding article remarks gave the same excessive scope. The corrected guide and article now put `exists_derivative_eq_iff` and `range_derivative_eq_ker_residue` under characteristic zero and leave `residue_derivative`, `residue_surjective`, and the termwise `primitive` definition field-general. This matches the actual source:

- `Surreal/Algebra/LaurentResidueChange.lean`: `[Field K]` at line 69; residue derivative and surjectivity at 183–197; `primitive` at 208–214; `section CharZero` and `[CharZero K]` at 216–218; the image/existence theorems at 233–248.
- The `FORMALIZATION.md` row at line 658 likewise distinguishes these scopes.

The false extension is concretely refuted in `F_2((X))`: the Laurent series `X` has residue zero, but the coefficient of `X` in the derivative of any Laurent series is `2 a_2 = 0`. Thus `X` has no primitive. The existence of a termwise `primitive` definition over every field does not imply that differentiating it recovers every residue-zero series. b8 itself replaces the wording without adding a historical counterexample remark; this review preserves both the old assertion and its failure as required by retention rule 11. A numbered source correction would make that record locally visible. No new error was found in the corrected declaration scope, and no new Lean-build result is claimed.

## Hypotheses checked in the reciprocal interfaces

The large-cardinal and across-universes additions correctly distinguish the earlier same-reals result from the cited extension to transitive models of ZFC. In the new statement, cuts use option sets in the smaller model, and summability/sums concern set-indexed families coded there. Elementarity is in the ordered-field language, formula by formula for class-sized fields, not in the language of set theory. Proper-inner-model support amplification still assumes a proper inner model; classification remains an open question. The first new birthday is a different invariant from the first ordinal outside a given finite-definition/parameter budget. The cited first-new-birthday cardinal argument was read through its conclusion; no stronger cofinality bound is inferred from it.

The selected normal-form proof explicitly imports the sign-expansion/normal-form theorem and distinguishes legal normal-form limits from arbitrary analytic limits or rearrangements. This review reads the repository's stated dependency and interface, not the external Gonshor, Bournez–Guilmant or Lipparini–Mezo sources. The Prikry discussion is conditional on its measurable-cardinal setup. The Namba statement uses the specified Laver-style tree presentation over `V=L`; the exact imported no-new-reals justification is still routed to the credited open question. The reciprocal prose does not turn that outstanding external/presentation obligation into a new proof.

The fixed-field notes retain “strong,” the real-and-ordinal fixed parameters, the distinction between adding the ordinal predicate and working without it, and finite formula/parameter tuples. The unrestricted non-strong classification remains open. Selected support-moving/Hahn-lift and definable-closure paragraphs were read; this is not an independent complete automorphism classification proof.

The Polish Borel interfaces use real coefficients and countable additive exponent subgroups of the reals. The matrix theorem is about left-finite fields with a uniform input cutoff for every bounded output range; the dual statement permits arbitrary weights only on an upper-bounded set of exponents. Neither is asserted as the same theorem for unrestricted full Hahn spaces. The logarithm/exponential correspondence requires a uniform positive gain. Its finite-cutoff coefficient argument and binomial-polynomial derivation proof were read. The Euler flows instead converge coefficientwise and need not converge as valuation-formal operator exponentials; the new reciprocal notes preserve this distinction. Rank-one integration needs the nonzero coefficient singled out in R1. The Hilbert guide refers to separable **real** Hilbert spaces and Borel translation-invariant total orders; it does not import that classification as a formalized surreal-Hilbert theorem.

These are infinite-series, descriptive-set-theoretic and class-field interfaces. No complete, fixed-arity ordinary-integer polynomial compiler, paid arithmetic ledger, or new finite witness bound follows from the changed notes.

## Labels, citations and verification limits

The ordered literal `\label{...}` / `\label[type]{...}` lists and ordered `\bibitem` key lists are unchanged in all nine changed article files. Counts below are literal source declarations, not `.aux` aliases or PDF destinations:

| Article directory | Labels | Bibliography keys |
|---|---:|---:|
| large-cardinal-embeddings-and-normal-forms | 323 | 30 |
| surreal-fields-across-universes | 286 | 24 |
| surcomplex/analysis | 426 | 44 |
| surcomplex-field-automorphisms | 229 | 19 |
| three-duals-of-hahn-vector-spaces | 77 | 11 |
| omnific-preserving-automorphisms | 729 | 27 |
| real-vector-space-structure | 249 | 25 |
| surreal-self-embeddings | 468 | 41 |
| polish-models-of-omnific-arithmetic (b8) | 1344 | 150 |

All 36 label-reference occurrences extracted from newly added article lines resolve to a literal declaration in the indexed immutable sources. This authenticates target presence, not rendered theorem numbering, the completeness of all Markdown links, or the proofs behind those labels. The README claim of 572 universe-report labels is not equated here with 286 literal source declarations; generated auxiliary aliases were not inspected. PDF page counts, build cleanliness and displayed reference numbers were not independently checked. No ancillary archive intake or byte-placement audit is part of these two commits' review.

## Frozen evidence pins

- Fresh collector `/tmp/review_reciprocal_c70ced0dd.py`: SHA256 `54d445aa245b50def87c0e1ddb6959281cca30ef39672b77a15dbacb40407494`.
- Receipt `/tmp/review_reciprocal_c70ced0dd.json`: SHA256 `e1b112cf454b61783078b57d8fc145a7ed6dff59820104510615f63dfd02b010`.

The collector contains no report-code imports and reads immutable Git objects only. Its one fresh execution produced the recorded pins, unchanged-label/key results and zero unresolved indexed label references. The review's mathematical conclusions are the bounded source-reading assessment above, not a result of executing a manuscript verifier.
