# Bounded semantic transfer review: Part XVII at f97814421

**PASS: no substantive mathematical or scope drift found in this integration.** The new Part XVII preserves both source manuscripts' formal statements, proofs and displayed mathematics, while explicitly distinguishing fixed bases from input bases, power-assisted certificates from ordinary quartics, and fixed phases from arbitrary branching. Its descriptions of the existing executable defects and unapplied repairs agree with the pinned research review.

This review is confined to commit `f97814421444abae15b469eb30c7343d03c65394`. It is a source/typesetting transfer audit, not a renewed proof audit of the whole collection or a replay of unchanged programs. The delivered report files were not changed; this review packet is maintained separately.

## Source identity and reproducible preservation

The actual second source is **`Spectral_Guards_Without_Time_Expansion.zip`**, with inner directory `Spectral_Guards`; there is no need to infer a differently named “Spectral_Guards_Diophantine” package. Both original articles were obtained directly from their authenticated archive objects at arrival commit `060e08a07`, not from a later working tree.

| Source | Archive SHA-256 | Article SHA-256 |
|---|---|---|
| Positive Spectrum | `fe519471be068a0f7f5822c2fd89f1767f15d60379fb8d06d4b7b87f994dfdf8` | `ffe039f42d006c97010b0ce626b67c8cd377225b3112f6311e9d95be7c9a19ba` |
| Spectral Guards | `0a5cf2d12333bab718453e1139622518f55b6361bd0e947f47d8e748d06f9e53` | `66800a6a5bc739300d263fa14481e45fc250327c8418b5d179e439be09ed4c37` |

The integrated `article.tex` is SHA-256 `40884764d49946d7cba6db3cfb2086aa0d3f1647ed206167e812cadede10c8a5`; its README is `7f7a6ca3496076f6114c0c26ec79553861bb4ed28616449500232b329051ba0b`.

The [portable checker](review_signcharts_f97814421.py) and [receipt](review_signcharts_f97814421.json) establish:

- **79 complete formal environment occurrences** preserved in their own manuscript's core: Positive Spectrum has 9 theorems, 7 lemmas, 2 propositions, 4 corollaries, 3 definitions and 21 proofs; Spectral Guards has 6 theorems, 4 lemmas, 2 propositions, 3 corollaries, 3 definitions and 15 proofs.
- **91 displayed formula block occurrences** preserved, including the source introductions and appendices: 46 from Positive Spectrum and 45 from Spectral Guards.
- All **114 source labels** preserved under their declared prefixes, 63 `cdc:ps:` and 51 `cdc:sg:`. The collection grows from 1,179 to 1,322 labels: the 114 source labels plus 29 editorial labels. No previous label is removed, and no target label is duplicated. All 249 reference occurrences in the new core resolve.
- All **29 placed non-manuscript files** from the two packages are byte-identical to their archive members: 13 Positive and 16 Spectral files. Thus the disclosures that the original code remains unpatched are accurate at this commit.
- The four prominently compared export interfaces agree with the actual JSON arrays, without executing either exporter or checker: Positive finite `(7 inputs,1231 witnesses,1703 residuals,52 atoms,7502 monomials)`, Positive infinite `(6,1297,1767,52,8256)`, Spectral power-assisted `(10,1294,1212,104)`, and Spectral bounded-bit `(10,1935,1995,0)`.

Normalization removes comments, whitespace, label/source wrapper commands and the added label prefixes, and applies the explicitly recorded bibliography-key renamings. It does not discard hypotheses, conclusion clauses, proof steps or arithmetic expressions. Citation keys are mapped explicitly rather than erased. Each formal environment occurrence consumes a distinct matching occurrence within its own manuscript's core, so neither an unrelated theorem elsewhere nor reuse of one matching occurrence can supply the match. Displayed formulas likewise consume distinct target occurrences from a shared pool for both sources; they are compared in the whole integrated article because the introductions and appendices were relocated. The receipt records original and integrated line numbers and a digest for every formal and displayed occurrence. Thus the stated 79/91 counts preserve multiplicities, not merely sets of formula values.

This verifies label preservation, not compiled theorem-number stability. I did not rebuild LaTeX, inspect the PDF layout, or independently reproduce the claimed clean 509-page build.

## Added editorial relations

I read the new source/scope and conventions section at article lines 24,040–24,084, the inserted relations beside the individual results, the comparison at lines 26,400–26,427, the merged and cross-referenced question lists, conclusions and provenance, the new introductions, the dated notes beside earlier results, and the corresponding README additions. I also checked the retained verifier conditions V1–V5 and the finite pair-intersection interface against the source text, rather than relying solely on theorem titles.

The following comparisons are correctly qualified:

1. **Base 1 and Part IV.** `E−1` is the forward difference. The merge explicitly notes that Part IV stops at a constant row, whereas these ladders add a zero row: `D²` versus `D²+1` slots. It therefore does not silently identify the complete coordinate interfaces. Base 1 needs no power atom and gives the earlier ordinary polynomial-trajectory specialization. The unipotent and unitriangular comparisons preserve the distinction between eigenvalue/diagonal 1 and general positive values.
2. **Two implementations of the endpoint method.** The shared-endpoint fixed-base implementation gives the source's `O(D³)` bound; the input-base, all-pairs implementation gives `O(D⁴)` and its exact `Q_D` formula. The new comparison does not claim that the second implementation has already been reduced to cubic size. The merged question explicitly leaves the canonical merge problem open. These are the stated shaped arithmetic systems, not fully paid ordinary universal-polynomial ledgers.
3. **Finite versus infinite horizons.** Positive Spectrum uses the coefficient-determined eventual sign in V5, without a guessed threshold. Spectral Guards uses its explicit threshold and a finite chart. The source's qualification that the latter all-time frontend is proved by composition but not separately exported survives. Integer-time signs are not replaced by real-interval positivity.
4. **Power atoms and bounded-bit quartics.** The merged text retains the power atoms in the horizon-independent systems. Ordinary quartics fix B in the syntax and restrict `T<2^B`; B is not silently treated as another input to the same finite circuit. The counted witnesses can have enormous bit lengths. No source or editorial note converts the residual-only quartic into a complete ordinary equation while forgetting its atoms.
5. **The order-two equivalence.** The dated note beside `cdc:pt:prop:exponential-boundary` at line 8,779 and the comparison at line 26,423 correctly sharpen an implication to the source's equivalence for the *specific complete chart graph of* `2^n−y`. They do not claim a lower bound for every order-two recurrence, or a solution of the single-fold/finite-fold problem. The ordinary bounded-bit family does not conflict with the uniform-in-horizon boundary.
6. **Universal-language and phase scope.** Repetition counts are supplied for fixed phases. The explicit warning at line 24,991 says that existentially quantifying the counts can destroy uniqueness. Neither compiler handles unbounded switching among phases for free. The rational-base discussion retains the warning that multiplying a sequence by a positive time-dependent factor preserves signs but need not preserve its minimizer.
7. **Oscillation.** The second manuscript strengthens the raw-profile obstruction to every fixed residue class of the specified rotation sequence. The merge keeps it an obstruction to that chart format, not to all Diophantine certificates or to decidability in general.

The earlier-part comparisons were read only where the new editorial notes invoke them; this was not a new audit of Parts I–XVI. The proposed question mergers preserve the original open-question texts and do not convert a conditional transfer into a claimed solved problem.

## Existing reviews, repairs and the Presburger atom

The record actually cited by the merge is the WIP `review_spectral_060e08a07.md`, whose target-commit SHA-256 is `12e55ea414a0c2e2e64f6220ff7acf78c2893ec3c61d1346ab687713e871eb76`. The integration's disclosure agrees with it: the Positive constructor/verifier accepts an unauthenticated supplied ladder, cached coefficients can be mutated, and the two-point exported-quartic test is not a polynomial identity test. The Spectral serialized checker has exact-type/index boundary defects. The merge retains the source wording but immediately adds the explicit correction to the two-point claim at line 25,372, and identifies both tested patches as **not applied**. This transfer PASS does not imply those public API defects are repaired.

The cited Lean files, `Paper1984/DPR.lean` and `Common/DiophantineTrace.lean`, are byte-identical between the source pin `e58b724c25bd34533b7a5834cfcbe873dfa01288` and the target commit. Their claimed roles remain separate: the former supplies the existing single-fold *exponential* normal form; the latter is existence-level iteration context. No new sign-chart theorem has thereby been kernel-checked.

I also confirmed the actual maintained Presburger comparison artifact, rather than inferring it from its filename. `presburger_congruence_five.py` at this commit has SHA-256 `f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc`, exactly the source pinned by `review_presburger_congruence_five.md`. Its five natural coordinates implement one fixed-modulus congruence truth atom on an already evaluated signed affine input, with five quadratic residuals and a displayed 21-operation isolated SOS schedule. The sixth remainder coordinate is restored by `a=b(s+1)`, giving the recorded full graph identity. This is a decidable fixed-Presburger-component optimization; it neither represents unbounded powers nor pays the sign-chart endpoints, surrounding Boolean circuit or complete ordinary finalizer. Part XVII makes no contrary claim and does not claim to have integrated that atom. Its source, receipt and independent review are pinned in this audit solely as existing research context; none was rerun.

No new reduction of the 87-operation universal polynomial follows from this typesetting integration. The two reports' useful transfer remains the previously reviewed endpoint-sharing mechanism with all power, shape and phase obligations exposed.

## Reproduce this bounded audit

```
python review_signcharts_f97814421.py \
  --repo /path/to/Proofs \
  --output fresh_signcharts_review.json \
  --expect review_signcharts_f97814421.json
```

The helper uses read-only Git object access at the fixed target and source commits, authenticates both archive byte streams, and compares exact typed receipts. It imports no report code, runs no author checks, and writes only the explicitly selected output. A fresh replay matches the saved receipt. Future commits, PDF visual quality, complete old-collection mathematics and a new literature-priority search are outside this audit.

Root reproduced the fresh occurrence-preserving receipt from the frozen helper and obtained the same 79 formal blocks, 91 displays and 29 byte-identical companions. This replay imports no author code and does not imply a PDF rebuild.
