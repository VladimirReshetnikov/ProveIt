# Two discrete/asymptotic reports at e88ed8bf6: bounded intake

Both reports provide useful exact finite combinatorics and asymptotic interfaces, but neither supplies a Turing-universal simulation or a paid ordinary-integer Diophantine compiler in the inspected material. Here **Borel completion means analytic Borel–Laplace summation**, not a descriptive-set-theoretic Borel presentation. The manuscript scopes explicitly prevent several tempting transfers: an analytic completion's recurrence is not the integer sequence's recurrence; fixed-order expansions do not automatically give growing-order counting errors; eventual index rounding is not a stated finite numerical threshold.

No concrete mathematical defect was found in the selected interfaces below. This is a bounded intake, not certification of all analytic or combinatorial proofs. The global growth, uniform remainder, sensitivity and short-path theorems were not fully audited. Their open continuations remain open with their original attribution.

## Immutable provenance

Commit `e88ed8bf6b349e63c0bb3e3ab146c582275ec0d9`, parent `ff6e95f4f41d812dceecba07ca2fe6820ece360a`. Both archives are new at that commit.

| Archive under docs/incoming | Git blob | Bytes | SHA256 |
|---|---|---:|---|
| `ProveIt_A189281_Borel_Completion.zip` | `c626d887feda2227acf7270e6db32a7724875d02` | 542661 | `64898f6a992021400f3e757f9921c3cff67560eec09ae7532fa6f46dec15e0c3` |
| `ProveIt_Moving_Gap_Permutations.zip` | `e952fd45dcc4d62b720293321f59c6d4992af0d7` | 538400 | `c2a78ce70a4e365b1678c283e55549a8433b5efb87ca682c8f61c86a812151d3` |

The fresh collector inventories and hashes all **37 regular members** (16+21), including compressed sizes and CRCs. All **35 shipped checksum entries** match and cover every regular member except the two manifests themselves. PDFs, supplied programs/builders and saved numerical/exact evidence are authenticated as bytes only; no delivered program was executed or imported, and no PDF was read or built.

The manuscript hashes are:

- `ProveIt_A189281_Borel_Completion/article.tex`: `cbe447928ea93cc29ec004218120c5bcf3f970b6eca89bf4a9744975af135462`, 1,505 lines.
- `Moving_Gap_Permutations/article.tex`: `0594efc8e69b601611086c51719ddb04f199c7a7ddd188c11cc061fc893480c3`, 1,968 lines.

The literal label inventories contain 98 and 138 labels, respectively, with no duplicated labels or unresolved recognized simple reference targets. This is a regular-expression census, not a TeX build or general macro parser.

Both provenance notes name the existing host `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions/`. Their two inspected revisions, `79e7aab60ee856862b36c38cf32cfdb1be95313f` and `d1680cdfa40c44abf0825416b6f36a3e9ec2662c`, really contain the same article blob `73a53d9784260c2f0d083f2baa62a5535f6d6105`. The first report's cited guide blob `59ad8b15b9522102e1f6d48f68c1db358a3ac044` also matches. These pins authenticate the cited repository context, not the authors' external-paper readings or priority claims.

## Exact reading scope

All spans below are inclusive, with exact line-terminator-preserving UTF-8 hashes in the companion JSON.

Both complete delivery guides were read: Borel README 1–126 and moving-gap README 1–87 (213 lines). Both complete provenance notes were read: Borel SOURCES 1–119 and moving-gap SOURCES 1–61 (180 lines).

| Manuscript | Inclusive spans read | Purpose |
|---|---|---|
| Borel completion | 101–215 | Counting model, credited prior inputs, scope and source pin |
| Borel completion | 434–509 | Definition and domain of the analytic completion, fixed-order expansion and quadrature |
| Borel completion | 754–789 | Non-P-recursiveness argument and explicit distinction between coefficient array/counts/completion |
| Borel completion | 870–1088 | Differential/shift equations, factorization certificate and four-index arithmetic obstruction |
| Borel completion | 1115–1238 | Smooth inverse, finite enumeration, test claims and limits |
| Borel completion | 1293–1438 | All ten further questions, conclusion, exact tiling proof and numerical conventions |
| Moving gaps | 196–474 | Model, main statement, exact profiles, geometry-independent moment bound and connected local placements |
| Moving gaps | 516–629 | Finite extraction/locality formula and its proof |
| Moving gaps | 1300–1390 | Exact path-polynomial and formal logarithmic coefficient algorithm |
| Moving gaps | 1447–1711 | Bonferroni/rational enclosures, reported checks and all-orders index reconstruction |
| Moving gaps | 1746–1914 | All eight further questions, declared dependencies, reproducibility and non-claims |

These are 716+918=**1,634 manuscript lines**, not full manuscript reads. In particular, the Borel paper's global Dawson/complex-growth and growing-order truncation proofs, and the moving-gap paper's uniform-remainder, sensitivity and short-path proofs, remain outside this audit. A selected argument using one of those theorems is reviewed relative to that stated dependency.

For prior context, article 3247–3297 was read at the first pinned revision: the entire-transform theorem expressly disclaims Laplace summability and recovery of flat sectors. Article 2260–2325 was read at the second pin: it lists the growing-gap, short-path, multigap and effective-threshold questions. No previous report helper was executed, and the earlier article was not reviewed wholesale. Its guide was pinned only, not human-read for this triage.

The standing retention rule at `docs/incoming/README.md` 426–442 was read. The immutable repository AGENTS inventory contains no applicable ancestor instruction file for the declared SetTheory/Cardinals host. No source claim was removed or silently elevated from a question into a theorem.

## A189281 Borel completion: useful boundary, not an integer recurrence compiler

The report studies the directed gap-(2,2) permutation count `a_n`. It takes the earlier fixed-order expansion and explicit auxiliary formal series as credited inputs. The analytic functions `C*(n)` and `A*(n)=Gamma(n+1) C*(n)/e` are defined by a particular positive-ray Laplace prescription on `Re(n)>1`. This prescription is not a unique recovery operation for all functions or integer sequences with that algebraic asymptotic expansion.

The selected shift calculation is internally consistent. Starting from the displayed differential equation and its justified Laplace transform, the report obtains a rationally forced recurrence for `C*`. After Gamma normalization, its rightmost operator satisfies

`(T A*)(n)=Gamma(n−1) Q(n)/(2e)`.

A fresh, independent integer-polynomial check verifies three displayed formal expansions: the stated Q from the rational forcing, the stated P after applying U, and the full zero polynomial obtained from V. The check was written from the displayed formulas and does not call, import or copy the delivered factor-certificate program. It does not certify the analytic growth estimates needed for the Laplace manipulations or turn these identities into a recurrence for `a_n`.

The nearby arithmetic obstruction is sound conditional on that analytic identity. If `A*(m),…,A*(m+3)` all equalled the integer counts, the rational-coefficient expression `(T A*)(m)` would be rational. But it equals `(m−2)! Q(m)/(2e)`, with a nonzero integer numerator for `m>=2`. Irrationality of e gives a contradiction. Thus the analytic completion cannot silently replace the integer sequence, even after finitely many initial terms are ignored. Flatness of their discrepancy separately uses both fixed-order asymptotic theorems; this audit does not reprove the global analytic premise.

The non-P-recursiveness argument for the correction coefficients is also valid relative to the stated infinite-order growth theorem for the entire Borel transform. Factorial rescaling preserves P-recursiveness, while an entire solution of a polynomial differential equation has finite order by a rational first-order-system/Gronwall bound. The result concerns the asymptotic coefficient array, **not** noncomputability, Turing universality or a theorem that the original counts are non-P-recursive. The report states these distinctions explicitly.

Exact counting by matching tilings is a terminating combinatorial procedure for each finite n. The supplied implementation's partition enumeration and its saved small permutation checks are evidence claims here; they were not rerun. Their operation count and storage grow with n, and no fixed paid straight-line integer graph or unbounded computation-history encoding is supplied.

The smooth inverse and eventual nearest-integer conclusion apply to actual sequence values on a final interval. They use asymptotic error and special real functions, not an explicit numerical onset or a declared finite-precision cost model. The paper leaves the integer-count recurrence, leading flat term, exponential counting error and full transseries as questions. Those are genuine additional proof obligations; the verified polynomial forcing alone does not settle them.

## Moving-gap permutations: finite local algebra with order-dependent size

Here “universal polynomials” means coefficients uniform over all pairs of actual path forests. It is not a universal machine claim. The model is one source path forest and one target path forest, with directed or absolute edge violations under a random bijection. It explicitly excludes arbitrary simultaneous colored constraints and cycles.

The selected exact profile proof correctly permits unselected violations: marked source rods are paired with disjoint target rods of the same lengths, orientations and equal-size matchings are counted, and the remaining vertices are freely bijected. This gives an exact rational factorial-moment formula. The elementary moment bound has a constant independent of component geometry; the proof uses the falling-factorial lower bound and counts source edge subsets.

The connected-overlap construction and selected locality proof supply a finite rational coefficient algorithm at each chosen order J. Connected placements span at most their total rod edge weight. Merger cost bounds the number of marked rods, leaving arbitrary unmarked unit rods to exponentiate. After removing the leading exponential, the coefficient has degree at most 2J and uses densities through edge length J+1. The cancellation argument is polynomial and does not divide by the leading edge densities, so zero-density cases are not lost. The exact path recurrence and second-difference logarithms supply an alternative finite implementation of the same coefficient interface.

This is meaningful effective finite algebra on explicitly supplied rational forest densities. Its intermediate weight bound is 2M when computing through order M; the number of variables, profiles, polynomial coefficients and rational operations is not fixed as M grows. No charged arithmetic ledger, fixed witness interface, integer input loader or simulation of arbitrary programs is given. It would be incorrect to infer a fixed-arity universal Diophantine evaluator merely from the word “finite.” Conversely, this review does not claim that some separate encoding theorem is impossible; none is constructed here.

The Bonferroni inequalities and exponential Taylor-tail enclosure are valid rational certificate mechanisms for fixed finite inputs. Their printed interval values and 3,209 delivered assertions were not independently reproduced. The inverse diagnostics are explicitly not interval certificates; broad reproducibility wording must be read with that distinction. The uniform all-orders remainder proof is outside the selected read, so this report does not certify all-size bounds from the four printed numerical intervals.

The inverse proof works along a fixed rational gap ray and actual sequence values. Formal recursive correction coefficients and the mean-value residual estimate yield eventual rounding to a multiple of the ray denominator, conditional on the main asymptotic theorem. The paper supplies no numerical threshold and explicitly leaves usable constants and certified onset as a research question. Inversion of arbitrary thresholds would need an additional staircase convention. These are appropriate declared limitations, not missing hypotheses silently supplied by this review.

## Result, priority and validation limits

For the current computational-substrate search these are **secondary analytic/combinatorial tools**, with no direct paid-compiler reduction found. The most reusable finite interface is the moving-gap coefficient/Bonferroni mechanism; the most important warning is the Borel paper's exact proof that a preferred analytic completion need not equal the integer counts. Neither warrants a Turing-completeness conclusion. A negative conclusion about all possible future encodings is not claimed.

Only the fresh `triage_discrete_e88ed8bf6.py` was executed. It authenticates Git/ZIP/member/manifest/source pins and exact read spans, inventories literal labels, and proves the three finite polynomial identities described above by new integer arithmetic. Fresh normal and optimized exact receipt replays passed from `/` before freezing. The supplied test totals, interval values, numerical precision claims, external source inspections and historical novelty remain attributed statements. No external literature, PDF, full proof, Lean development or supplied execution was certified, and no repository/Git mutation occurred.
