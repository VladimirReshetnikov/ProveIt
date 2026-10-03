# Batch 79 catalogue and reciprocal notes: bounded semantic review

Four new prose issues need correction. The new comparison of natural and nonnegative-real signal witnesses is sound for nonzero natural input; its zero-input caveat overlooks the complete packet's disjoint-branch hypothesis. None of these findings refutes the reused certificate constructions or changes an arithmetic ledger.

Scope is exactly `abfc0cb2524aa221a7e110f6dacc8f1fb8b60e65..37652b3e60a676e119746f5b874147cb4d9e1d2b`: the catalogue commit `ca62e1488bbee0e7f9f16c3455ea250f495fe0c6`, reciprocal-notes commit `bbc67d225e96a80a94b7d7a3c9a42f4c93e23cca`, and incoming-index update. All changed text in fourteen files was read, including the new catalogue entries and all 68 added TeX lines in the four reports. I consulted the previously reviewed constructions and the original theorem context needed by these comparisons. This is not a fresh proof audit of every catalogue theorem, a source-suite replay, a PDF/build review, or an audit of later commits.

## Findings confined to this diff

1. **P3 — the polynomial-witness catalogue calls the univariate construction linear.** `SetTheory/Cardinals/docs/reports/README.md:512` describes all three manuscripts as unique linear certificates over `N[X,Y]`, `N[X]`, or any commutative ring. The second manuscript instead proves the bounded-coefficient obstruction to a universal linear univariate compiler and gives eleven **quadratic** identities sharing one stride. The third assumes a **nonzero** commutative ring. The new manifest already states both distinctions correctly. The patch makes the short README agree with it.

2. **P3 — the quadratic-report catalogue retains a now-false “Each Part” degree assertion.** `SetTheory/Cardinals/docs/reports/manifest.tex:3827` says every Part has degree two, while its newly added Part IV description at line 3851 correctly specifies a quartic sum of squares of quadratic residuals. The opening sentence predates this diff, but this diff newly extends its referent to six Parts; the resulting contradiction is new. The patch lists Parts I–III, V and VI as quadratic and Part IV as quartic.

3. **P3 — the reciprocal PQC summary names the optional lift as the compiled lift.** `probabilistic-quantum-and-continuous-computation/article.tex:16137` says the signal packet uses a uniform common denominator. The actual printed integer map uses the positive pivot speed of the selected branch, with scale `lambda_(k+1)=c_j lambda_k`; the uniform `QD^k` construction is explicitly an alternative (`signal-machine-collision-certificates/article.tex:2780–2826`). The patch states both conventions. It also makes explicit the disjoint integer-linear **partial** branch system and repairs the newly added PQC README line 945's “one natural zero” comparison: the signal endpoint fibre can be empty, while the unconditioned clipped-network trace always exists. No undefined collision or terminated signal trajectory is silently totalized.

4. **P3 — distinguish the weak gates alone from the full packet at zero input.** The new quadratic-report note at `quadratic-orthant-certificates/article.tex:4740` and signal README at line 562 describe a fractional-selector exception at `X=0`. That exception is possible for the isolated weak gates, but not for the complete packet under the explicitly stated disjoint homogeneous branch hypothesis. The new signal article paragraph at line 2933 partly protects its claim with “gates alone”; its conclusion and reciprocal summaries should carry that qualification consistently. The patch explains the full zero-input argument without changing the original natural-only theorem.

For the fourth finding, the code-independent proof is short. At a nonnegative-real zero with natural input `X`, every nonnegative summand vanishes. If two selectors are positive, every complementarity first factor is positive, so every local copy vanishes and therefore `X=0`. For `X!=0` the selector is consequently one-hot, the active copy equals `X`, and integer guard forms force all slacks and outputs integral. At `X=0`, the input-copy equations already force every copy to vanish. A strict guard becomes `-b_r-s=0`, forcing its selector to zero. Every branch with only homogeneous weak/equality guards contains zero. Disjointness **on `N^d`, including zero**, allows at most one such branch; the selector sum then forces it to one, or no zero exists. Thus the complete real fibre is natural also at zero. For the actual signal event branches, positive-span/positive-pivot guards exclude zero altogether.

The isolated tuple with two selectors `1/2,1/2` and zero copies does make the weak gate vanish. Making both branches guard-free would violate the theorem's disjointness hypothesis, so it is not a counterexample to the complete packet. Adding the selector to each right factor enforces one-hot selection independently of that hypothesis. It preserves the **witness, affine-row and product counts**, not a claimed unchanged arithmetic-operation schedule.

## Comparisons that passed within this scope

The six new canonical-report notes correctly preserve the reset net's consume–reset–produce convention, natural weights and overlaps, external horizon, labelled-word semantics, peak-mass fuel threshold, and distinction from nontrivial commutation classes. The `2813h` peak ledger and real-fibre statement concern fixed natural inputs and source horizon, not the separately optional real-valued duration slack. The membrane population `L+R+5` is numerical population, not binary input length; no general substrate-transfer theorem is claimed.

The sparse comparison correctly charges `T[M(q^3+14)+5M(M-1)]` natural witnesses for total alphabet size `q`, mass rather than occupied-site count, and large gaps through witness heights. It neither supplies a support-linear sandpile compiler nor a uniform scalar horizon compression. The comparison/equality/comparator counts and the low-mass Presburger quartic's `2I+6C+G` witnesses agree with the reviewed original constructions; the separately reviewed five-witness congruence improvement is not silently substituted into the source ledger.

The catalogue distinguishes polynomial unknowns of unbounded degree, finite field configurations, external proof DAGs, and ordinary integer witnesses in its detailed entries. The exact Tree Calculus constructor-DAG count is a charged constant representation, not a small emitted scalar or an ordinary-input universal-operation bound. The smooth-finalizer phrase “same natural zeros” is read as its explicitly stated graph bijection with five additional coordinates. None of these notes claims an improvement to the complete universal 87-operation benchmark.

The earlier Tree Calculus exact-size/upper-bound uniqueness, `n=0,1` DAG-size exceptions and single-fold-loader implication are **outside this new diff**. They are already handled separately by `review_tree_typesetting_954261e15.patch`; this patch does not repair or count them again. I independently read that five-edit patch and agree with its single-fold qualification: a computable input translation alone supplies no single-fold polynomial graph, whereas a fully charged single-fold translation composes by a sum of squares.

## Pins and reproducibility

The [receipt](review_batch79_j2_bbc67d225.json) records both full commit IDs, base/head Git blobs and SHA-256 hashes for all fourteen text files, normalized read scope, prior review pins, and the private patch's before/after hashes. A bounded mechanical check found exactly **180** manifest entries, identical ordered label occurrences in each of the four report articles, and all **32** named cross-references introduced by the new TeX resolving in the pinned report sources. These checks do not establish mathematical truth or verify PDF pagination.

The [private prose patch](review_batch79_j2_bbc67d225.patch), SHA-256 `2c3b12c40d1413069ac16afffa35b32b0fa85da5947c6503c6e4fd08205802d3`, changes seven files. Both `patch --batch --fuzz=0 -p1 --dry-run` and the actual application passed against private copies of the pinned head; every resulting file matched the independently constructed expected text byte for byte. No repository file, archived source, Python/Lean program or original theorem was edited. No unchanged author tests were rerun.

To reproduce the source scope, use `git diff --no-ext-diff abfc0cb2524aa221a7e110f6dacc8f1fb8b60e65 37652b3e60a676e119746f5b874147cb4d9e1d2b` and retrieve the receipt's paths with `git show COMMIT:PATH`. Apply the patch only to a private checkout or copied file tree rooted at that head. Later builds and repaired source commits need their own pins.

## Root verification

Root read the new report comparisons, findings and complete patch, independently
checked all 28 base/head text hashes, four ordered label censuses, 32 named
references and 180 catalogue entries, and applied the seven-file patch to fresh
private copies with zero fuzz. Every expected before/after hash matched.
The complete-packet zero-input argument was independently checked against its
disjoint homogeneous branch hypothesis. No maintained report or PDF is edited;
applying the patch requires rebuilding the affected PDFs and catalogue.
