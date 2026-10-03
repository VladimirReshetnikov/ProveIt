# Smooth-finalizer typesetting transfer review

The mathematical transfer in `83abbd7fae02219e3d11a44c2825fef73e193325` passes this bounded review. The original formulas, theorem statements and proofs are preserved. Two new presentation defects need narrow corrections: the reproduction command does not pin its recorded Python version, and the new Poonen comparison omits his nonconstant-input hypothesis and overstates the degree for lower-degree source systems. Neither is a defect in the archived finalizer theorem or implementation.

The [receipt](review_smooth_typesetting_83abbd7fa.json) pins the new sources, all 16 original archive members, the previous complete review artifacts, and the separate reciprocal note added by `7ec2b5a2a`. The [presentation patch](smooth_typesetting_83abbd7fa_presentation.patch) changes only the two affected text passages. It applies successfully to a private copy of the exact source blobs. Canonical repository files have not been edited.

## Exact transfer and coverage

The original archive is `Smooth_Quartic_Diophantine_Certificates.zip` at `ef2fc7990`, SHA-256 `52cea74ad86e678a10963c2d8db4cb5874fc8aece9691c2dcfea45bfb00f9551`. Its original `smooth_diophantine/article.tex` has SHA-256 `2ad776fa10af8d8bd446e77273888b9806564cf1e32e6c31475f526de164be89`. All 16 archived member hashes match the [earlier full proof/code review](review_smooth_quartic_aebfa386e.md) and its receipt.

This typesetting commit changes only the report's README, TeX and PDF. It changes no computational module, exported certificate or verification data. I read the full new README and entire TeX diff against the previously reviewed source, then checked each added mathematical comparison against the relevant source statements. The earlier 21,128-check author replay and independent algebra/domain checks remain prior evidence; no unchanged author suite was rerun for this audit.

For an explicit preservation check, remove each `sdf:` label prefix and `\label{...}` macro, trim line whitespace, and discard blank lines. Comparing original and new source sequences then finds exactly one deleted/replaced original line: title-page spacing changes from `\vspace*{16mm}` to `\vspace*{2mm}` with a comment. Every other old normalized line remains in order. All new material is inserted editorial text, provenance, labels, bibliography or layout support.

The bodies of all nine theorems, four propositions, five lemmas, three corollaries, one example, two remarks, ten research questions and 22 proofs compare identically under that normalization. All 64 original labels survive with the `sdf:` prefix; the typeset article has 85 labels. The source grows from 1,733 to 2,129 lines. The supplied PDF metadata reports 34 pages. I did not rebuild the PDF or audit its rendered layout.

The added preface, notation table, provenance appendix and marked notes preserve the important boundaries:

- Natural zeros have the unique lift `(x,1,1,0,0,0)`; integer zeros have two sign-related copies. This is not an assertion about the rational or real zero set.
- The bounded counter frontend has an external horizon and accepts halting by that horizon. Its growing witness list is not a fixed-arity unbounded-history compiler.
- Fixed-arity universality uses an already available MRDP representation. Its witness multiplicities are retained, with no finite-fold or single-fold conclusion.
- The finalizer has witness degree four. Treating the specified ordinary input loader parameter as a coordinate instead of a coefficient gives the described total-degree-six presentation. The alternative total-quartic homogenization does not supply the unresolved relative-smoothness claim.
- The five-auxiliary minimum is confined to the positive integral guard architecture of total weight four. It is not a lower bound on general Diophantine representations.
- Geometric smoothness concerns the affine scheme over the integers, not a smooth proper model. Dyadic existence is distinct from density. No operation improvement on the universal-polynomial benchmark is claimed.

I checked the added CDC references to unique quadratic lifting, the counter zero guard and quartic normalization against their actual labeled statements. I checked the PQC Boolean-circuit residuals, compiler theorem, Hessian theorem and following nonsingularity remark. The ordinary externally bounded PWH exports are also admissible integer quadratic-residual inputs; applying the finalizer preserves their external bounds. This is an interface check, not a fresh review of every theorem in those large reports. The named Lean declarations exist, but no Lean build or axiom audit was performed.

Ramanujan's primary paper lists the `(1,1,2,2)` form used in the elementary four-square argument; the editorial note says it was listed there and does not claim its first discovery. I checked that entry in [Section 2 of the original paper](https://ramanujan.sirinudi.org/Volumes/published/ram20.html). I did not re-prove every form in that historical list or conduct a comprehensive priority search. The added Minsky reference is background attribution, not a new implementation dependency or a fresh full-book audit.

## Two presentation repairs

At `README.md:292`, the `uv` command pins SymPy but permits a different Python version. Lines 294–296 then compare all output bytes after removing carriage returns. The verifier explicitly records `platform.python_version()`, and the supplied receipt records `3.13.5`; the README itself reports a `3.14.4` rerun differing in that field. Exact comparison therefore need not succeed with the displayed unpinned command. The private regression changes only that metadata field and confirms that the records differ while every other field agrees. It does not claim to rerun the verifier under either Python version.

The patch adds `--python 3.13.5` to the existing command. SymPy remains pinned to `1.14.0`, and the exact comparison is retained.

At `article.tex:366–373`, the added comparison says Poonen's lemma takes a single equation `f` with degree `2 deg f`, and that a quadratic system would yield degree eight. I reread the complete statement and proof of [Poonen's Lemma 4.1](https://math.mit.edu/~poonen/papers/automorphism.pdf), PDF page 3. It explicitly requires **nonconstant** `f`. Its construction has the form `c(y²−y)+f²`, for a suitable positive integer `c`, and exact degree `2 deg f` under that hypothesis.

For `f=Σ f_i²` with integer residuals of degree at most two, the correct conclusion is **at most eight when the sum is nonconstant**. It is exactly eight if at least one residual has degree two: the leading real squares cannot cancel. The permitted residual `f_1=x` instead gives `f=x²` and a degree-four Poonen polynomial. Constant systems lie outside the cited lemma's stated hypothesis; the patch does not extend its geometric-integrality theorem to them.

The patch restores this qualification and degree distinction. The corrected text still accurately compares one added variable with this finalizer's five, without changing either construction. **Applying the text patch requires rebuilding `article.pdf`; the supplied PDF remains unmodified and contains the original comparison note.**

## Reciprocal PQC note

I also read the complete changed TeX and README passages in `7ec2b5a2ac62a5b7f48a09f1d143c141021e03bd`. That commit adds 45 TeX lines, deletes or replaces no existing TeX lines, and preserves the exact sequence of 1,138 labels. The receipt pins its three new blobs. This is a bounded audit of the reciprocal note, not another full review of the PQC report or its PDF build.

The note correctly applies the smooth finalizer to `X_i(X_i−1)` and the circuit residuals, all integer polynomials of degree at most two. The natural zeros are exactly `(b,1,1,0,0,0)` for satisfying Boolean circuit assignments `b`; the integer zeros additionally have `(-b,-1,-1,0,0,0)`. Smoothness of this new hypersurface and nondegenerate minima of the original sum-of-squares energy concern different polynomials. The original non-claim about complex zeros of the energy is preserved.

The new polynomial takes negative values even when the Boolean circuit is unsatisfiable. Put `c=Σ f_i(0)²`, choose `ε=1/(2(c+1))`, and set

```
X=0, t=ε, u=1/ε, z1=z2=z3=1/4.
```

Then the homogeneous residual sum is `H=c ε⁴`, the unit residual vanishes, and the weighted guard sum is `−1/2`. Thus `F=c/(16(c+1)⁴)−1/2<0`. This point is in the nonnegative real orthant, and no source solution is assumed. At every real zero the nonzero gradient also prevents a local minimum on the full real ambient space. The reciprocal note needs no repair.

The later exponential-sign-chart integration `f97814421` is outside this packet.

## Pins and reproduction boundary

The exact `83abbd7fa` SHA-256 pins are:

| File | SHA-256 |
|---|---|
| `article.tex` | `43346893ae17520923a3bec7a2be89c38fd96fa058ec1253cfd74d23a2b8d94f` |
| `README.md` | `3e0c33dbf9bef13ce21efc44b2f587750e351d2b7314ee34bc221f21fc9b634b` |
| `article.pdf` | `2ff119dc4dc774d524ec083d682bdff9c5a175d3acf8ae894d1e0debcf0cb6f6` |

The receipt includes before/after text hashes for the private patch application and the complete original member inventory. The comparison can be repeated by obtaining the original ZIP with `git show ef2fc7990:docs/incoming/Smooth_Quartic_Diophantine_Certificates.zip`, obtaining the three report blobs with `git show 83abbd7fa:<report-path>/<name>`, applying the explicit normalization above, and comparing the ordered source lines and named environment bodies. The Git change inventory is `git diff --numstat 83abbd7fa^ 83abbd7fa -- <report-path>`.

The patch was validated with `patch --batch --forward -p1` in a private directory containing only the pinned source copies. Both resulting text files match the receipt's patched hashes, while the copied PDF remains byte-identical. No report formula, domain encoding, computational source, arithmetic-operation count or original export changed.

Root separately authenticated all sixteen archived members and the three typeset blobs, reproduced the ordered-line and every named-environment comparison, and applied the patch privately to reproduce both patched text hashes. Root also checked the nonconstant hypothesis directly in Poonen's primary Lemma 4.1.
