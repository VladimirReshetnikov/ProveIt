# Review: Mixing Does Not Remove Arithmetic

PASS on the stated mathematics, the compiler's documented construction interface, and both original executable verification entry points. No repair is requested. This review covers the entire 1,513-line `article.tex`, README/provenance, and all three substantive Python modules. It is not a historical-priority certification, a proof-assistant verification, a hostile-JSON parser audit, or an instantiated universal-polynomial arithmetic improvement.

The original archive is `docs/incoming/Mixing_Does_Not_Remove_Arithmetic.zip`, SHA256 `8c3543f514df39f26f5668d5434ddaa50580aab0303ef84dc6c286731c50c1ca`. [Portable checker](review_mixing_aebfa386e.py) and [deterministic receipt](review_mixing_aebfa386e.json) contain all 27 member hashes. They check archive and member bytes before execution, reject unsafe or duplicate ZIP entries, extract privately, and restore the exact prior compiler module after imported checks. They require only a caller-supplied archive path; no retained `/tmp` tree is needed. Original archives were preserved.

## What the construction actually represents

For a nonzero rational polynomial `P` in `k` natural letter counts, the derivative/translation space `V` has finite dimension `r`. Rational polynomial evaluation on the whole natural grid is injective; finite differences and derivatives span the same module. The article's row-oriented shift matrices therefore satisfy `a A_1^n1 ... A_k^nk b=P(n)` and all total-order `d+1` differences vanish when `deg(P)<=d` (`article.tex:249–353`). The evaluation column `b` is nonzero because `V` contains the constant polynomial. This also covers nonzero constants; the compiler rejects a wholly zero family but permits loading zero into a previously compiled nonzero module.

The lift at `article.tex:369–489` is correct. Choose `C` with first column `b`, set `E=[C|-C1]`, and `F=E^T(EE^T)^(-1)`. Then `EF=I`, `FE=I-J`, `E1=0`, and `Ee1=b`, where `J` is uniform averaging in `s=r+1` states. For `K_i=FA_iE`, `q=theta/(1+s max|K_i|)` and `0<theta<1`, the actual transition matrices `M_i=J+qK_i` are strictly positive, doubly stochastic, commuting and invertible. Their entries lie strictly between `(1-theta)/s` and `(1+theta)/s`; their spectrum is `1,q,...,q`, including possible Jordan blocks.

Loading `p=u+epsilon*aE` with the displayed positive scale gives

```
p M_1^n1 ... M_k^nk e1 = 1/s + epsilon*q^(n1+...+nk)*P(n).
```

The empty word is included because `J+FE=I`. Arbitrary word order is harmless precisely because the matrices commute. Uniform minorization gives total-variation contraction by at most `theta` per letter, including arbitrary switching. Yet every finite matrix product is invertible: a nonuniform full distribution cannot become uniform. A single coordinate can equal its equilibrium value. Confusing those two events would invalidate the theorem; the report explicitly distinguishes them (`article.tex:525–542`).

This is a controlled finite-word existential computation, not an autonomous finite Markov chain simulation of an arbitrary Turing machine. The unbounded natural count tuple is the witness. Rational evaluation of any supplied finite word is decidable. Strong contraction and bounded matrix size do not supply a computable universal bound on an exact equilibrium hit.

## Dimension, degree and the boundary of universality

The exact-series lower bound `s>=r(P)+1` (`article.tex:490–524`) is justified by the mass-zero state subspace of dimension `s-1` and the rank of polynomial translates. It also extends to a shared alphabet/observable/decay factor realizing a whole family: use its joint translation module. This is **not** a lower bound for representing just the same zero set, and is not a gate-count lower bound. The independent fixtures exhibit `P=x` and `P=x^2`, which have the same natural zero set but require three and four states respectively under this exact-series recipe.

The quartic dimension proof (`article.tex:543–613`) is sound: derivatives of order at least two have degree at most two, so

```
r(P) <= 1+k+binomial(k+2,2) = binomial(k+3,2)-1.
```

Radial quartics `(sum x_i^2)^2` attain the rank bound. The general degree split similarly gives `s<=2*binomial(k+2,2)+1` for quintics. These count vector-space/state dimensions, not additions, multiplications, polynomial variables after a finite-history expansion, or the minimum complexity of a universal Diophantine equation.

The universal-existence construction (`article.tex:614–845`) imports MRDP, separates positive and negative coefficient circuits, and gives unique natural intermediate values **for each original witness tuple**. It does not give finite-fold MRDP. With a copied input coordinate `z0`, fixed quadratic gate rows produce a nonnegative integer quartic `S(z)=sum q_j(z)^2`. Then

```
Q_t(z)=(z0-t)^2+S(z)
```

has the required natural zeros. Its joint family lies in the module of `Q_0,z0,1`, retaining the quartic state budget. Initial rows vary on an explicitly bounded rational quadratic curve whose denominator is proportional to `(1+t)^2`. The matrices, accepting state and alphabet are fixed; the exact initial rational data carry the input.

For a straight-line rational initial loader the report instead uses

```
P_t(z)=t-z0+(z0+1)S(z)
      =t+1-(z0+1)(1-S(z)).
```

If `t,z0` are natural and `S` is a nonnegative integer, `P_t=0` forces `S=0,z0=t`; this is equality of complete natural root tuples with `Q_t`, not equality of their values. Integrality and the natural domain matter. For example, `t=0,z0=1,S=1/2` gives a spurious real zero of `P_t`; `t=0,z0=-2,S=2` gives a spurious signed zero. The degree rises to five. Since the nonconstant module contains `1`, the initial rows can be written `(b0+t*b1)/(1+t)` with fixed strictly positive rational endpoints. The limiting endpoint `b1` represents constant `1` and has no equilibrium hit. The proof does not treat this limiting endpoint as a finite natural input.

Exact rational numerator/denominator bit length grows as `O(log(1+t))`; this is a paid input representation in the Markov model, not a free ordinary parameter loader into the repository's charged polynomial. The delivered numerical factorization families are not the universal alphabet. The report implements polynomial-family-to-Markov compilation, leaving an actual machine-to-universal-polynomial frontend and its numerical Markov matrices as future work.

The effective converse (`article.tex:846–920`) is also valid under its explicitly tested promises. Setting `R_i=q^(-1)(M_i-J)-(I-J)`, commuting total nilpotence of degree `d+1` makes the normalized acceptance a rational polynomial of degree at most `d`, obtained by a finite multivariate binomial sum. Clearing one positive denominator returns an ordinary integer polynomial. This permits c.e.-completeness at depth at most four through the imported quartic result. The cubic case is characterized in terms of the cubic natural-root problem; the article does not claim to resolve it.

The diagonalizability observation at `article.tex:921–948` needs its restricted spectral assumptions: simple eigenvalue `1` and a single transient eigenvalue `q`. In that class diagonalizability forces `M=J+q(I-J)`, so normalized signals are constant. It is not a blanket theorem that every reversible stochastic model is arithmetically trivial.

For a target separated from equilibrium (`article.tex:949–1027`), an exact rational `H` with `theta^H<|c-1/s|` gives a finite search over words of length `<H`; under commutation there are `binomial(H+k-1,k)` count tuples. The inequality is strict. At `theta=1/2,delta=1/8`, the least valid `H` is four. Approximate equilibrium tolerance eventually accepts everything; it does not decide exact equality. None of these robustness statements supplies an exact critical-target horizon.

## Actual source and independent replay evidence

`mixing_compiler.py` constructs matrices from an exact derivative basis, verifies closure by coefficient equality, snapshots families/variables, and returns immutable SymPy matrices in a frozen realization. The documented entry point is `compile_family`; arbitrary manually assembled `Realization` instances are not claimed to be authenticated certificates. Exact rational parameters, natural counts, module membership and initial positivity are checked. Zero loading and constant families work. The packaged standard-library checker is expressly a verifier for these exports, not a hostile schema parser; its use of `zip` and assertions is read in that stated scope.

Both original commands ran successfully in a safe private extraction:

```
python code/build_examples.py
python code/verify_exports.py
```

All 14 example JSON files reproduced byte for byte. Both saved reports matched exactly after removing only `compiler_report.sympy_version`. The producer performed 14 symbolic reverse identities, four radial rank cases and 19 malformed-input rejections. The original independent Fraction checker covered 1,310 count tuples, 1,424 words including empty words, and 269 degree-plus-one nilpotence products. It also checked full-vector non-erasure, invertibility by exact ranks, strict margins and both parameterized input curves. The two `t=6` factorization examples have exactly `(1,6,6),(2,3,6),(3,2,6),(6,1,6)` in the tested box. No LaTeX recompilation or rendered-PDF layout audit was needed for this mathematical/code review.

The new review helper independently expands the normalized binomial matrix series **from the actual transition entries** using only `Fraction` arithmetic and sparse polynomial products. It matches every coefficient of all 14 exported polynomials and checks the corresponding 269 degree-plus-one centered-row products. This is a finite symbolic identity computation, stronger than comparing polynomial values at sampled tuples. General annihilation of the full matrix algebra is supplied by the article's proof and the original full-matrix checker; the new row checks are not mislabeled as full-matrix checks.

Additional independently generated cases include nonzero constants, a zero load, a linear polynomial, a quadratic, a joint family with a zero member, an integer-valued binomial polynomial with rational coefficients, and a mixed rational polynomial. Recorded checks are:

- Six independent translation-grid rank computations; nine exact determinant identities.
- Ten additional complete polynomial reconstructions and positive loadings; 88 distribution tuples and 88 contraction inequalities.
- Forty-two immutable-matrix mutations rejected and one original-input-container snapshot check.
- Sixteen malformed numeric/domain/module calls rejected.
- Twelve strict separation boundary cases, the zero-set/rank distinction fixture, and 320 exact natural positive-filter tuples.

The finite examples supplement the proofs; no universal accepting witness was materialized and no claim of exhaustive testing over all polynomials is made.

Reproduce the complete pinned review with

```
python review_mixing_aebfa386e.py --archive Mixing_Does_Not_Remove_Arithmetic.zip --expect review_mixing_aebfa386e.json
```

## Literature and useful transfer

The inspected primary references support the report's careful provenance. Bell proves undecidability for commuting probabilistic automata and distinguishes a binary **noncommuting** construction. [Bell, arXiv v3](https://arxiv.org/abs/1902.09407v3). Bell–Semukhin's binary fixed commuting results are NP-hardness claims, which do not by themselves prove binary commuting undecidability. [Bell–Semukhin, v5](https://arxiv.org/abs/2105.10293v5). The classical minimal linear-state dimension equals Hankel rank; Balle–Mohri state and prove this as Theorem 1 in Section 3.2, with attribution to Fliess. [Learning Weighted Automata](https://borjaballe.github.io/papers/cai15.pdf). These checks establish relevant prior-work boundaries, not novelty of every present combination.

The practical transfer is an exact module-sharing compiler with a paid rational input curve and a reverse polynomial certificate. Its domain-sensitive positive-error filter is useful when a line loader is more valuable than preserving degree four. It is not automatically an arithmetic improvement: given an already evaluated `S`, evaluating `(z0-t)^2+S` costs one multiplication and two additions, whereas `t-z0+(z0+1)S` costs one multiplication and three additions under the repository's usual charged operations. The report trades degree and state dimension for simpler input geometry. A smaller fixed ordinary-input universal circuit would still need actual source-level composition and a full ledger; this review does not claim one.
