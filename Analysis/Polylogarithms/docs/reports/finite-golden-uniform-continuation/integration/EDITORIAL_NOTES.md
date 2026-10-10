# Proposed corrections to the pinned algebraic-ladder chapter

## Baseline, scope, and application

`corrections.patch` is a proposed unified patch against ProveIt commit
`28357e8ca63dd78327db91d9be239d75e4462879`. It changes only:

- `Analysis/Polylogarithms/docs/manuscript/chapters/03-algebraic.tex`
- `Analysis/Polylogarithms/docs/manuscript/references.tex`

The downloaded source files were not edited. Their SHA-256 values are:

| File relative to the manuscript directory | SHA-256 |
|---|---|
| `chapters/03-algebraic.tex` | `270ffd30430d1b3737026263040725c00953c3efe733ccb45b1f053dd2dc07aa` |
| `references.tex` | `80e5c8c28a06652f6a5059fcaadc31efb23b297ce4d712cdea5db0a2617f3121` |

The patch was produced with Python's `difflib.unified_diff`, with exact-once
replacement checks. `git apply --check` succeeds against an untouched copy
of these two pinned files. To review and apply it from a matching repository
root, use:

```sh
git apply --check /path/to/this-bundle/integration/corrections.patch
git apply /path/to/this-bundle/integration/corrections.patch
```

Application is proposed, not performed. On a later repository revision,
review the changed context before applying. The patch does not insert the
new research article or assert that the manuscript's numerical formulas
are false. Its purpose is to correct a definite historical error, state
the evidence accurately, and repair incomplete ladder notation.

## Reasons for the replacements

### 1. The plastic-field sequel was published

The statement that the sequel was “never-published” is incorrect. The
publisher records M. Abouzahra, L. Lewin, and Xiao Hongnian,
*Polylogarithms in the field of omega (a root of a given cubic): Functional
equations and ladders*, **Aequationes Mathematicae 33** (1987), **23–45**,
DOI [10.1007/BF01836149](https://doi.org/10.1007/BF01836149).
The [publisher's record](https://link.springer.com/article/10.1007/BF01836149)
also makes the historical proof status explicit: lower orders were treated
analytically, while the reported results above order five were numerical
at publication. That is a statement about the 1987 paper, not a claim that
no later proofs exist.

The patch therefore replaces the false publication claim, changes the
heading that presents this classical base as new, and adds a bibliography
entry. The page range 23–45 follows the primary publisher, rather than the
inconsistent 1–20 range appearing in one later bibliography.

### 2. Numerical evidence and proof are different statements

The opening golden-ladder paragraph, its numerical-cancellation remark,
and the headings for the displayed weight-four through weight-nine
relations are revised together. “Verified,” “holds,” and “correct” can
reasonably refer to an actual proof; the local supporting material here
reports PSLQ recovery and finite-precision substitution. The replacements
say exactly what that evidence establishes.

Specifically, the patch retains the reported precisions and residuals,
describes weight-six and weight-seven vectors as reconstructions, and
describes the weight-eight and weight-nine formulas as numerically
supported candidates in this presentation. An integer coefficient agreeing
with a historical coefficient is an exact comparison of integers. It does
not independently prove the corresponding numerical period identity.
Likewise, a displayed residual of zero at a fixed working precision means
the residual rounded to zero in that computation.

The opening qualification expressly limits these remarks to the evidence
supplied in the chapter. It avoids any blanket assertion that published
golden ladders remain unproved. The later cubic and quartic trilogarithm
proofs are preserved as proofs; their earlier numerical discovery is
described as a useful diagnostic, not as what establishes equality.

### 3. Bounded searches do not prove a maximal ladder weight

The chapter's negative-search sentences are restricted to the argument
sets and coefficient bounds actually tested. The claim attributing a
general negative answer about arbitrarily high golden weight to
Abouzahra–Lewin is replaced by references to the established ladder
literature and a statement of what still needs proving.

The research article in this bundle proves a complete golden
multiplicative seed lattice and the corresponding specified exterior-symbol
kernel. Those are precise completeness results. They do not by themselves
prove a greatest possible weight for ordinary polylogarithm evaluations,
nor numerical independence of all remaining constants. Additional
higher-weight conditions are needed. This distinction also governs the
later paragraph about the supergolden field.

### 4. The tetralogarithm reduction has a local missing proof step

The chapter's two duplication identities are exact. The specialized
cross-base Kummer relation is then stated, but the chapter's concluding
paragraph explicitly says that a complete derivation from Kummer's
functional equation, with its branch conditions, has not been supplied
there. The earlier assertion that the tetralogarithm identity follows
unconditionally is inconsistent with that qualification.

The patch makes the implication conditional: proving the displayed Kummer
specialization completes the duplication argument. It leaves every
coefficient and the explicit intermediate relation unchanged. This is a
correction to the local proof exposition, not a claim that the
tetralogarithm relation is false or lacks a proof elsewhere.

### 5. The canonical ladder chain needs an explicit `L12`

The chain defines `L20` and `L24`, then uses `L12` without defining it.
Its factorial denominators also become undefined at the claimed lower
orders. The patch supplies a proposed reconstruction of `L12`, uses the
same normalization as the two displayed definitions, and states the
convention that a tail summand with a negative factorial index is omitted.
The domain of the low-order statement is explicitly `1 <= n <= 4`.

This is a notation repair justified by exact rational equivalence at
order five and independently replayed at orders one through five. It does
not add an analytic proof of the special-value formulas. The section
heading is updated to include index 12, and the subsequent numerical
extrapolation is labeled accordingly.

### 6. Later plastic-field literature needs correct normalization and dates

The final literature paragraph now includes the published 1987 sequel
and Herbert Gangl's *Functional equations and ladders for polylogarithms*,
**Communications in Number Theory and Physics 7** (2013), no. 3, 397–410,
DOI [10.4310/CNTP.2013.v7.n3.a1](https://doi.org/10.4310/CNTP.2013.v7.n3.a1).
The author's preprint is dated September 2010; 2013 is the bibliographic
volume year recorded by the
[author's institution](https://durham-repository.worktribe.com/output/1478789).

Gangl's higher functional relations use modified polylogarithms. This
normalization matters: the even-weight single-valued modified functions
vanish on real arguments, so their real specialization must not be
identified silently with an ordinary even-weight `Li_n` ladder. The patch
retains a brief distinction and does not import unproved claims from one
normalization into another.

## Exact derivation of the canonical notation repair

Put

\[
\rho=\frac{\sqrt5-1}{2},\qquad
\ell=\log\rho=-\log\phi.
\]

For positive integers `n`, define the tail associated to a triple
`(D1,D2,D3)` by

\[
\operatorname{tw}(n)=D_1\frac{\ell^n}{n!}
 +D_2\zeta(2)\frac{\ell^{n-2}}{(n-2)!}
 +D_3\zeta(4)\frac{\ell^{n-4}}{(n-4)!},
\]

omitting each term whose factorial index is negative. The proposed missing
definition is

\[
L_{12}(n)=\frac{\operatorname{Li}_n(\rho^{12})}{12^{n-1}}
 -\frac32\frac{\operatorname{Li}_n(\rho^6)}{6^{n-1}}
 -\frac{\operatorname{Li}_n(\rho^4)}{4^{n-1}}
 +\frac{11}{48}\frac{\operatorname{Li}_n(\rho^2)}{2^{n-1}}
 +\operatorname{tw}_{12}(n),
\]

with

\[
(D_1,D_2,D_3)=
\left(-\frac{13}{48},\frac1{48},-\frac{19}{1728}\right).
\]

### Exact residual transformation

Let `E1`, `E2`, `E3` denote left side minus right side of the three
weight-five formulas as printed in the source, in their displayed order.
Then the following are identities of coefficient vectors, independently
of whether the proposed special-value evaluations have been proved:

\[
\begin{aligned}
L_{12}(5)-\frac{67}{6912}\zeta(5)
 &=\frac{E_1}{15\cdot12^4},\\
L_{20}(5)-\frac{201}{10000}\zeta(5)
 &=\frac{E_2}{9\cdot20^4},\\
L_{24}(5)+\frac{1541}{110592}\zeta(5)
 &=\frac{E_3+\frac{64}{3}E_1}{-15\cdot24^4}.
\end{aligned}
\]

All denominators are nonzero. This triangular transformation is invertible,
so the three source formulas and the three normalized evaluations are
equivalent. In particular, the index-24 normalization needs the indicated
recombination; simply rescaling the third source formula would leave a
`Li_5(rho^6)` term instead of the displayed `Li_5(rho^12)` term.

### The three tail triples

After replacing `log(phi)` by `-ell`, the right-side coordinates of the
first, second, and recombined third source formulas are as follows. The
columns refer to the basis
`zeta(5), ell^5, pi^2 ell^3, pi^4 ell`.

| Canonical index | Divisor `Q` | `zeta(5)` | `ell^5` | `pi^2 ell^3` | `pi^4 ell` |
|---|---:|---:|---:|---:|---:|
| 12 | `311040` | `3015` | `702` | `-180` | `38` |
| 20 | `1440000` | `28944` | `6000` | `-1600` | `356` |
| 24 | `-4976640` | `69345` | `12888` | `-3600` | `2516/3` |

If a row has polynomial coefficients `(A,B,C)` in the last three columns,
moving that polynomial to the left and using
`pi^2 = 6 zeta(2)` and `pi^4 = 90 zeta(4)` gives

\[
D_1=-\frac{5!A}{Q},\qquad
D_2=-\frac{6\cdot3!B}{Q},\qquad
D_3=-\frac{90C}{Q}.
\]

Thus the triples and zeta coefficients are exactly:

| Index | `(D1,D2,D3)` | Coefficient of `zeta(5)` |
|---|---|---|
| 12 | `(-13/48, 1/48, -19/1728)` | `67/6912` |
| 20 | `(-1/2, 1/25, -89/4000)` | `201/10000` |
| 24 | `(179/576, -5/192, 629/41472)` | `-1541/110592` |

For example, the first triple is obtained from

\[
-\frac{702\cdot120}{311040}=-\frac{13}{48},\quad
\frac{180\cdot36}{311040}=\frac1{48},\quad
-\frac{38\cdot90}{311040}=-\frac{19}{1728}.
\]

The normalized polylogarithm coefficients follow just as directly:
an unnormalized coefficient `c_a` is replaced by `c_a a^4/Q`.
These operations are checked using Python `Fraction`, with no
floating-point arithmetic. In particular,

\[
\frac{1296}{625}\frac{67}{6912}=\frac{201}{10000},\qquad
\frac{23}{16}\frac{67}{6912}=\frac{1541}{110592},
\]

which verifies the stated cancellation of the order-five zeta terms in
`M20` and `M24`. It supplies no additional higher-order identity by itself.

## Numerical replay and its precise limits

The bundle includes:

- `code/canonical_reconstruction_check.py`
- `data/canonical_reconstruction_check.json`

The script freezes the source coefficients and proposed canonical
definitions. It performs exact rational comparisons first, then two
numerical evaluations: `mpmath.polylog`, and a separately coded finite
defining power series summed with `mpmath.fsum`. Both use the same
arbitrary-precision arithmetic library, so these are different
representations, not independent numerical software engines. No integer
relation search is used.

At 160 working decimal digits with 600 power-series terms, the replay gives:

| Check | Largest absolute discrepancy |
|---|---:|
| Individual polylogarithms, the two evaluation methods, orders 1–9 | `2.23e-162` |
| Three canonical ladders, orders 1–5, against zero or the stated zeta term | `1.12e-161` |
| Three unnormalized source weight-five formulas | `2.92e-157` |
| Source's displayed `T(9)` formula, after the reconstruction | `9.16e-165` |

Every diagnostic passes. In particular, the lower-order vanishing
statements are numerically consistent with omitting negative-factorial
summands, and the reconstructed `L12` is also consistent with the later
displayed `T(9)` expression. The JSON records the individual residuals,
the exact transformation data, source hash, script hash, working precision,
term count, and numerical library version.

For every argument used here, `0 < rho^a <= rho^2 < 2/5`. Therefore the
uncomputed tail after `N` terms, for all positive integer orders, has the
rigorous uniform bound

\[
0<\sum_{k>N}\frac{\rho^{ak}}{k^n}
 <\frac{(2/5)^{N+1}}{(N+1)(1-2/5)}.
\]

For `N=600` this is below `1.91e-242`. This bound controls truncation only;
the script does not enclose floating-point rounding, logarithms, or zeta
values in certified intervals. The replay therefore supplies a reproducible
numerical consistency check, not a proof of any asserted equality.

## Bibliographic additions and TeX validation

The patch inserts all four new citation keys into the existing
`references.tex`, so no external bibliography database or new macro is
required:

| New key | Source and role |
|---|---|
| `golden:AbouzahraLewin1985` | M. Abouzahra and L. Lewin, *The polylogarithm in algebraic number fields*, J. Number Theory 21(2) (1985), 214–244, [DOI](https://doi.org/10.1016/0022-314X(85)90052-6). Historical golden-ladder context. |
| `golden:AbouzahraLewinXiao1987` | Published plastic-field sequel, [primary publisher](https://link.springer.com/article/10.1007/BF01836149). Corrects the publication error and separates that paper's analytic and numerical results. |
| `golden:BaileyBroadhurst1999` | D. H. Bailey and D. J. Broadhurst, *A seventeenth-order polylogarithm ladder*, 1999 [primary preprint](https://arxiv.org/abs/math/9906134). Historical golden seed and higher-ladder discussion; cited explicitly as a preprint. |
| `golden:Gangl2013` | Published higher functional equations; [author's text](https://www.maths.dur.ac.uk/users/herbert.gangl/ladders1_ams.pdf) and [institutional record](https://durham-repository.worktribe.com/output/1478789). Distinguishes the modified-polylogarithm normalization. |

An extracted patched golden-ladder section together with the complete
patched bibliography was compiled successfully with `latexmk` and
pdfLaTeX. After the reference pass it had no undefined citations,
undefined references, or TeX errors. The pre-existing math in the section
title gives the usual PDF-bookmark warning; an inherited paragraph has a
small line-width warning in the test preamble. This was a syntax and
citation check of the affected section, not a reconstruction or layout
certification of the entire repository manuscript.

The ordinary-polylogarithm coefficient formulas already displayed in the
source are preserved. The added equation is the explicitly labeled
reconstruction of missing notation, with the exact equivalence and
numerical status documented above.
