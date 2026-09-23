# Dilation Rigidity of Surreal Numbers and Omnific Integers

**Autonomous Mahler equations, finite support, sharp algebraic degrees, and a higher-order hierarchy**
Single-source research report, 23 September 2026. It is built from one
manuscript, manuscript 08 of batch 30 (archive `surreal_dilation_rigidity`),
pinned to repository commit `b895e86`, and placed in commit `21375f8`.
Author line: research article prepared with ChatGPT for Vladimir Reshetnikov.

This directory holds one manuscript. It is not a merge: there was no second
source, and nothing was selected out of a larger body of work. Every result,
proof, example, question and limitation of the manuscript is printed.

```
article.tex       the report, standalone LaTeX with an internal bibliography
article.pdf       the compiled report, 32 pages (unnumbered title page, contents page i,
                  then pages 1–30)
README.md         this guide
SOURCE_AUDIT.md   the source's author-side source and claim audit, as delivered
code/             verify.py (the source's exact finite checks, SymPy)
data/             verification_results.json (the source's recorded run),
                  requirements.txt (the source's pin, sympy==1.14.0)
```

Every label in `article.tex` carries the prefix `adr:`. The source's 83 labels
are kept, unchanged after the prefix, and eight were added
(`adr:sec:conventions`, `adr:sec:collection`, `adr:sec:nonclaims`,
`adr:app:report`, `adr:app:onesource`, `adr:app:pinned`, `adr:app:literature`,
`adr:app:files`). No `adr:` label has a Lean implementation mapping in the
[formalization ledger](../../FORMALIZATION.md). `code/`, `data/` and
`SOURCE_AUDIT.md` are byte-identical to the delivery; the delivered README,
PDF and checksum list are not shipped, and `article.pdf` is a build of this
text. Text added when the manuscript joined the collection is marked `[write]`
inside the source's sections; Sections 1.4, 1.5 and 18 and Appendix C are new.

## The operator

For an ordinary integer `d ≥ 2`, the exponent dilation of a Hahn series is

    S_d(Σ a_γ t^γ) = Σ a_γ t^{dγ},   and on surreals   S_d(Σ a ω^g) = Σ a ω^{dg}.

It is the map that
[single-dilation-hahn-support](../single-dilation-hahn-support/) writes `S_q`
at `q = d`, and that
[surcomplex-field-automorphisms](../surcomplex-field-automorphisms/) writes
`S_a` at `a = d` (`saut:eq:dilation`). It is **not** `y ↦ y^d`
(`S_2(ω+1) = ω²+1`, while `(ω+1)² = ω²+2ω+1`), not the argument dilation
`f(z) ↦ f(λz)` of the holonomic-rigidity report, and not an exponential
automorphism. `A_Γ(k)` is the **negative-support** ring (support in `Γ_{≤0}`,
nonnegative growth support in `ω` notation), not the valuation ring. The
"autonomous algebraic order" of `y` is the least `r` with
`y, S_d y, …, S_d^r y` algebraically dependent over `k`. Section 1.4 fixes
these and the local letters (`M(y)`, `D`, `H_a`, `L`, `T`); no symbol of the
source was renamed.

## What the report claims

Theorem numbers are those of the built `article.pdf`. `k` is a field of
characteristic zero, `Γ` any ordered abelian group, `K_Γ(k) = k((t^Γ))` the
full Hahn field, `d ≥ 2` an integer. "Strong" means preserving Hahn summation,
not convergence of partial sums.

- **Support collapse (Theorem 6.1).** If `y ∈ K_Γ(k) \ k` satisfies
  `F(y, S_d y) = 0` for some nonzero `F ∈ k[X,Y]`, then `y ∈ k((t^δ))` with
  `δ = γ/e ∈ Γ`, where `γ` is the valuation of the positive-valuation
  coordinate (`y − res y` or `1/y`) and `1 ≤ e ≤ deg_Y F`. No divisibility or
  Archimedean hypothesis on `Γ` and no order on `k` is needed. The proof
  combines an evaluated Newton–Puiseux branch with individual-branch
  denominator bound (Lemma 4.1), a formal Böttcher coordinate built and proved
  unique inside `k[[Z]]` (Lemma 5.1), the exhaustive description of all Hahn
  solutions of a superattracting germ `S_d x = h(x)` (Proposition 5.2), and the
  monomial recognizer `S_d w = w^d ⇔ w = a t^η`, `a^{d−1} = 1` (Lemma 3.3).
  Supporting lemmas: strong evaluation commuting with `S_d` (Lemma 3.1);
  constants relatively algebraically closed, `Fix(S_d) = k` (Lemma 3.2).
- **Finite profiles and existence (Theorem 7.1, Corollary 7.2, Theorem 7.3,
  Corollary 7.4).** Over algebraically closed `k`, a fixed `F` has a finite list
  of ordinary Laurent profiles `f` whose evaluations `f(t^δ)`, `δ > 0`, are all
  nonconstant solutions in every nonzero divisible `Γ`; coefficients of
  solutions are algebraic over the coefficient field of `F`; a nonzero
  positive-valuation solution of `G(x, S_d x) = 0` exists iff the minimum of
  `i + dj` over the support of `G` is attained twice; existence is independent
  of `Γ` and effectively decidable for algebraic-number coefficients.
- **Negative-support classification (Theorem 8.1, Corollary 8.2).** For
  `y ∈ A_Γ(k) \ k`: `y, S_d y` are algebraically dependent iff
  `y = P(t^{−δ})` with `P ∈ k[T]` iff the support is finite with cyclic exponent
  group; `deg P ≤ deg_Y F`. The condition does not depend on `d`; infinite
  support, or finite support of rational rank at least two, forces independence.
- **Exact relation degree (Theorem 9.2, Corollary 9.3, Example 9.4).** The least
  `Y`-degree of a relation equals the primitive degree `M(y)`;
  `k(y, S_d y) = k(T)` for the primitive monomial `T`; the irreducible relation
  has bidegree `(dM, M)`. Consequence: `k(P(T), P(T^d)) = k(T^g)`, `g` the gcd of
  the supported positive degrees. `T² + T` at `d = 2` gives an explicit quadratic
  relation (worked in Appendix A).
- **Omnific integers (Theorem 10.1, Corollary 10.2, Examples 10.3–10.6).** For
  `x ∈ Oz \ Z`: `x, S_d x` are algebraically dependent over `R` (equivalently
  over `C`) iff `x = P(ω^δ)` with `P ∈ R[T]`, `P(0) ∈ Z`, iff the support is
  finite with commensurable positive exponents; the least relation degree is
  `deg P` in the primitive step. The same holds for `Oz[i]` with `C[T]` and
  `Z[i]`. Any two distinct forward dilates of an infinite-support omnific
  integer are algebraically independent over `C`. `ω^{√2} + ω + 1` is dilation
  independent (its primality is L'Innocente–Mantova's Theorem B, cited).
- **Rational maps (Theorems 11.1, 11.2, Corollary 11.3).** Over algebraically
  closed `k` and divisible `Γ ≠ 0`, `S_q y = R(y)`, `q ∈ Q_{>1}`, has a
  nonconstant solution iff `R` has a fixed point of local degree `q` (so `q`
  is an integer), with all solutions given by Böttcher
  coordinates; in `A_Γ(k)` the only solutions are `y = α t^{−γ} + b` with
  `R(Z) = α^{1−d}(Z − b)^d + b`; simultaneous solutions force commuting maps.
- **Infinitesimal tail (Theorem 12.1).** For a polynomial `P` of degree `d ≥ 2`
  whose centred normalization is not `X^d`, the infinite solution has an exact
  first positive-valuation term `−(αc/d) T^{1−r}`, so it is not omnific;
  `S_2 y = y² + 1` has no nonconstant omnific solution, `(Z − 3)² + 3` has
  `3 + ω^γ`.
- **Higher order (Definition 13.1, Theorems 13.2, 13.3, Proposition 13.4).**
  `u_d = Σ_{n≥0} ω^{d^{−n}}` is an omnific integer of exact autonomous order two,
  with `S_d² u_d − S_d u_d = (S_d u_d − u_d)^d`; sums of `r` monomials with
  `Q`-independent exponents have exact order `r`; finite support of rational rank
  `r` has order at most `r`, exactly 1 for `r = 1`, exactly 2 for `r = 2`.
- **Effective shapes (Theorems 15.1, 15.2).** A fixed `F` has finitely many
  polynomial shapes of degree at most `deg_Y F`; nonconstant solvability in
  `Oz` or `Oz[i]` is decidable for algebraic-number `F`, with a finite list of
  algebraic shapes (a termination result, not implemented).
- **Research questions 1–12** (Section 16) are left open. Question 5,
  nonintegral rational dilation, has one partial datum from the collection (see
  below).

## What the report does not claim

Section 18 collects every non-claim with its location: 24 from the source
(S1–S24) and 7 added when the report joined the collection (W1–W7). In brief:

- Not refereed; AI-assisted. No theorem is Lean-verified and no Lean source is
  supplied; no repository Lean build was performed by the source. No named
  published conjecture is claimed solved. Novelty is proposed, priority is not
  certified, and an absence of search results is not proof of priority.
- Credited, not claimed: Hahn arithmetic, the Neumann lemma, Newton–Puiseux,
  formal Böttcher coordinates (Salerno–Silverman), the collection's `d = 2`
  recognizer, resultants and exact algebraic-system solving. Mahler equations,
  Böttcher coordinates and non-Puiseux solutions are not new topics. The
  decreasing-denominator pattern of `u_d` is prior (Chyzak–Dreyfus–Dumas–
  Mezzarobba Remark 2.18, Gontsov–Goryuchkina); only its minimal order is
  claimed. The polynomial-field identity is a consistency check, not a priority
  claim. Not a factorization theorem; the primality example is cited.
- Scope: membership in `k((t^δ))` is necessary, not sufficient; strong
  evaluation is not valuation convergence; coefficient descent is for a fixed
  coefficient field; the Newton-weight test decides existence in the full
  field, not omnific existence and not whether an encoded series is a solution.
  Pairwise independence is not independence of longer tuples.
- Boundaries: false for `d = 1`; implicit relations with nonintegral `q` are not
  covered; fails in positive characteristic (Frobenius); fails with nonconstant
  coefficients (`S_d u_d − u_d = ω^d`); nothing about full first-order theories,
  and no contradiction with the single-dilation report's undecidability. Exact
  order for rational rank `r ≥ 3` is open.
- The decision procedure is a termination result, not implemented and with no
  complexity claim. The 91 finite checks certify no infinite statement.
- The source compared Nishioka–Nishioka only at abstract level, and cited the
  late-2025 preprints from their abstracts; the repository comparison covered
  selected reports and the inventory, not a line-by-line review.
- Added: (W1) no `adr:` label has a Lean mapping; (W2) Nishioka–Nishioka,
  read in full for this report, record Mahler's 1983 criterion for convergent
  power-series solutions of `P(f(z), f(z^d)) = 0` with constant coefficients,
  so no priority is claimed for Theorem 7.3, Corollary 7.4 or Theorem 7.1 in
  that rank-one power-series setting (Mahler's paper itself was not read);
  (W3) the partial datum below does not answer Question 5; (W4) none of the
  single-dilation report's questions is answered and its non-claim on
  variable-coefficient Mahler systems stands; (W5) not the holonomic report's
  argument dilations; (W6) nothing on which value-group automorphisms lift to
  exponential automorphisms, and none of the surcomplex-automorphisms questions;
  (W7) the source's repository statements stand at the placement commit.

## Relation to the neighbouring reports

Section 1.5 of the article gives these relations with labels.

**[single-dilation-hahn-support](../single-dilation-hahn-support/)** (`dsup:`)
— the same operator and the nearest report. Lemma 3.3 at `d = 2` is
`dsup:lem:monomialrecognition` (same least-term proof), and `Fix(S_d) = k` is
`dsup:eq:dilationfixed`. The boundary equation `S_d u_d − u_d = ω^d` is, at
`d = 2`, the Conway form of the second series of `dsup:ex:opposite` after one
application of `S_2` (`u_2 = S_2 y` with `y = Σ_{n≥1} ω^{2^{−n}}`,
`S_2 y − y = ω`); that report calls the example illustrative, and only the
exact order is claimed here. **Partial answer to this report's Question 5:**
for divisible `Γ` and `q = a/b`, `dsup:lem:rationalrecognition` shows that the
nonzero solutions of `(S_q x)^b = x^a` are exactly `μ_{|a−b|}(k) t^Γ`. So
implicit relations `F(y, S_q y) = 0` with nonintegral `q` do have nonconstant
solutions; these are monomials, consistent with Theorem 11.1 (since `b ≥ 2`)
and with the cyclic-support conclusion. The source's Section 14.3 leaves the
nonintegral case open, which is no contradiction; the general case stays open.
The linear and multiplicative equations of `dsup:thm:dilationcohom` and the
undecidability of `dsup:thm:undecidable` are credited; none of the three
questions of `dsup:sec:questions` (in particular definability from other
exponent automorphisms) is answered.

**[surcomplex-field-automorphisms](../surcomplex-field-automorphisms/)**
(`saut:`) — `S_d` is its `S_a` at `a = d` (`saut:eq:dilation`), built by
`saut:thm:monomial`; none of its questions is addressed.

**[exponential-automorphism-rigidity](../../surreal/exponential-automorphism-rigidity/)**
(bare labels) — on `No`, `S_d` is the canonical lift (`prop:hahn-lift`) of the
value-group dilation by `d`, which has no exponential lift (`thm:dilation`);
so `S_d` does not commute with `exp`. That report's subject, which value-group
automorphisms admit exponential lifts (`q:image`), is not this report's
subject, and the source's last question (interaction with the surreal
exponential) stays open.

**[holonomic-rigidity-for-entire-hahn-functions](../holonomic-rigidity-for-entire-hahn-functions/)**
(`hol:`) — its dilations are argument dilations `f(z) ↦ f(qz)` of entire Hahn
functions in linear `q`-difference equations (`hol:main:q`,
`hol:sec:qnecessity`), and its "order" is a differential order. It shares a
word with this report, not a theorem.

**[dynamics-and-normal-forms](../dynamics-and-normal-forms/)** — cited by the
source as a point of contact; it has no superattracting germs or Böttcher
coordinates (they occur in no other report), and nothing of it is used.

## Provenance and corrections (Appendix C)

The source compared itself with the collection at `b895e86`; Section 1.2 keeps
that comparison as written. Checked at the placement commit `21375f8`, its
repository statements stand (Appendix C.2): the single-dilation report has the
recognizer, the linear and multiplicative equations, the undecidability and the
normal-form recovery; no report supplies the classification. The reports the
source inspected are unchanged since the pin. No stale statement needed
correction.

References checked for this report (Appendix C.3):

- L'Innocente–Mantova: Theorem B of arXiv:1710.07304v5 states that
  `ω^{√2} + ω + 1` is prime in `Oz` (Gonshor's conjecture); the attribution is
  correct. The journal DOI is listed on arXiv; the volume number was not checked.
- Nishioka–Nishioka (Tsukuba J. Math. 39(2), 251–257): bibliographic data
  confirmed and the open-access full text read; see W2. Its example
  `f(z²) = f²/(1 − 2f²)` has the reciprocal solution `z^r + z^{−r}`, the
  identity `S_2 y = y² − 2` of Section 12.1.
- Gontsov–Goryuchkina (J. Symbolic Comput. 128, 102399): bibliographic data
  confirmed through the DOI registry; not read.
- Faverjon–Poulet (arXiv:2511.18877) and Faverjon–Roques (arXiv:2512.10661):
  titles, authors and dates confirmed; abstracts only, as in the source. The
  source's one-line summary of the second (generalized Mahler-series structure)
  is not confirmed by its abstract, which describes a purity theorem.
- Neumann, Mannaa–Coquand, Salerno–Silverman, Chyzak–Dreyfus–Dumas–Mezzarobba
  and Faverjon–Roques (arXiv:2412.04928) were confirmed during placement.
  Mahler (1983) is cited as reported by Nishioka–Nishioka and was not consulted;
  Basu–Pollack–Roy and the encyclopedia page were not checked.

## Build and reproduce

TeX Live or MiKTeX with newtxtext/newtxmath, amsmath/amsthm, mathtools,
geometry, microtype, xcolor, booktabs, tabularx, array, enumitem, fancyhdr,
needspace, tcolorbox, xurl, hyperref, aliascnt and cleveref. No external
figures or bibliography file.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX) has 32 pages and no errors, undefined references
or citations, multiply defined labels, duplicate destinations, LaTeX or package
warnings, or overfull or underfull boxes. A clean compile proves nothing about
the proofs.

`code/verify.py` needs Python 3.9 or later and SymPy (`data/requirements.txt`
pins 1.14.0). It uses exact arithmetic, prints its report and **writes
`verification_results.json` beside itself, overwriting any file of that name**.
Run in place it would create an unshipped `code/verification_results.json`;
Appendix B and `SOURCE_AUDIT.md` describe the flat delivered layout. Run it on a
copy, from this directory:

```sh
python -m pip install -r data/requirements.txt
T=$(mktemp -d)
cp code/verify.py "$T"/ && (cd "$T" && python verify.py > run.txt)
diff <(grep -v '"python"' "$T/verification_results.json") \
     <(grep -v '"python"' data/verification_results.json)
```

Do not run it with Python optimization flags that disable assertions. This was
run for this report under Python 3.14.4 with SymPy 1.14.0: exit code 0,
`"status": "PASS"`, and the written file agrees with
`data/verification_results.json` except for the recorded Python version
(3.13.5 in the delivery). The 91 checked instances are 6 inverse Böttcher
expansions through degree 32, 20 resultant cases (10 polynomials at `d = 2, 3`: one
irreducible factor of bidegree `(dM/g, M/g)` with multiplicity `g`), 10
Jacobian instances, 45 finite telescoping identities (with their boundary
terms), 4 Frobenius examples and 6 Newton-weight tests. They check finite
instances only; the decision procedure of Theorem 15.2 is not implemented.
