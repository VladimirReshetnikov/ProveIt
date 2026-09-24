# A Single Dilation Recovers Hahn Support

**Exact difference cohomology, definable normal forms, and centralizers of monomial automorphisms**
Single-source research report, 22 September 2026. It is built from one
manuscript, manuscript 09 of batch 22 (archive `surreal_dilation_support`),
pinned to repository commit `465a54b`, and placed in commit `7b5f934`.
Author line: research article prepared with ChatGPT for Vladimir Reshetnikov.

This directory holds one manuscript. It is not a merge: there was no second
source, and nothing was selected out of a larger body of work. Every result,
proof, example, question and limitation of the manuscript is printed.

```
article.tex      the report, standalone LaTeX with an internal bibliography
article.pdf      the compiled report, 35 pages (unnumbered title page, then pages 1–34;
                 pages 1–2 are the contents)
README.md        this guide
PROOF_AUDIT.md   the source's author-side hypothesis and verification-scope checklist, as delivered
code/            verify.py (exact finite checks), Makefile (the source's, see "Build and reproduce")
data/            verification.txt (the source's recorded run of verify.py)
```

Every label in `article.tex` carries the prefix `dsup:`. The source's 99 labels
are kept, unchanged after the prefix, and nine were added
(`dsup:sec:conventions`, `dsup:sec:position`, `dsup:sub:recovered`,
`dsup:sub:notmade`, `dsup:sec:nonclaims`, `dsup:app:report`,
`dsup:app:onesource`, `dsup:app:pinned`, `dsup:app:files`). No `dsup:` label has
a Lean implementation mapping in the [formalization ledger](../../FORMALIZATION.md).
`code/`, `data/` and `PROOF_AUDIT.md` are byte-identical to the delivery; the
delivered README and PDF are not shipped, and `article.pdf` is a build of this
text.

## One dilation, written `S_q`

For `q ∈ Q_{>0}` and divisible `Γ` (2-divisibility suffices for `q = 2`), the
exponent dilation is

    S_q(Σ a_g t^g) = Σ a_g t^{qg}.

The source wrote `D_q`, and abbreviated `D_2` to `D` in its definability
section. The report writes `S_q` throughout (Section 1.4), because
[NOTATION.md](../../NOTATION.md) reserves `D` (with `∂`) for a scalar
derivation, and because
[surcomplex-field-automorphisms](../surcomplex-field-automorphisms/) writes the
same map `S_a` (`saut:eq:dilation`) and uses `D_λ`, `D_χ` for character twists.
The source's support formula `S(m,x)` is written `Supp(m,x)` so that `S` has one
meaning; an unsubscripted `S` is only a well-ordered subset of `Γ`. No
normalization changed and no mathematical statement was changed.

Two readings to avoid: `S_2` is not squaring (`S_2(Σ a_g t^g) = Σ a_g t^{2g}`,
whereas the square is `Σ a_g a_h t^{g+h}`; they agree exactly on the canonical
monomials, Lemma 8.2), and `S_q` is not the argument dilation `f(z) ↦ f(λz)`
of formal functions. `σ` is always a coefficient-fixing monomial automorphism
of the scalar field, not the collection's symbolic shift or small-divisor rate;
"resonance" means only the set `R_λ` below, not the multiplier resonances of the
dynamics report.

## What the report claims

Theorem numbers are those of the built `article.pdf`. `K = k((t^Γ))` is the
**full** Hahn field over a field `k` of characteristic zero, with `Γ` any
ordered abelian group unless stated; `σ(Σ a_g t^g) = Σ a_g χ(g) t^{θg}` with
`θ ∈ Aut_ord(Γ)` and a character `χ: Γ → k^×`. "Strong" means preserving Hahn
summation, not convergence of partial sums.

- **Monomial automorphisms (Proposition 2.3).** Each `σ` is a strong field
  automorphism fixing `k`, with `v(σx) = θ(vx)`; the commutation criterion for
  two of them is explicit. The construction is credited background.
- **Orbit hull (Lemma 3.1, Corollary 3.2).** On `θg > g`, the forward orbits of a
  well-ordered set form a well-ordered set with finite fibres (inverse orbits on
  `θg < g`); summable families stay summable under all iterates. No cofinal
  growth is involved (Remark 3.3).
- **Resolvent (Theorem 4.1; Corollaries 4.2, 4.3).** For `λ ≠ 0` an explicit
  strong `k`-linear `Q_λ` satisfies `(σ−λ)Q_λ = Q_λ(σ−λ) = I − P_λ`,
  `P_λQ_λ = Q_λP_λ = 0` and `v(Q_λ f) ≥ v(f)`, where `P_λ` restricts to the
  resonance set `R_λ = {g : θg = g, χ(g) = λ}`. Hence `ker(σ−λ) = P_λK` and
  `im(σ−λ) = ker P_λ`. The fixed field is `k((t^{Γ_σ}))`, powers of `σ−λ` have
  the same kernel, and split polynomial operators `p(σ)` behave alike.
- **Koszul contraction (Lemma 5.1, Theorem 5.2, Corollaries 5.3, 5.4).** For `d`
  commuting such automorphisms with common fixed field `F`, an explicit strong
  homotopy retracts the Koszul complex onto its joint-resonant coefficients:
  `H^r(Z^d, K_add) ≅ F^{C(d,r)}`, zero for `r > d`. Simultaneous additive
  equations have exact criteria and a formula for the normalized solution, and
  the projection onto `F` is parameter-free definable.
- **Multiplicative equations (Lemma 6.1, Corollary 6.2, Theorems 6.3, 6.4).**
  `x = c t^g exp(h)` with `h` infinitesimal; `H^r(Z^d, U_1) ≅ m_F^{C(d,r)}`;
  `σy/y = f` is solvable iff one `g` satisfies `(θ−I)g = γ`, `χ(g) = c` and
  `Ph = 0`; the compatible system version needs one `g` for all `j`.
  `H^r(Z^d, K^×)` splits as a monomial-module part times `m_F^{C(d,r)}`; no smaller
  formula for the monomial part is claimed.
- **Rational dilations (Theorem 7.1, Examples 7.2, 7.3).** For divisible `Γ` and
  positive rationals not all 1: `H^r(Z^d, K_add) ≅ k^{C(d,r)}` and
  `H^r(Z^d, K^×) ≅ (k^×)^{C(d,r)}`; `S_q y − y = f` is solvable iff `[f]_0 = 0`, and
  `S_q y / y = f` iff the leading coefficient of `f` is 1.
- **Recovery from one dilation (Theorem 8.1, Lemma 8.2).** For `Γ ≠ 0`
  2-divisible, the structure `(K, S_2)` in the language of rings plus `S_2`
  defines without parameters: `k`, the constant-coefficient map, the monomial
  group `t^Γ` (exactly the nonzero solutions of `S_2 x = x²`), every coefficient,
  the support relation, the order of exponents, `O` and `m`, leading terms and
  truncation at every monomial.
- **Unrestricted centralizer (Theorem 9.1, Corollary 9.2).** Every field
  automorphism commuting with `S_2` is `Σ a_g t^g ↦ Σ ρ(a_g) t^{θg}`, so
  `Cen_{Aut(K)}(S_2) ≅ Aut(k) × Aut_ord(Γ)`; no valuation preservation or
  strength is assumed, and both follow. A character twist commutes with `S_2`
  only if it is trivial.
- **Logic (Theorems 10.1, 10.2).** The complete theory of `(k((t^Γ)), S_2)` is
  undecidable: it uniformly interprets `(N, P(N); +, ∈)` with one monomial
  parameter, which is quantified away. A coefficient formula has `TP_2`; the
  support relation has the independence and strict order properties.
- **All rational dilations (Lemma 11.1, Theorems 11.2, 11.3).** For divisible
  `Γ ≠ 0` every `S_q`, `q ≠ 1`, defines the same data and every `S_r`, with the
  same centralizer; yet distinct `S_r`, `S_s` are not conjugate in `Aut(K)`, and
  `Nor(⟨S_2⟩) = Cen(S_2)`.
- **Examples (Section 12).** A shear of lexicographic `Q²` with fixed field
  `k((t^{{0}×Q}))`; a phase character on `C((t^Q))` with fixed field `C((t^Z))`,
  which is not algebraically closed; compatible tuples that are not exact.
- **Surreal and surcomplex transfer (Theorem 13.1).** Via `t^g = ω^{−g}` and
  set-sized localization of supports, for `No` and `No(i)` (coefficients `R`,
  `C`): the scalar and simultaneous equation criteria, definability of the
  coefficient field, Conway monomials, coefficients, natural valuation ring and
  truncations in the field expanded by `S_q`, and the centralizer: a class field
  automorphism commuting with `S_q` is `Σ c ω^a ↦ Σ ρ(c) ω^{θ(a)}` for unique
  `ρ ∈ Aut(k)` and an ordered additive class automorphism `θ` of `(No,+,<)`, with
  `ρ = id` on `No`.
- **Questions 15.1–15.3** (minimal closure for definable normal forms; a
  nontrivial coefficient action; definability from other exponent
  automorphisms such as shears) are left open.

## What the report does not claim

Section 14.3 keeps the source's non-claims in place and collects them in a
ledger of 33 items: 28 from the source and 5 added when the report joined the
collection. In brief:

- Not refereed. No theorem is Lean-verified and no Lean source accompanies the
  report; Section 14.1 is a formalization route only. No named published open
  problem is settled: not the existence or image of nontrivial exponential
  automorphisms of `No`, and not Camacho's monomial-definability question in the
  language without the dilation. Priority is not certified; the literature
  review was focused, not exhaustive. The source inspected only the catalogue,
  the root README and the surcomplex-automorphisms guide, and built nothing.
- Credited, not claimed: monomial and character lifts (Kaplan–Krapp–Serra and
  `saut`), the dilations themselves, Hahn background and the normal-form
  dictionary, the support-to-arithmetic principle (Camacho), the principal-unit
  logarithm; the Mahler identities are illustrations.
- Scope: coefficient action the identity; finite commuting families only;
  abelian `K^×`, not matrix gauge classification; no replacement for
  Faverjon–Roques and no theorem on variable-coefficient Mahler systems; no
  claim of Pal's residue difference closedness. The resonance projection is not
  a field homomorphism, and kernels do not give an eigenspace decomposition.
  The Koszul complex is additive, not a differential graded algebra. Full Hahn
  fields are essential; characteristic zero is retained (the recognition formula
  fails in characteristic two). No uniform algorithm on Hahn names.
- Logic: the undecidability concerns the complete theory of the stated
  structure, not every smaller valued-field language; the arithmetic comes from
  the expansion by `S_2`, not from naming a valuation ring. Interdefinability is
  not conjugacy.
- Proper classes: ordinary cohomology and complete theories are set-sized only;
  no set of class automorphisms or cochains; no birthday bound for the
  localizations. On `No(i)` the real axis is not recovered, and the centralizer
  contains all of `Aut(C)`. `S_q` is not the exponential, the omega-map, a
  derivation or an exponential-preserving automorphism; the fine topology is not
  used.
- The 66,131 finite checks certify no infinite statement, first-order
  interpretation or class statement.
- Added: no question of `saut` is answered, and its non-claims (the four-layer
  decomposition covers `G_v` only; `Aut(No(i))` is not classified) are extended
  only by the one subgroup `Cen(S_q)`; the rigidity report's Question 13.1 is
  untouched; the dilations are not the holonomic-rigidity report's argument
  dilations; the birthday-cutoffs undecidability is for a different expansion;
  no `dsup:` label has a Lean mapping.

## Relation to the neighbouring reports

Section 1.5 of the article gives these relations with labels.

**[surcomplex-field-automorphisms](../surcomplex-field-automorphisms/)** — `S_q`
is its `S_a` at `a = q` (`saut:eq:dilation`), and the maps `σ` are its
`M_{ρ,τ,χ}` (`saut:thm:monomial`) with `ρ = id`, `τ = θ`; the source credits that
construction. (1) *Consistent with* `saut:thm:decomp`: that theorem factors each
valued automorphism `α ∈ G_v` of `No(i)` uniquely as `u D_χ M_{ρ,τ}`; by Theorem
13.1(5), an automorphism commuting with some `S_q`, `q ≠ 1`, is an `M_{ρ,θ}`, so
it lies in `G_v` with `u = 1` and `χ = 1` (Theorem 9.1 is the set-sized
analogue). (2) *One subgroup beyond `G_v`*: `saut` states that its decomposition
covers `G_v` only, not `Aut(K)`, and that `Aut(K)` is not classified (items 1
and 10 of `saut:sec:nonclaims`; its README lists both). The centralizer here is
computed among all field automorphisms, with valuedness a conclusion. That
identifies one subgroup of the unrestricted group inside `G_v`; it classifies
nothing else, and both non-claims otherwise stand. (3) *Complementary to*
`saut:prop:nondefinability`, which shows `No` and `O` are not definable in the
pure field with any parameters: after adding `S_q`, `O`, the coefficient field,
the monomials and every coefficient become parameter-free definable (Theorems
8.1, 13.1(4)). The real axis `No` is still not claimed definable in `No(i)`.
(4) *Its questions*: none of the four questions of `saut:sec:questions`
(exponential image on the value group, omega-map compatibility, effective
descriptions in the leading-term kernel, real-form and continuity
classifications) is answered; the source says it does not settle the
exponential-automorphism image problems (Section 13.3). `saut` computes only the
centralizer of conjugation (`saut:thm:axis`) and never asserts that `S_r` and
`S_s` are conjugate, so Theorem 11.3 contradicts nothing there.

**[exponential-automorphism-rigidity](../../surreal/exponential-automorphism-rigidity/)**
— on `No`, `S_q` is its canonical lift `T̂_q` (`prop:hahn-lift`) of the
value-group dilation `T_q(γ) = qγ`, which has no exponential lift for rational
`q ≠ 1` (`thm:dilation`). Theorem 13.1(5) with `k = R` says the class field
automorphisms of `No` commuting with `S_q` are exactly the canonical lifts `T̂` of
ordered additive automorphisms `T` of `(No,+,<)`. Theorems 11.2 and 11.3 are new
statements about these maps. Which lifts commute with `exp` is not addressed;
its Question 13.1 (`q:image`) is untouched.

**[omnific-preserving-automorphisms](../../surreal/omnific-preserving-automorphisms/)**
(`opa:`) — its Part X (batch 34), from a manuscript that does not cite this
report, re-derives the difference core with trivial character: the weighted
Green operator `opa:us:thm:green` is Theorem 4.1's partial inverse with
`χ = 1` (dictionary `opa:us:rem:dsup`), proved directly on the class `No`;
`opa:us:thm:multiplicative` and the relative retraction
`opa:us:thm:retraction` specialize Theorem 6.3; `opa:us:thm:firstorder`
solves `σx − ax = b` with nonconstant `a`; `opa:us:thm:cocycles` gives
degree-one cohomology for every group with a central nonidentity element
(Theorem 7.1 has every degree for `Z^d`). A batch-34 paragraph in Section 1.5
records this; no statement here changes.

**[holonomic-rigidity-for-entire-hahn-functions](../holonomic-rigidity-for-entire-hahn-functions/)**
— the dilations of its batch-22 material are argument dilations
`f(z) ↦ f(λz)` of formal functions; `S_q` acts on the exponents of scalars. The
two share a word, not a theorem. Its batch-31 `hol:pc:cor:linear` (strongly
entire solutions of mixed differential–Mahler equations are polynomials)
concerns substitutions `f(P_j(z))` in the variable, not exponent dilations; a
batch-34 note in Section 1.2 compares it with the Mahler remark there.

**[birthday-cutoffs-and-hereditary-sets](../../foundations-and-computation/birthday-cutoffs-and-hereditary-sets/)**,
placed after the pin — the surreal field expanded by birthday interprets full
second-order arithmetic (`hset:prop:arithmetic`), has an undecidable complete
theory (`hset:cor:undecidable`) and the independence property (`hset:prop:ip`).
Section 10 here obtains the same kind of consequence, plus `TP_2` and the strict
order property, for a different expansion (a Hahn field with one exponent
dilation) by a different mechanism (Boolean coefficient coding, after Camacho).
Neither implies the other.

**[dynamics-and-normal-forms](../dynamics-and-normal-forms/)** (resonances and
centralizers of germs), **[analytic-geometry](../analytic-geometry/)** and
**[finite-deformations](../finite-deformations/)** (Koszul complexes of
polynomial ideals) share words only.

## Stale statements corrected (Appendix D.2)

The source compared itself with the collection at `465a54b`; Section 1.3 keeps
that comparison as written. Checked at the placement commit `7b5f934`, its
repository statements stand: the root README still documents strong Hahn
summation, the Neumann support lemma, coefficient maps, the infinitesimal
exponential and logarithm and algebraic closedness of Hahn fields (Lean
statements that prove nothing in this report), the catalogue still separates
fine-topology small nets from strong summation, and `saut` still constructs the
lifts. Neither the `saut` article nor the rigidity article has changed since the
pin. At the pin the catalogue listed 44 research reports in five families; batch
21 (placed in `d4e71b7`, after the pin) added two, among them the birthday-cutoffs
report compared above, and batch 22 adds further reports, this one among them.
The `saut` guide gained one paragraph after the pin, on two batch-21 reports that
use conjugation; it bears on nothing here. The source did not audit the `saut`
article; the relations above were checked against it.

## Build and reproduce

TeX Live or MiKTeX with newtxtext/newtxmath, amsmath/amsthm, mathtools,
geometry, microtype, booktabs, longtable, array, enumitem, xcolor, fancyhdr,
xurl, hyperref, bookmark and listings. No external figures or bibliography
file.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX) has 35 pages and no errors, undefined references
or citations, multiply defined labels, duplicate destinations, LaTeX or package
warnings, or overfull or underfull boxes. With the batch-34 paragraphs of
Section 1.5 (still 35 pages, every label number unchanged) the log also
contains one informational line "ignored: Infinite glue shrinkage found in box
being split" at a page break inside a `longtable`; it is not a warning. A clean
compile proves nothing about the proofs.

`code/verify.py` needs Python 3.10 or later and only the standard library. It
uses exact rational arithmetic, prints to standard output and writes no file.
**Do not run `code/Makefile` in this directory.** It is the source's Makefile
for its flat delivered layout (`article.tex`, `verify.py`, `verification.txt`
side by side): `make check` runs `python3 verify.py > verification.txt`,
overwriting the recorded output in place, and `make all` also rebuilds
`article.pdf` from `article.tex` beside it. Placed under `code/`, it would write
an unshipped `code/verification.txt`, and `make all` would fail for want of
`code/article.tex`. Run it on a copy. From this directory, with a fresh scratch
directory:

```sh
T=$(mktemp -d)
python code/verify.py > "$T/direct.txt"
diff --strip-trailing-cr "$T/direct.txt" data/verification.txt
cp code/verify.py code/Makefile "$T"/ && make -C "$T" check
diff --strip-trailing-cr "$T/verification.txt" data/verification.txt
```

Both were run for this report under Python 3.14.4 on Windows (the Makefile with
GNU Make, installed there as `mingw32-make`). Each printed 17 `PASS` groups and
`TOTAL: 66131 exact checks passed.`, and reproduced `data/verification.txt`
exactly apart from line endings (Windows writes CRLF). The checks cover finite
telescopes with their endpoint terms, finite diagonal Koszul models in
dimensions 1–5, initial coefficients of the Mahler product and character and
exponent identities; they prove no infinite statement, first-order
interpretation or proper-class statement. `PROOF_AUDIT.md` is the source's own
checklist and refers to the delivered file names (`article.tex`, `verify.py`,
`verification.txt`) in that flat layout.
