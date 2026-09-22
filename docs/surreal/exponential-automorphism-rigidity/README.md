# Cofinal displacement and the rigidity of exponential automorphisms

`article.pdf` (19 pages) — source `article.tex`, checks in `code/`, recorded
output in `data/`.

An unrefereed AI-assisted draft, dated 21 September 2026. Not refereed, not
machine-checked; the article states plainly that no Lean proof is claimed for
it.

## What it establishes

Let `F` be an ordered field carrying a total increasing ordered exponential
`E: (F,+) → (F_{>0},·)` that is **onto**, and let `w: F^× → Γ` be a
**nontrivial convex** valuation. No Hahn workspace, no completeness, no
saturation, no set-size hypothesis.

The engine is one finite lemma. For a unital field endomorphism `σ`, the
displacement `D(x) = σ(x) − x` is additive but is **not** a derivation; the
correct rule is the *twisted* product identity

    D(ab) = σ(a)·D(b) + b·D(a)

— with `σ(a)`, not `a`. Given `d = D(a) ≠ 0` and any bound `B > 0`, the single
probe pair `b = 2B(1+|σ(a)|)/|d|` and `ab` forces `max{|D(b)|, |D(ab)|} > B`.
Two probes, no transfinite construction, no surjectivity or order-preservation
of `σ` required — so it also covers self-embeddings and class-sized fields.

Around that:

- **Theorem 4.1 / Corollary 4.2.** A nonidentity exponential automorphism
  stabilizing `O_w` displaces value-group elements **cofinally and
  coinitially** — for every `M > 0` in `Γ` something moves up by more than `M`
  and something moves down by more than `M`. Hence `ρ_w: Aut_exp(F; O_w) →
  Aut(Γ,+,<)` is **injective**. The bridge is `ν = w∘E`, surjective, additive
  and order-*reversing*, whose kernel is a proper convex additive subgroup —
  and such a subgroup of an ordered field is bounded by a **field** element,
  not by an integer or a real. That distinction is the whole point: the finite
  surreals are bounded by `ω`.
- **Theorem 4.4.** Coarsening rigidity, faithfully on `Γ/Δ` for proper convex
  `Δ` — with stabilization of `Δ` as an *explicit hypothesis*.
- **Theorem 5.1 / Corollary 5.2.** Specialized to **No**: an exponential
  automorphism fixing every natural-valuation value is the identity, and
  therefore every exponential 1-automorphism of No is the identity. This is
  the report's claimed **negative answer to Question 5.4** of Kaplan–Krapp–Serra,
  *Decomposing the automorphism group of the surreal numbers*,
  arXiv:2509.22374v3. See the next section for exactly what that rests on.
- **Section 6.** Two *disjoint* obstruction mechanisms separating ordered-Hahn
  symmetry from exponential symmetry: bounded-layer reweightings `T_c` (bounded
  displacement) and positive rational dilations `T_r` (displacement image all
  of `Γ`, excluded by `Q`-linearity of `v∘exp` and a value comparison at `ω`,
  with a second proof using multiplication at `ω` and `ω²`).
  Every one of them **does** lift as an ordered field automorphism (Prop 6.3),
  so cofinal displacement is necessary but provably **not sufficient** for
  exponential lifting.
- **Section 7.** Here **assume additionally that `F` is real closed**. On
  `K = F(i)`, the intrinsic logarithmic modulus
  `L: K^× → F`, `L(z) = log √(z z̄)` — defined for every nonzero input,
  real logarithm only, no complex-log branch, no
  argument, no sin/cos at infinite arguments — gives
  `Aut_L(K) ≅ Aut_exp(F) × C₂`, with invisible value-group kernel exactly
  `{id, conjugation}`. Preservation of `F` and of conjugation is *derived*, not
  assumed, from `im(L) = F`.

## What the Question 5.4 answer rests on

The elementary engine has been checked independently of the author: the
twisted identity holds exactly, the untwisted version (`a` in place of
`σ(a)`) does not, and the two-probe amplification holds with margin
`2B + B|σ(a)|`. **That validates the engine only.** The report's conclusion
additionally rests on four things that the engine does not supply:

1. **The valuation step.** From `σ∘exp = exp∘σ` and `v(σy) = v(y)` one gets
   `v(exp(σx − x)) = 0` for all `x`, and then Proposition 2.3 —
   `ker(v∘exp) = O`, the finite surreals — makes *every* displacement finite.
   Proposition 2.3 is proved here from monotonicity of `exp` alone and uses no
   normal-form formula for the exponential, but it is a genuine extra step.
2. **`B = ω`.** The contradiction is Lemma 3.1 applied with `B = ω`. This is
   legitimate precisely because the bound in Lemma 2.2 is a *field* element;
   an integer or real bound would not close the argument.
3. **Imported surreal facts.** Gonshor's total increasing exponential on No
   extending real `exp`, with increasing inverse, and the natural valuation
   whose ring is the finite surreals. These are cited, not reproved.
4. **The reading of Question 5.4, checked 22 September 2026.** The pinned
   [KKS v3 PDF](https://arxiv.org/pdf/2509.22374v3), Definitions 2.4–2.5 and
   Remark 2.6 on page 4, confirms that a 1-automorphism fixes each leading
   term, hence each value `v(y)`. Proposition 5.2 on page 10 treats the
   strongly `R`-linear case; Question 5.4 there asks the unrestricted question
   used by this report's Corollary 5.2. The version remains **v3, submitted
   23 April 2026, PDF dated 27 April 2026**. This replaces the earlier
   unchecked-source disclaimer; it verifies the interpretation, not priority.

The article also concedes that the elementary displacement lemma may be
familiar in other language, and that a specialist may recognize further
antecedents; the searches behind it were targeted, not exhaustive.

## Where it sits

`surreal/` — the surreal field **No** itself, plus `No[i]` in Section 7.
It is **independent of every other report here** and can be read on its own.

The [Hahn-evaluation report](../hahn-evaluation-at-omega/) gives related
coefficient-fixing maps obtained by changing exponents. The present report
asks which value-group actions can also preserve the exponential. The
surcomplex analysis and foundations reports use surreal exponential fields
as background; no result from those reports is needed in these proofs.

**Disambiguation — three unrelated things in this collection are called
"rigidity."** The *all-scale polynomial rigidity* of
[`surcomplex/analysis`](../../surcomplex/analysis/) (`f:thm-rigidity`) is a
different theorem about a different object: it says a class function on `No[i]`
that is Hahn-entire at every scale is a polynomial. The *scalar rigidity* of
[`gamma-functions`](../gamma-functions/) is a third: compatibility with the
Berarducci–Mantova derivation forces a gauge to vanish. What is proved here is
neither — it is faithfulness of `ρ_w`. The growth scale in this report is
nothing but the natural-valuation value read through `ν = w∘E`; it is not a
Hardy-field or germ order, and not a scale of function growth. The three
rigidity statements have different objects and hypotheses.

## What it does NOT claim

- **Rigidity here means faithfulness, not triviality.** The article states
  plainly that this is **not** a claim of total automorphism rigidity for No.
- The **image** of `ρ_v` is not classified. The article shows only that it is
  strictly smaller than all of `Aut(No,+,<)` and that a cofinal-displacement
  test alone cannot characterize it. Question 10.1 leaves this open.
- Coarsening rigidity **requires** as an explicit hypothesis that the
  automorphism stabilize the chosen convex subgroup. The article does not
  assert that every exponential automorphism stabilizes every coarsening.
- Do **not** weaken `v(σy) = v(y)` in Theorem 5.1 to preservation of
  comparisons `v(y) < v(z)`: the latter is automatic for ordered field
  automorphisms and the theorem would be false as stated.
- Theorem 8.2's non-expansion hypothesis is **global**. The article warns it
  must not be used to exclude surreal exponential derivations that are merely
  small on finite elements.
- No global surreal composition theory, no classification of
  omega-map-preserving automorphisms, and no claim that an arbitrary ordered
  additive value-group automorphism lifts exponentially — Section 6 disproves
  that one.
- `Aut_exp(No)` and similar expressions are metamathematical shorthand about
  individual class maps, not assertions that the collection is a set or an NBG
  class; class-sized coarsening quotients are handled relationally, as
  `τ(γ) − γ ∈ Δ`.
- The structure on `No[i]` is specified by `L(z) = log|z|` only. There is no
  unspecified surcomplex exponential, no complex-logarithm branch, no analytic
  path theory.
- The Python checks verify finite algebraic identities and finite Hahn
  analogues only. They are not an implementation of No, do not verify infinite
  summability, and certify no theorem.
- Repository documentation was inspected at commit
  `aa846271b4dcae2c055b216126a87210292ec19b` of `VladimirReshetnikov/Surreal`
  and is cited as **research context only**, not as an external proof source.
  That snapshot records the original research context; this maintained copy
  now belongs to the collection and includes later exposition revisions.
  The named question is external (KKS Question 5.4).

## Build

MiKTeX or TeX Live with the usual AMS packages plus `newtx`, `geometry`,
`microtype`, `fancyhdr`, `hyperref` and `cleveref`. No external `.bib`, no
figures, no distributed font files.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Without `latexmk`, run `pdflatex` until cross-references settle. Last verified
build: exit 0, **19 pages**, no LaTeX warnings, no undefined references, zero
overfull or underfull boxes.

## Rerun the checks

Python 3.10 or later. Standard library only — `fractions`, `random`,
`unittest`; no third-party dependency.

```sh
python code/verify-identities.py
```

Seven test methods, deterministic seed `20260921`, 300 exact-rational trials
per randomized test: the twisted product identity; the two-probe inequality;
value-group reweighting; the finite Hahn lift (additive *and* multiplicative
compatibility); the bounded-layer/coarsening analogue; the rational-dilation
polynomial identity, with an exhaustive check that `r² − r = 0` only at
`r = 0, 1` over numerators `−10..10` and denominators `1..7`; and
multiplicativity of the squared complex modulus. Last run here: `Ran 7 tests
in 0.201s`, **OK**, all seven, on Python 3.14.4.

**This script writes nothing.** It has no `open()`, no path handling; it prints
to stdout and exits with the `unittest` status. `data/verification-output.txt`
is a hand-captured stdout redirect, so running the checks cannot silently
rewrite it — but for the same reason, do not redirect a run over it, and if you
want to regenerate it, do so on a copy and compare.

The value group is modelled as lexicographically ordered `Q³` and series as
finite-support dicts. That is a toy model, deliberately: it protects against
elementary formula and sign mistakes and nothing more.
