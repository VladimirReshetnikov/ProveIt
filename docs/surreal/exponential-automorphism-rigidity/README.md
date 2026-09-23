# Cofinal displacement and the rigidity of exponential automorphisms

`article.pdf` (29 pages) — source `article.tex`, checks in `code/`, recorded
output in `data/`, external-source audit in
`05-exponential-valuation-SOURCE_AUDIT.md`.

An unrefereed AI-assisted draft, dated 21 September 2026. Not refereed, not
machine-checked; the article states plainly that no Lean proof is claimed for
it.

## What it establishes

Let `F` be an ordered field carrying a total increasing ordered exponential
`E: (F,+) → (F_{>0},·)` that is **onto**, and let `w: F^× → Γ` be a
**nontrivial convex** valuation. No Hahn workspace, no completeness, no
saturation, no set-size hypothesis. Two of those standing hypotheses are
later traded away, and Section 4.2 says exactly which.

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
- **Theorem 4.6.** Coarsening rigidity, faithfully on `Γ/Δ` for proper convex
  `Δ` — with stabilization of `Δ` as an *explicit hypothesis*.
- **Theorem 5.1 / Corollary 5.2.** Specialized to **No**: an exponential
  automorphism fixing every natural-valuation value is the identity, and
  therefore every exponential 1-automorphism of No is the identity. This is
  the report's claimed **negative answer to Question 5.4** of Kaplan–Krapp–Serra,
  *Decomposing the automorphism group of the surreal numbers*,
  arXiv:2509.22374v3. See the next section for exactly what that rests on.
- **Section 8.** Two *disjoint* obstruction mechanisms separating ordered-Hahn
  symmetry from exponential symmetry: bounded-layer reweightings `T_c` (bounded
  displacement) and positive rational dilations `T_r` (displacement image all
  of `Γ`, excluded by `Q`-linearity of `v∘exp` and a value comparison at `ω`,
  with a second proof using multiplication at `ω` and `ω²`).
  Every one of them **does** lift as an ordered field automorphism (Prop 8.3),
  so cofinal displacement is necessary but provably **not sufficient** for
  exponential lifting.
- **Section 9.** Here **assume additionally that `F` is real closed**. On
  `K = F(i)`, the intrinsic logarithmic modulus
  `L: K^× → F`, `L(z) = log √(z z̄)` — defined for every nonzero input,
  real logarithm only, no complex-log branch, no
  argument, no sin/cos at infinite arguments — gives
  `Aut_L(K) ≅ Aut_exp(F) × C₂`, with invisible value-group kernel exactly
  `{id, conjugation}`. Preservation of `F` and of conjugation is *derived*, not
  assumed, from `im(L) = F`.

Weakened hypotheses, each independent of the surreal application:

- **Theorem 4.4, rigidity from one visible exponential scale.** It needs only
  some `H > 0` with `w(E(H)) < 0`, and therefore **drops surjectivity of `E`**,
  the standing convention stated in Section 1.1 ("In particular, `E` is onto
  and has an increasing inverse"), together with the `log` that convention
  supplies. Corollary 4.2's self-embedding version is recovered as the case
  where `E` is onto and `w` is nontrivial.
- **Corollary 4.5, the detector.** The same mechanism with no ordering, no
  convexity and no restriction on the characteristic: if `E(x)` being a
  valuation unit forces `v(x) ≥ β` for one fixed `β`, then commuting with `E`
  and fixing `v` pointwise forces the identity. For the surreal exponential
  this holds with `β = 0`, giving a second proof of Theorem 5.1 that never
  mentions the bound `ω`.
- **Theorem 3.4, one identity for displacement and derivation.** Displacements
  and ordinary derivations are both *σ-derivations*, `δ(ab) = σ(a)δ(b) +
  bδ(a)`. No nonzero σ-derivation of a field with a nontrivial surjective
  valuation has `v(δ x) ≥ β` for a single fixed `β` — at any valuation rank,
  with no ordering and no convexity.
- **Theorem 6.1, profile rigidity.** `ν = w∘E` is additive with proper convex
  kernel, so `ν(σx) = ν(x)` on any additive *generating set* already forces
  every displacement into that kernel. One **final interval** suffices:
  `z = |c|+|x|+1`, `y = z+x` puts both above `c` with `x = y−z`. It assumes
  neither that `σ` fixes valuations nor that it commutes with `E` anywhere.
  Corollary 6.2 turns this into a tail-commutation statement; Corollary 6.3
  compares two automorphisms by profile alone.

New consequences, rather than weaker hypotheses:

- **Theorem 7.1.** The multiplicative motion `{σ(y)/y : y > 0}` of a
  nonidentity exponential automorphism is cofinal and coinitial. No valuation
  is used.
- **Theorem 7.2 / Corollary 7.3.** For a nonidentity `σ` that fixes every
  value but is *not* assumed to commute with `E`, the valuations of the
  commutation defects `C_σ(x) = σ(Ex)/E(σx)` are cofinal and coinitial, since
  `w(C_σ(x)) = −ν(D_σ x)`. A bound on even one side forces `σ = id`. The
  theorem is conditional: it does not assert that such a `σ` exists.
- **Theorem 10.3 / Corollary 10.4.** The differential counterpart, strengthened.
  Theorem 10.1 forbids `w(∂y) ≥ w(y)` — the case `γ = 0` — under an ordering
  and a convex valuation. Theorem 10.3 forbids `v(∂y) ≥ v(y) + γ` for **any**
  fixed `γ`, over any nontrivially valued field, with no ordering and with `E`
  merely a nowhere-vanishing map satisfying `∂(E x) = E(x)∂x`. Rescaling by a
  nonzero scalar does not help. Applied to the Berarducci–Mantova derivation:
  no fixed nonzero surreal multiple of it is globally valuation-contracting.
- **Section 11, sharpness over `R((t))`.** Disjoint from the non-lifting
  families of Section 8. The substitution `f(t) ↦ f(t+t²)` fixes every leading
  term yet has absolute displacement valuation unbounded below; it commutes
  with the canonical partial exponential on `R[[t]]` **at every finite
  argument**, which shows that local exponential compatibility is not enough;
  `T = id + N` with `N` nilpotent is a nonidentity additive automorphism with
  uniformly bounded displacement, so a purely additive analogue of the
  amplification lemma is **false**; and `∂ = t² d/dt` is a nonzero contracting
  derivation carrying only a *partial* exponential.

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
4. **The reading of Question 5.4, checked 22 September 2026.** Corollary 5.2
   turns Theorem 5.1 into an answer by way of a single implication: a
   1-automorphism fixes every *leading term*, hence every value `v(y)`.
   Leading coefficients play no role in the proof. The pinned
   [KKS v3 PDF](https://arxiv.org/pdf/2509.22374v3), Definitions 2.4–2.5 and
   Remark 2.6 on page 4, confirms that implication. Proposition 5.2 on page 10
   treats the strongly `R`-linear case; Question 5.4 there asks the
   unrestricted question used by Corollary 5.2.
   `05-exponential-valuation-SOURCE_AUDIT.md` records what was inspected, and
   both PDF pages were **visually inspected**. The version remains **v3,
   submitted 23 April 2026, PDF dated 27 April 2026**; **keep that version
   pinning prominent.** This verifies the interpretation, not priority: no
   exhaustive search for a later resolution was made, several search results
   were irrelevant, and no priority conclusion is drawn from their
   unhelpfulness. Theorem 5.1 needs neither strong additivity nor pointwise
   fixation of `R`, which KKS Proposition 5.2 assumes.

The article also concedes that the elementary displacement lemma may be
familiar in other language, and that a specialist may recognize further
antecedents; the searches behind it were targeted, not exhaustive.

## Where it sits

`surreal/` — the surreal field **No** itself, plus `No[i]` in Section 9.

This report is **no longer independent of the rest of the collection**, and
two earlier claims here have been withdrawn as false.

- Section 10.2 proves a statement about the **Berarducci–Mantova derivation**
  on No: no fixed nonzero surreal multiple of it is globally
  valuation-contracting. [`gamma-functions`](../gamma-functions/) imports that
  same derivation for its scalar rigidity, and
  [`tail-spans-and-differential-transcendence`](../tail-spans-and-differential-transcendence/)
  cites the Berarducci–Mantova restriction rather than reproving it. These are
  statements about one shared object, not shared theorems.
- [`gamma-functions`](../gamma-functions/) already links here from its own
  disambiguation note.
- The [Hahn-evaluation report](../hahn-evaluation-at-omega/) gives related
  coefficient-fixing maps obtained by changing exponents. The present report
  asks which value-group actions can also preserve the exponential.
- [`genetic-gaps-and-primitives`](../genetic-gaps-and-primitives/) treats
  *order* automorphisms of gap indicators — a different group acting on a
  different object, but enough to make "nothing else studies automorphisms"
  wrong as stated.
- Ehrlich–Kaplan on surreal ordered exponential *fields* is cited in
  `surcomplex/analysis` and in `foundations-and-computation/foundations` for
  the exponential construction, and two bibliography entries to
  Kaplan–Krapp–Serra appear in the sources of
  `surcomplex/dynamics-and-normal-forms`, both used only for class-size
  conventions. Those reports use surreal exponential fields as background;
  no result from them is needed in these proofs.

The rigidity theorems can still be read without reading anything else.
[surcomplex-field-automorphisms](../../surcomplex/surcomplex-field-automorphisms/)
reprints `lem:amplify`, the faithfulness of Corollary 4.2, Theorem 5.1 and
Corollary 5.2, Theorem 8.4 (second proof) and Theorem 9.2 with its kernel
clause for `F = No`, with attribution. It then studies plain field
automorphisms of `No(i)`, where `Aut_L(No(i))` is a proper subgroup of the
real-axis stabilizer `Aut(No) × C₂` (its (1.2)).

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

The canonical Hahn lift of the dilation `T_q` is studied as a field
automorphism in
[single-dilation-hahn-support](../../surcomplex/single-dilation-hahn-support/):
its centralizer among all field automorphisms (`dsup:thm:centralizer`) and the
non-conjugacy of distinct rational dilations (`dsup:thm:nonconjugate`). Question
13.1 is untouched there.

## What it does NOT claim

- **Rigidity here means faithfulness, not triviality.** The article states
  plainly that this is **not** a claim of total automorphism rigidity for No.
- The **image** of `ρ_v` is not classified. The article shows only that it is
  strictly smaller than all of `Aut(No,+,<)` and that a cofinal-displacement
  test alone cannot characterize it. Question 13.1 leaves this open.
- Coarsening rigidity **requires** as an explicit hypothesis that the
  automorphism stabilize the chosen convex subgroup. The article does not
  assert that every exponential automorphism stabilizes every coarsening.
- Do **not** weaken `v(σy) = v(y)` in Theorem 5.1 to preservation of
  comparisons `v(y) < v(z)`: the latter is automatic for ordered field
  automorphisms and the theorem would be false as stated.
- Theorem 10.1's non-expansion hypothesis is **global**, and so is Theorem
  10.3's bound `v(∂y) ≥ v(y) + γ`. Both compare output with input at *every*
  nonzero element. Neither must be used to exclude surreal exponential
  derivations that are merely small on finite elements, or contracting on a
  subring, on a support class, or on a bounded domain — Section 11.4 exhibits
  exactly such a contracting derivation.
- Theorem 7.2 is **conditional**. It says how badly a nonidentity value-fixing
  automorphism must fail to commute with `exp`; it does not assert that one
  exists, and by Corollary 4.2 none commutes with `exp`.
- Profile rigidity does **not** say that `ν(x)` reconstructs `x`. The profile
  stays highly non-injective, and none of Section 6 is an approximation
  procedure for normal forms. Corollary 6.3 uses surjectivity of one of the
  two maps; Theorem 6.1 uses none.
- The `R((t))` examples in Section 11 are **not** counterexamples to any
  theorem here. In particular no total exponential preserved by the
  substitution automorphism is supplied — Theorem 5.1 proves that none exists.
- The application to the Berarducci–Mantova derivation uses only its existence
  and its exponential-compatibility law. It does **not** contradict formal
  operator exponentials built from derivations that satisfy contraction
  hypotheses on restricted domains rather than the total compatibility law.
- No global surreal composition theory, no classification of
  omega-map-preserving automorphisms, and no claim that an arbitrary ordered
  additive value-group automorphism lifts exponentially — Section 8 disproves
  that one.
- `Aut_exp(No)` and similar expressions are metamathematical shorthand about
  individual class maps, not assertions that the collection is a set or an NBG
  class; class-sized coarsening quotients are handled relationally, as
  `τ(γ) − γ ∈ Δ`.
- The structure on `No[i]` is specified by `L(z) = log|z|` only. There is no
  unspecified surcomplex exponential, no complex-logarithm branch, no analytic
  path theory. The surcomplex classification is **derived** from the range of
  `L`; the article notes in one sentence that the shorter route, which assumes
  commutation with conjugation and preservation of `E` on the real axis, proves
  strictly less and is not used.
- The Python checks verify finite algebraic identities, finite Hahn analogues
  and truncated Laurent-series computations only. They are not an
  implementation of No, do not verify infinite summability, and certify no
  theorem.
- Repository documentation was inspected at commit
  `aa846271b4dcae2c055b216126a87210292ec19b` of `VladimirReshetnikov/Surreal`
  and is cited as **research context only**, not as an external proof source.
  That snapshot records the original research context; this maintained copy
  now belongs to the collection and includes later exposition revisions.
  The named question is external (KKS Question 5.4).

## A correction carried in the staged audit

`05-exponential-valuation-SOURCE_AUDIT.md` is the source audit that arrived
with one of the merged manuscripts. Its external-source section is what
item 4 above now rests on. Its **repository-comparison section is wrong**, and
the file carries an appended correction saying so: it pins revision
`608dd23c0539fce73723843949ee627641c27b30` and concludes that the collection
held no exponential-automorphism report, whereas `git ls-tree -d` at that
revision lists this directory with the 1310-line article already in it. What
the audit actually inspected was `docs/README.md`, whose surreal table had no
exponential row at that revision. Do not propagate that conclusion, and do not
treat the catalogue as a substitute for the tree.

## Build

MiKTeX or TeX Live with the usual AMS packages plus `newtx`, `geometry`,
`microtype`, `fancyhdr`, `hyperref` and `cleveref`. No external `.bib`, no
figures, no distributed font files.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Without `latexmk`, run `pdflatex` until cross-references settle. Last verified
build: exit 0, **29 pages**, no LaTeX warnings, no undefined references, zero
overfull or underfull boxes.

## Rerun the checks

Three independent check files are kept here. None of them certifies a theorem;
each protects against elementary formula and sign mistakes.

**`code/verify-identities.py`** — Python 3.10 or later, standard library only
(`fractions`, `random`, `unittest`).

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
in 0.435s`, **OK**, all seven, on Python 3.14.4.

**This script writes nothing.** It has no `open()`, no path handling; it prints
to stdout and exits with the `unittest` status. `data/verification-output.txt`
is a hand-captured stdout redirect, so running the checks cannot silently
rewrite it — but for the same reason, do not redirect a run over it, and if you
want to regenerate it, do so on a copy and compare.

**`code/04-exponential-automorphism-verification.py`** — needs SymPy; the
version used for the recorded run is pinned in
`data/04-exponential-automorphism-requirements.txt` (`sympy==1.14.0`).

```sh
python code/04-exponential-automorphism-verification.py
```

Seed `20260922`. It checks the twisted product identity and the amplification
margin; 250 exact rational amplification samples including signed images; both
substitution-inverse identities modulo `t¹³`, printing the inverse parameter
`t − t² + 2t³ − 5t⁴ + 14t⁵ − 42t⁶ + 132t⁷ − 429t⁸`; the Laurent displacement
coefficient `−m` at exponent `1−m` for `m = 1..12`; 40 additive
inverse/nilpotence checks with the nonmultiplicativity witness; quadratic norm
multiplicativity; and partial-exponential/substitution compatibility modulo
`t¹³`. **309 exact checks passed** in the recorded run (Python 3.13.5) and in a
rerun here (Python 3.14.4, SymPy 1.14.0). The recorded output is
`data/04-exponential-automorphism-verification_results.txt`. It prints to
stdout only.

**`code/05-exponential-valuation-verify.py`** — Python 3.10 or later, no
third-party packages; `python -O` is rejected.

```sh
python code/05-exponential-valuation-verify.py --output /some/scratch/path.json
```

Default seed `20260922`, 1,000 samples: **6,132 named checks** — two universal
polynomial identities, two inverse-composition checks through order 48, 128
leading-displacement formula checks, and six families on 1,000 deterministic
randomized examples (substitution additivity and multiplicativity, leading-term
preservation, derivation Leibniz, derivation valuation gain, ordered-witness
arithmetic). A rerun here on Python 3.14.4 reproduced `"status": "PASS"` and
the same 6,132 total as the recorded run in
`data/05-exponential-valuation-verification.json`.

**Pass `--output` explicitly.** Unlike the other two, this script *writes* a
file, and its default path is computed relative to the script's own location:
after staging into `code/`, that default lands a `verification.json` in this
report directory. Send it to a scratch path and compare against
`data/05-exponential-valuation-verification.json` by hand.

The value group in the first script is modelled as lexicographically ordered
`Q³` and series as finite-support dicts; the other two work with truncated
rational Laurent series. Those are toy models, deliberately: they protect
against elementary formula and sign mistakes and nothing more.
