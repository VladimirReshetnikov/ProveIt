# Three Duals at Surreal Scales

**Strong Hahn operators, completion defects, and invisible functionals**
Research report, 22 September 2026, built from one manuscript (item 04 of the
collection's nineteenth batch, prepared for Vladimir Reshetnikov, written
against repository revision `048b72c`, placed at `52c7ab6`). AI-assisted
draft; not refereed; no Lean formalization.

```
article.tex        the report, standalone LaTeX with an internal bibliography
article.pdf        the compiled report, 34 pages (title, contents i-ii, pages 1-31)
README.md          this guide
source_audit.md    the manuscript's own repository and literature audit, as delivered
code/              verify_examples.py            exact finite checks (standard library only)
data/              verification_report.json      recorded output of that program
```

Every label in `article.tex` carries the prefix `duals:`. The 70 labels of the
delivered manuscript were all kept, each with the prefix added; seven labels
were added at placement (`duals:sec:conventions`, `duals:rem:order-unit`,
`duals:rem:ihs-riesz`, `duals:rem:basechange-collection`,
`duals:sec:collection`, `duals:tab:ihs`, `duals:app:provenance`). No `duals:`
label currently has a mapping in the [formalization ledger](../../FORMALIZATION.md).
The files in `code/` and `data/` and `source_audit.md` are byte-identical to
the delivery; `source_audit.md` describes the repository at the manuscript's
pin, not the current tree (see "Relation to neighbouring reports").

## The setting

For a field `k`, a set-sized ordered abelian group `Γ` and a `k`-vector
space `V`, let `K = k((t^Γ))` and `V_Γ = V((t^Γ))` (well-ordered supports,
coefficientwise convolution, valuation `v` = least exponent). Inside `V_Γ`
the report separates three things:

- `E_Γ(V) = span_K V ≅ K ⊗_k V`, the algebraic scalar extension;
- `C_Γ(V)`, its closure (= completion) in the intrinsic valuation topology;
- `V_Γ` itself, the closure under strong Hahn sums.

For a complex Hilbert space `H` it compares three duals of `H_Γ = H((t^Γ))`,
the Hahn–Hilbert space of the spectral report (called `𝓗_Γ` there):
`D_rep` (functionals `x ↦ ⟨x, y⟩`), `D_str` (strong functionals) and
`D_cont` (valuation-continuous functionals).

Words with one meaning each here (Section 1.4): **strong** = preserves strong
summability of every family *and* commutes with its sum (the "strongly linear"
of `dyn:def:summable`, here `K`-linear; not the strong operator topology);
**continuous**, **completion** = intrinsic valuation topology of the one fixed
workspace, never the fine topology; **cofinality** `cf(Γ)` and "Γ cofinal in
Δ" as in the entire-functions report (`ent:rem:one-name`); an **order unit**
is `α > 0` with `nα` cofinal; **noncyclic** = `Γ ≠ 0` not ordered-isomorphic
to `Z`; **bounded** = bounded by a positive element of `F = R((t^Γ))`;
**invisible** = zero on every constant vector; **Riesz** = Riesz
representation, not Riesz spectral projections. Inner products are linear in
the first variable, as in Part I of the spectral report.

## What the report claims

Numbers refer to the built `article.pdf`.

1. **Strong operators (Theorem 3.2, Corollary 3.3).** For arbitrary `k`-vector
   spaces `V, W` and every ordered `Γ` (including `0`),
   `Hom_K^str(V_Γ, W_Γ) ≅ Hom_k(V, W)((t^Γ))` by convolution: every strong
   `K`-linear map is one Hahn series of *arbitrary* `k`-linear coefficient maps
   with one global well-ordered support. The proof is a descending-support
   argument; no topology on `V`, Baire category or adjoint is used. Every
   strong map is valuation-continuous.
2. **Completion is a coefficient-rank condition (Proposition 4.1, Theorem
   4.2).** `x ∈ E_Γ(V)` iff all coefficients of `x` span a finite-dimensional
   space; for `Γ ≠ 0`, `x ∈ C_Γ(V)` iff the coefficients below every cut
   `γ ∈ Γ` do. Example 4.3 gives a vector outside `C_Γ(V)` that no finite
   coefficient span approximates.
3. **Which groups (Theorems 4.5, 4.6; Remark 4.7).** For infinite-dimensional
   `V` and `Γ ≠ 0`: `C_Γ(V) = V_Γ` iff `Γ ≅ Z`; `E_Γ(V) ⊊ C_Γ(V)` iff
   `cf(Γ) = ℵ0`. Hence the trichotomy `E ⊊ C = V_Γ` (`Γ ≅ Z`),
   `E ⊊ C ⊊ V_Γ` (noncyclic, countable cofinality), `E = C ⊊ V_Γ`
   (uncountable cofinality). An order unit is sufficient but not necessary
   for the middle case.
4. **Completeness and extension (Proposition 5.1, Theorem 5.3).** `V_Γ` is
   spherically complete at every rank with no topology on `V`; a contractive
   Hahn–Banach extension theorem over arbitrary `Γ`, proved in full (a
   classical mechanism, using choice).
5. **The continuous dual (Theorem 6.3).** Restriction to constants gives an
   exact sequence `0 → N_Γ(V) → D_cont(V_Γ) → P_Γ(V) → 0`, where `P_Γ(V)` is
   the space of `k`-linear maps `V → K` with a common lower valuation bound
   and `N_Γ(V)` the continuous functionals zero on constants; on strong
   functionals, restriction is injective with image `V^#((t^Γ))`.
6. **Invisible functionals (Theorem 6.4, Corollary 6.5).** For `Γ ≠ 0`,
   `C_Γ(V)` is exactly the common kernel of `N_Γ(V)`; nonzero invisible
   functionals exist iff `dim V = ∞` and `Γ` is noncyclic; none is strong.
7. **Two failures of strongness (Theorem 7.1, Corollary 7.2, Theorem 7.3).**
   For `dim V = ∞` and noncyclic `Γ`, a continuous functional can annihilate
   every term of a strong sum but not the sum, and another can map a strongly
   summable family to the non-summable family `(1)_n`; the second is not
   strong plus invisible, and `D_cont / (D_str + N_Γ) ≅ P_Γ(V) / V^#((t^Γ))`
   is nonzero. `D_cont = D_str` iff `dim V < ∞` or `Γ ≅ Z`.
8. **Three duals (Proposition 8.2, Theorems 8.3–8.4, Corollary 8.6,
   Proposition 8.7).** Continuous maps on `H_Γ` are exactly those with a
   positive `F`-valued bound; the coefficientwise extension of an ordinary
   unbounded functional has exactly the positive infinite scalars as bounds.
   `D_str ≅ H^#((t^Γ))`, `D_rep ≅ H'((t^Γ))` and
   `D_str / D_rep ≅ (H^#/H')((t^Γ))`. For infinite-dimensional `H`:
   `D_rep ⊊ D_str = D_cont` if `Γ ≅ Z`, and `D_rep ⊊ D_str ⊊ D_cont` if `Γ` is
   noncyclic; all three coincide for finite-dimensional `H`. For separable
   `H`, `dim_K(D_str/D_rep) ≥ 2^𝔠`.
9. **A hyperplane with no orthogonal geometry (Theorems 9.1, 9.2).** The
   kernel of the extension of an ordinary unbounded functional is a
   valuation-closed hyperplane, closed under strong sums, with a strong
   bounded projection `P_M`, but zero orthogonal complement; the distances
   from an exterior constant have exactly `0` and the positive
   infinitesimals as nonnegative lower bounds, and no infimum in `F`.
10. **Enlarging the exponent group (Theorem 10.1).** For nonzero
    `Γ ⊆ Δ`: `E_Δ(V) ∩ V_Γ = E_Γ(V)`, and `C_Δ(V) ∩ V_Γ` is `C_Γ(V)` if `Γ`
    is cofinal in `Δ` and collapses to `E_Γ(V)` if not. Explicit example
    with `Γ = Q ⊂ Δ = Qω + Q ⊂ No`: `x = Σ ω^(-n) e_n` is in the completion
    over `Q` and leaves it once the tolerance `ω^(-ω)` is admitted
    (Section 10.2, equation (11.2)).

Section 11 transports everything into `No` and `No[i]` through fixed
normal-form workspaces (`t^γ ↦ ω^(-γ)`).

## What the report does not claim

Appendix A lists 26 non-claims, each also stated at its point of use; none of
the manuscript's limitations was dropped. The main ones:

- Hahn summation, non-Archimedean Hahn–Banach, spherical completeness and
  failures of Riesz representation or orthogonal complementation are **not**
  claimed as new; strongly linear maps are established (Bagayoko–Krapp–
  Kuhlmann–Panazzolo–Serra). The proposed contribution is the combined
  completion–duality–enlargement package.
- No named published conjecture is claimed solved. The repository and
  literature comparisons were targeted; **priority is not certified**.
  Ingleton's paper and the Aguayo–Nova paper were not read in full.
- **Not refereed; not verified in Lean** or any other proof assistant.
- Hahn–Banach uses choice; invisible functionals are existence results, not
  formulas. The exact sequence has no canonical splitting; invisible
  functionals have no canonical transport under enlargement.
- No least real-Hahn operator norm is defined; `F`-valued boundedness is not
  an ordinary norm estimate.
- Everything is set-sized: no Zorn argument over a proper class, no dual of a
  class-sized space over `No[i]`; the intrinsic topology is not the fine
  topology; a Hilbert vector is not a surcomplex scalar.
- The finite program checks finite identities and prefixes only (see below).

## Relation to neighbouring reports

Section 12 and its Table 1 compare the report with
[Infinite-dimensional Hahn spectral theory](../infinite-dimensional-hahn-spectral-theory/),
citing it only by label because that report is receiving additions:

- `ihs:hh:thm:adjoint` (adjointable = `B(H)((t^Γ))`) sits inside Theorem 3.2
  (strong = `End_C(H)((t^Γ))`); both inclusions
  `B(H)((t^Γ)) ⊆ End_C(H)((t^Γ)) ⊆ End_K^cont(H_Γ)` are proper for
  infinite-dimensional `H` and noncyclic `Γ`. The algebraic maps of
  `ihs:hh:thm:defect` are strong and generally not adjointable.
- `ihs:hh:prop:riesz` (a non-represented continuous functional) is shown in
  Remark 8.5 to be **strong**, with a discontinuous leading coefficient, so it
  lies in the first gap `D_str / D_rep`, not the second. This is an editorial
  comparison added at placement.
- `ihs:hh:thm:closedrange` (closed range with zero orthogonal complement,
  infinite codimension) is the in-collection predecessor of Theorem 9.1 (a
  hyperplane). `ihs:hh:prop:complete` (rank-one metric completeness) is
  contained in Proposition 5.1. `ihs:hh:prop:inner` is Proposition 8.1.
  `ihs:hh:cor:autobounded` and `ihs:hh:thm:norm` are the bounded-coefficient
  counterparts of Proposition 8.2 and Theorem 8.3. `ihs:hh:cor:extension`
  (persistence under every enlargement) answers a different question from
  Theorem 10.1. `ihs:warn:three` ("not `H ⊗ K`") is made exact by Theorems
  4.2 and 4.6. For Part II, `ihs:rf:lem:strongaction` is contained in
  Theorem 3.2 with `V = C^(I)`, and `ihs:rf:prop:noconv` is the scalar form of
  the two-scale phenomenon.

[Entire functions at arbitrary rank](../entire-functions-at-arbitrary-rank/)
uses the same cofinality invariants: `ent:cor:cofinality` (nonpolynomial
entire series exist iff `cf(Γ) = ℵ0`) and `ent:thm:extension-criterion`
(cofinal/noncofinal change of workspace) have the same shape as Theorems 4.6
and 10.1 (Remarks 4.7, 10.2); neither is used to prove the other.

**Stale repository statements corrected.** The manuscript's comparison
(Section 14.2) describes revision `048b72c` and is kept as provenance. The
update that follows it records that the spectral report has since removed
Part I's divisibility hypothesis and proved `ihs:hh:thm:closedrange` at every
rank (revision `6e34651`; at the pin, for divisible `Γ ⊆ R`), that
`ihs:hh:prop:riesz` and `ihs:hh:thm:closedrange` were omitted from the
manuscript's comparison, and that the two manuscripts added to the spectral
report at `52c7ab6` contain no theorem about duals, completions or strong
maps. The manuscript's finding that no coefficient-rank completion theorem,
restriction sequence or completion-intersection formula appears in the
collection still holds for the current tree.

For the uncountable-cardinal analogue of the completion results — Hahn series
with fewer than `κ` terms — see
[first-kappa-coefficients](../first-kappa-coefficients/) (`fkc:thm:completion`,
`fkc:thm:dichotomy`): there the field is complete exactly when
`cf(Γ) ≠ cf(κ)`.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or `pdflatex` three times. The bibliography is internal (no BibTeX); no
figures, fonts or shell escape. The build gives no errors, no undefined or
multiply defined references, and no overfull or underfull boxes.

## Reproduce the finite checks

Python 3.10 or later, standard library only. **The script writes its report
next to itself by default** (that is, to `code/verification_report.json`, not
to `data/`), so pass an output path:

```sh
python code/verify_examples.py --output /tmp/verification_report.json
```

The recorded run, `data/verification_report.json`, reports 610 exact
assertions in nine groups (operator composition 60, scalar compatibility 60,
finite-family regrouping 60, leading squared norm 180, coefficient ranks below
cuts 69, two-scale ranks 69, projection algebra 69, descending-support prefix
42, cancellation 1), with seed 20260922 and `fractions.Fraction` arithmetic. A
rerun at placement (Python 3.14) reproduced it exactly. The program does not
verify infinite well-ordering or the arbitrary-rank Hom theorem, the
completion and cofinality classifications, spherical completeness or
Hahn–Banach, the existence of Hamel or invisible functionals, the
infinite-dimensional orthogonal-complement and missing-infimum claims, or
novelty.
