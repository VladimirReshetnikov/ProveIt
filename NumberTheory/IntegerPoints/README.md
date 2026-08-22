# Integer points in circles

Formal Lean statements of the results of two papers on the **primitive
circle problem**: the asymptotic count `V(x)` of coprime integer pairs
`(a, b)` with `a² + b² ≤ x`, whose main term is `(6/π) x`.

- W. Zhai and X. Cao, *On the number of coprime integer pairs within a
  circle*, Acta Arith. 90 (1999), 1–16: under RH,
  `V(x) = (6/π) x + O(x^{11/30 + ε})`.
- J. Wu, *On the primitive circle problem*, Monatsh. Math. 135 (2002),
  69–81: under RH, `V(x) = (6/π) x + O(x^{221/608 + ε})`.

## Layout

- [`Papers/`](Papers/) — OCR transcriptions of the two papers as LaTeX.
  The Zhai–Cao transcription was compared page by page with the original
  Acta Arithmetica PDF; its statements match the print.  The Wu original
  could not be retrieved; the one correction made there (the signs in the
  Vaughan identity (4.1)) is annotated in the source.
- [`Lean/`](Lean/) — the Lake library `IntegerPoints`
  (`lake build IntegerPoints` from the repository root), namespace
  `LeanProofs.IntegerPoints`:
  - `IntegerPoints.Basic` — `P(x)`, `E(x)`, `V(x)`, `E_P(x) = Δ(x)`, `r(n)`,
    `e(t)`, dyadic ranges, the bilinear sum `ℛ(M, N)`.
  - `IntegerPoints.ExponentialSums` — Zhai–Cao Lemmas 1–8 (Kuz'min–Landau,
    Perron, Krätzel, Weyl–van der Corput, Bombieri–Iwaniec,
    Fouvry–Iwaniec, Min's B-process, Srinivasan) and Wu Lemma 2.1,
    Theorem 2, Lemmas 2.5–2.7 (triple and double monomial exponential
    sums), with a Graham–Kolesnik definition of exponent pairs.
  - `IntegerPoints.ZhaiCao` — (1.1)–(1.4), Lemmas 9–10, Propositions 1–2.
  - `IntegerPoints.Wu` — Theorem 1, Nowak's formula, the reduction to
    `ℛ(M, N)`, the regions `𝒜, ℬ, 𝒞, 𝒟`, Propositions 1–4, and the exact
    Vaughan identity behind Lemma 4.1.
  - `IntegerPoints.Consequences` — **proved**: Wu's Theorem 1 ⇒ Zhai–Cao's
    Theorem ⇒ Nowak's bound; Wu's unconditional (1.1) ⇒ Zhai–Cao's (1.2);
    Nowak's formula ⇒ Zhai–Cao Proposition 2; the regions cover the square,
    so Propositions 1–4 plus the reduction give Wu's Theorem 1
    (`wu_theorem1_of_props`).
  - `IntegerPoints.Vaughan` — **proved**: both forms of the Vaughan identity
    (`wu_vaughanIdentity_pointwise_holds`, `wu_vaughanIdentity_holds`) via
    Dirichlet convolution with the truncated Möbius function.
  - `IntegerPoints.Srinivasan` — **proved**: Zhai–Cao Lemma 8
    (`zhaiCao_lemma8_holds`) by an intermediate-value crossing argument.
  - `IntegerPoints.ExponentPairs` — **proved**: `(0, 1)` is an exponent pair.
  - `IntegerPoints.WeylVanDerCorput` — **proved**: Zhai–Cao Lemma 4, the
    Weyl–van der Corput inequality with real shift length `Q`
    (`zhaiCao_lemma4_holds`, implied constant `6c`), by a fully discrete
    window-sum argument.

## Status

Every result is a `Prop`-valued definition (e.g. `zhaiCao_theorem`,
`wu_theorem1`); the ones proved so far have a companion `…_holds` theorem
(or an implication between statements), listed above.  The library compiles
with no `sorry` and no axioms beyond Mathlib's.  The analytic core — the
exponential-sum estimates (Zhai–Cao Lemmas 1–3, 5–7, 9–10, Proposition 1; Wu
Theorem 2, Lemmas 2.1, 2.5–2.7, Propositions 1–4), Nowak's formula, and the
RH-conditional main theorems — remains unproved.

## Conventions worth knowing

- `≪` with an implied constant depending on parameters `p` is rendered
  `∀ p, ∃ C, ∀ …, ‖·‖ ≤ C * …`; `∼`/`≪`/`≫` hypotheses carry explicit
  constants quantified before `C`.
- `m ∼ M` is the dyadic block `M < m ≤ 2M` (Wu's convention) in both papers.
- Functions of a real variable are globally `C^k` on `ℝ` with hypotheses on
  the relevant interval.
- `min(D, 1/‖t‖)` and `min(1, L/(T‖M‖))` use helpers that return the
  intended `+∞` branch when `‖t‖ = 0`, since `1/0 = 0` in Lean.
- Zhai–Cao Lemma 7 is stated with `f'' > 0` (the `f'' < 0` case follows by
  conjugation) and with the `u`-sum over all integers in `[α, β]`.
- Wu's reduction "(1.3) suffices for Theorem 1" is stated for any
  `1/3 ≤ θ < 1/2`, the range in which his derivation is uniform.
