import IPRADerivations.AnalyticNumberTheory.PsiTheta
import IPRADerivations.Core.BoundedSums

/-!
# Changing the mesh and the denominator of the harmonic logarithm (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `pnt_ipra.tex`, §"An entirely arithmetical
statement": "`F(n) = (n²)!`, `A(n) = Σ_{j=n+1}^{n²} F(n)/j`, `L(n) = A(n)/F(n) = H_{n²} − H_n`", and §"Rational
logarithm intervals" (refinement nests the intervals). The contraction works at a large mesh `K` over a large
factorial denominator; the arithmetic statement uses the mesh `n` over `(n²)!`. Both conversions are exact
rational bounds:

* `S_denom`: `M₀! S(m, L!) = L! S(m, M₀!)` for `m ≤ M₀ ≤ L` (every `1/j`, `j ≤ M₀`, is exact over both);
  in particular `A(n) = S(n², (n²)!) − S(n, (n²)!)` is `H_{n²} − H_n` over `(n²)!`;
* `mesh_pair` (`LogRefinement.log_refine` at `b = 1`): with `G = S(KMa) − S(KM)` the refined logarithm,
  `S(Ma) − S(M) ≤ G ≤ S(Ma) − S(M) + ⌊F/M⌋`;
* `mesh_change`: through the common refinement `NK`, the logarithms of `N` at the meshes `N` and `K` differ by
  at most `⌊F/K⌋`, resp. `⌊F/N⌋`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.MeshChange

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (S_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The denominator -/

/-- `M₀! ⌊L!/(m+1)⌋ = L! ⌊M₀!/(m+1)⌋` for `m + 1 ≤ M₀ ≤ L`. -/
theorem quo_scale {m M0 L : PTm n} (h1 : Γ ⊢[PRAAx] le (succ m) M0) (h2 : Γ ⊢[PRAAx] le M0 L) :
    Γ ⊢[PRAAx] fact M0 * quo (fact L) (succ m) ≐ fact L * quo (fact M0) (succ m) := by
  ipra_lc 𝔞 (quo (fact L) (succ m)) * natEq (Prf.andE₁ (div_mod_at (Γ := Γ) (x := fact M0) (y := succ m) (c := m) (.eqRefl _))) -
    𝔞 (quo (fact M0) (succ m)) * natEq (Prf.andE₁ (div_mod_at (Γ := Γ) (x := fact L) (y := succ m) (c := m) (.eqRefl _))) +
    𝔞 (quo (fact L) (succ m)) * natEq (dvd_fact h1) - 𝔞 (quo (fact M0) (succ m)) * natEq (dvd_fact (le_trans h1 h2))

/-- `M₀! S(m, L!) = L! S(m, M₀!)` for `m ≤ M₀ ≤ L`. -/
theorem S_denom {m M0 L : PTm n} (hm : Γ ⊢[PRAAx] le m M0) (h2 : Γ ⊢[PRAAx] le M0 L) :
    Γ ⊢[PRAAx] fact M0 * S m (fact L) ≐ fact L * S m (fact M0) := by
  have h2' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift M0) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using h2.shift
  let P : Fm PTm (n + 1) :=
    fact (Syn.shift M0) * S (var 0) (fact (Syn.shift L)) ≐ fact (Syn.shift L) * S (var 0) (fact (Syn.shift M0))
  have atIndex : Γ ⊢[PRAAx] P.subst (Syn.inst m) := by
    refine qfIndAtMost hm trivial ?_ ?_
    · simp only [P, Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      have a := natEq (sum_zero (Γ := Γ) hB (fact L))
      ipra_lc 𝔞 (fact M0) * a - 𝔞 (fact L) * natEq (sum_zero (Γ := Γ) hB (fact M0))
    · simp only [P, Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      let Δ := lt (var 0) (Syn.shift M0) :: P :: Γ.map Fm.shift
      have ih := natEq (Prf.hyp1 : Δ ⊢[PRAAx] P)
      have q := natEq (quo_scale (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift M0)) h2'.wk.wk)
      have a := natEq (S_succ (Γ := Δ) (var 0) (fact (Syn.shift L)))
      have b := natEq (S_succ (Γ := Δ) (var 0) (fact (Syn.shift M0)))
      ipra_lc ih + q + 𝔞 (fact (Syn.shift M0)) * a - 𝔞 (fact (Syn.shift L)) * b
  simpa [P] using atIndex

/-! ## The mesh -/

section Mesh

variable {M K a L : PTm n}

theorem mesh_pair (hM : Γ ⊢[PRAAx] le one M) (ha : Γ ⊢[PRAAx] le one a) (hK : Γ ⊢[PRAAx] le one K)
    (hL : Γ ⊢[PRAAx] le (K * (M * a)) L) :
    Γ ⊢[PRAAx] le (S (M * a) (fact L) + S (K * M) (fact L)) (S (K * (M * a)) (fact L) + S M (fact L)) ⋏
      le (S (K * (M * a)) (fact L) + S M (fact L)) (S (K * M) (fact L) + S (M * a) (fact L) + quo (fact L) M) := by
  have pM := pos_of_one_le hM
  have hMa : Γ ⊢[PRAAx] le M (M * a) := by
    have q := le_scale M ha
    ipra_le sl q
  have eT := eq_add_of_le hMa
  have e1 : Γ ⊢[PRAAx] succ (pred M) + monus (M * a) M ≐ M * a := (congrAdd pM.eqSymm (.eqRefl _)).eqTrans eT.eqSymm
  have hL' : Γ ⊢[PRAAx] le (K * (succ (pred M) + monus (M * a) M)) L :=
    le_congr (congrMul (.eqRefl _) e1).eqSymm (.eqRefl _) hL
  have lr := log_refine (pos_of_one_le hK) hL'
  have s1 := natEq (congrAp2 (sumF hB) e1 (.eqRefl (fact L)))
  have s2 := natEq (congrAp2 (sumF hB) (congrMul (.eqRefl K) pM.eqSymm) (.eqRefl (fact L)))
  have s3 := natEq (congrAp2 (sumF hB) (congrMul (.eqRefl K) e1) (.eqRefl (fact L)))
  have s4 := natEq (congrAp2 (sumF hB) pM.eqSymm (.eqRefl (fact L)))
  have c1 := Prf.andE₁ lr
  have c2 := Prf.andE₂ lr
  have hm : Γ ⊢[PRAAx] le (pred M + monus (M * a) M) (succ (pred M) + monus (M * a) M) := by ipra_le 1
  have sm := S_mono (fact L) hm
  have ss := natEq (S_succ (Γ := Γ) (pred M) (fact L))
  have sq := natEq (congrAp2 quoF (.eqRefl (fact L)) pM.eqSymm)
  refine .andI ?_ ?_
  · ipra_le sl c1 with s1 + s2 - s3 - s4
  · ipra_le sl c2 + sl sm with s3 + s4 - s2 - s1 - ss - sq

/-- The logarithms of `N` at the meshes `N` and `K`, over the common denominator `L!`, `L ≥ KN²`. -/
theorem mesh_change {N : PTm n} (hN : Γ ⊢[PRAAx] le one N) (hK : Γ ⊢[PRAAx] le one K)
    (hL : Γ ⊢[PRAAx] le (K * (N * N)) L) :
    Γ ⊢[PRAAx] le (S (N * N) (fact L) + S K (fact L)) (S (K * N) (fact L) + S N (fact L) + quo (fact L) K) ⋏
      le (S (K * N) (fact L) + S N (fact L)) (S (N * N) (fact L) + S K (fact L) + quo (fact L) N) := by
  have p1 := mesh_pair hN hN hK hL
  have hL2 : Γ ⊢[PRAAx] le (N * (K * N)) L :=
    le_congr (by ipra_ring) (.eqRefl _) hL
  have p2 := mesh_pair hK hN hN hL2
  have g := natEq (congrAp2 (sumF hB) (show Γ ⊢[PRAAx] K * (N * N) ≐ N * (K * N) by ipra_ring)
    (.eqRefl (fact L)))
  have k := natEq (congrAp2 (sumF hB) (show Γ ⊢[PRAAx] N * K ≐ K * N by ipra_ring)
    (.eqRefl (fact L)))
  refine .andI ?_ ?_
  · ipra_le sl (Prf.andE₁ p1) + sl (Prf.andE₂ p2) with g + k
  · ipra_le sl (Prf.andE₁ p2) + sl (Prf.andE₂ p1) with g + k

end Mesh

end LeanProofs.IPRA.AnalyticNumberTheory.MeshChange

export_ipra AnalyticNumberTheory.MeshChange (S_denom)
