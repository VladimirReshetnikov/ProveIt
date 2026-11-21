import IPRADerivations.AnalyticNumberTheory.BlockCross

/-!
# The finite block deficit (`pnt_ipra_constructive_2026-11-14`, Lemma `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, Lemma `con:deficit` (Finite
block deficit): "Suppose `ε ≤ a ≤ 4` and `|r(t)| ≤ a` throughout a block `[s, s + H]` … Then
`∫_s^{s+H} (a − |r(t)|) dt ≥ 1/(64q²)`. The proof needs only finitely many comparisons of rational numbers."

Here the block is `D₁ < d ≤ D₂` with midpoint `D_h`, both halves of harmonic length `≥ F H₀`, the stage bound
`D|ψ(m) − Fm| ≤ AFm` on the block, `1 ≤ A ≤ 4D` and `16 D A H₀ ≥ 3A² + 384 D²`. Then

  `3 A² F x ≤ 48 D Σ_{D₁<d≤D₂} g + 100 A D F (D₂ + ⌊x/D₁⌋)`  (`block_deficit`),

the finite form of the lemma (the deficit `Σ g` is at least `A² F x/(16 D)` up to the boundary terms). The case
analysis is by bounded searches (`BoundedReflection.ex_cases`): no high sample on the upper half (`case_A`), no low
sample on the lower half (`case_B`), or a crossing (`CrossingSearch.crossing`, `case_C_core`).

* `off_at`: the offset search body; `hi_fail`, `lo_fail`, `hi_pass`, `lo_pass`: a test at a divisor read as an
  inequality.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockDispatch

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockTests (four hiB loB hi_at lo_at test_zero test_one half_of_lt
  mid_of_neither)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem off_at (g : PTm 2) (i b P : PTm n) : Γ ⊢[PRAAx] inst2 (offB g) i (pairT b P) ≐ inst2 g (b + i) P := by
  rw [inst2_offB]; exact congrInst2 g (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

section Tests

variable {d X D₁ D₂ A Ds K F : PTm n}

/-- A failed high test: `2D(ψ ∸ Fq) ≤ AFq`. -/
theorem hi_fail (h : Γ ⊢[PRAAx] inst2 hiB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) ≐ zero) :
    Γ ⊢[PRAAx] le (two * (Ds * monus (Psi wt (quo X d) (pairT K F)) (F * quo X d))) (A * (F * quo X d)) :=
  half_of_lt (test_zero ((hi_at _ _ _ _ _ _ _ _).eqSymm.eqTrans h))

/-- A failed low test: `2D(Fq ∸ ψ) ≤ AFq`. -/
theorem lo_fail (h : Γ ⊢[PRAAx] inst2 loB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) ≐ zero) :
    Γ ⊢[PRAAx] le (two * (Ds * monus (F * quo X d) (Psi wt (quo X d) (pairT K F)))) (A * (F * quo X d)) :=
  half_of_lt (test_zero ((lo_at _ _ _ _ _ _ _ _).eqSymm.eqTrans h))

/-- Both tests failed: `2D|ψ − Fq| ≤ AFq`. -/
theorem mid_fail (h1 : Γ ⊢[PRAAx] inst2 hiB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) ≐ zero)
    (h2 : Γ ⊢[PRAAx] inst2 loB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) ≐ zero) :
    Γ ⊢[PRAAx] le (two * (Ds * absd (Psi wt (quo X d) (pairT K F)) (F * quo X d))) (A * (F * quo X d)) :=
  mid_of_neither (test_zero ((hi_at _ _ _ _ _ _ _ _).eqSymm.eqTrans h1))
    (test_zero ((lo_at _ _ _ _ _ _ _ _).eqSymm.eqTrans h2))

/-- A passed high test. -/
theorem hi_pass (h : Γ ⊢[PRAAx] neg (inst2 hiB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) ≐ zero)) :
    Γ ⊢[PRAAx] le (A * (F * quo X d)) (four * (Ds * monus (Psi wt (quo X d) (pairT K F)) (F * quo X d))) :=
  test_one (LeanProofs.IPRA.Foundations.CrossingSearch.ne_transport (hi_at _ _ _ _ _ _ _ _) h)

/-- A passed low test. -/
theorem lo_pass (h : Γ ⊢[PRAAx] neg (inst2 loB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) ≐ zero)) :
    Γ ⊢[PRAAx] le (A * (F * quo X d)) (four * (Ds * monus (F * quo X d) (Psi wt (quo X d) (pairT K F)))) :=
  test_one (LeanProofs.IPRA.Foundations.CrossingSearch.ne_transport (lo_at _ _ _ _ _ _ _ _) h)

end Tests

/-! ## The half-block hypotheses from a failed search -/

open LeanProofs.IPRA.Foundations.BoundedReflection (exB ex_none)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (OnBlock stg Pm Qm)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')

section Halves

variable {x D₁ Dh D₂ A Ds K L : PTm n}

/-- The shifted layout parameter. -/
abbrev Psh (x D₁ D₂ A Ds K L : PTm n) : PTm (n + 1) :=
  pairT (Syn.shift x) (BlockSums.Y (Syn.shift D₁) (Syn.shift D₂) (pairT (Syn.shift A) (Syn.shift Ds))
    (pairT (Syn.shift K) (fact (Syn.shift L))))

abbrev Pl (x D₁ D₂ A Ds K L : PTm n) : PTm n :=
  pairT x (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K (fact L)))

abbrev HCtx (x E₁ E₂ : PTm n) (Γ : List (Fm PTm n)) : List (Fm PTm (n + 1)) :=
  le (var 0) (Syn.shift E₂) :: lt (Syn.shift E₁) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift

/-- In the half `E₁ < d ≤ E₂`: `d = E₁ + 1 + (d − (E₁ + 1))`. -/
theorem idx_eq {x E₁ E₂ : PTm n} :
    HCtx x E₁ E₂ Γ ⊢[PRAAx] var 0 ≐ succ (Syn.shift E₁) + monus (var 0) (succ (Syn.shift E₁)) :=
  eq_add_of_le (show HCtx x E₁ E₂ Γ ⊢[PRAAx] lt (Syn.shift E₁) (var 0) from .hyp (by simp [HCtx]))

/-- In the half `E₁ < d ≤ E₂`, the search index `d − (E₁ + 1)` is below `E₂ − E₁`. -/
theorem idx_lt {x E₁ E₂ : PTm n} :
    HCtx x E₁ E₂ Γ ⊢[PRAAx] lt (monus (var 0) (succ (Syn.shift E₁))) (monus (Syn.shift E₂) (Syn.shift E₁)) := by
  have hlt : HCtx x E₁ E₂ Γ ⊢[PRAAx] lt (Syn.shift E₁) (var 0) := .hyp (by simp [HCtx])
  have hle : HCtx x E₁ E₂ Γ ⊢[PRAAx] le (var 0) (Syn.shift E₂) := .hyp (by simp [HCtx])
  have a := natEq (eq_add_of_le hlt)
  have b := natEq (eq_add_of_le hle)
  have c := natEq (eq_add_of_le (le_trans (le_of_lt hlt) hle))
  ipra_le 𝔞 (monus (Syn.shift E₂) (var 0)) with a + b - c

/-- Case A hypotheses: the stage bound and no high sample on `D_h < d ≤ D₂`. -/
theorem onblock_A (h1h : Γ ⊢[PRAAx] le D₁ Dh) (hst : Γ ⊢[PRAAx] OnBlock x D₁ D₂ (stg x A Ds K L))
    (hz : Γ ⊢[PRAAx] exB (offB hiB) (monus D₂ Dh) (pairT (succ Dh) (Pl x D₁ D₂ A Ds K L)) ≐ zero) :
    Γ ⊢[PRAAx] OnBlock x Dh D₂ (stg x A Ds K L ⋏
      le (two * (Syn.shift Ds * monus (Pm x K L) (Qm x L))) (Syn.shift A * Qm x L)) := by
  have h1h' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift D₁) (Syn.shift Dh) := by simpa [Fm.shift, Syn.shift] using h1h.shift
  have hz' : (Γ.map Fm.shift) ⊢[PRAAx]
      exB (offB hiB) (monus (Syn.shift D₂) (Syn.shift Dh)) (pairT (succ (Syn.shift Dh)) (Psh x D₁ D₂ A Ds K L)) ≐ zero := by
    simpa [Fm.shift, Syn.shift, exB, LeanProofs.IPRA.Foundations.BoundedReflection.allB, Psh, Pl, BlockSums.Y, fact]
      using hz.shift
  refine .allI (.impI (.impI (.impI ?_)))
  have hlt : HCtx x Dh D₂ Γ ⊢[PRAAx] lt (Syn.shift Dh) (var 0) := .hyp (by simp [HCtx])
  have st : HCtx x Dh D₂ Γ ⊢[PRAAx] stg x A Ds K L :=
    Prf.impE (Prf.impE (Prf.impE hst.allOpen.wk.wk.wk (.hyp (by simp [HCtx]))) (lt_of_le_of_lt h1h'.wk.wk.wk hlt))
      (.hyp (by simp [HCtx]))
  have hi := idx_lt (Γ := Γ) (x := x) (E₁ := Dh) (E₂ := D₂)
  have ev := idx_eq (Γ := Γ) (x := x) (E₁ := Dh) (E₂ := D₂)
  have ez := ex_none (offB hiB) hz'.wk.wk.wk hi
  have e : HCtx x Dh D₂ Γ ⊢[PRAAx] inst2 hiB (var 0) (Psh x D₁ D₂ A Ds K L) ≐ zero :=
    ((congrInst2 hiB ev (.eqRefl _)).eqTrans (off_at _ _ _ _).eqSymm).eqTrans ez
  exact .andI st (hi_fail e)

/-- Case B hypotheses: the stage bound and no low sample on `D₁ < d ≤ D_h`. -/
theorem onblock_B (hh2 : Γ ⊢[PRAAx] le Dh D₂) (hst : Γ ⊢[PRAAx] OnBlock x D₁ D₂ (stg x A Ds K L))
    (hz : Γ ⊢[PRAAx] exB (offB loB) (monus Dh D₁) (pairT (succ D₁) (Pl x D₁ D₂ A Ds K L)) ≐ zero) :
    Γ ⊢[PRAAx] OnBlock x D₁ Dh (stg x A Ds K L ⋏
      le (two * (Syn.shift Ds * monus (Qm x L) (Pm x K L))) (Syn.shift A * Qm x L)) := by
  have hh2' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift Dh) (Syn.shift D₂) := by simpa [Fm.shift, Syn.shift] using hh2.shift
  have hz' : (Γ.map Fm.shift) ⊢[PRAAx]
      exB (offB loB) (monus (Syn.shift Dh) (Syn.shift D₁)) (pairT (succ (Syn.shift D₁)) (Psh x D₁ D₂ A Ds K L)) ≐ zero := by
    simpa [Fm.shift, Syn.shift, exB, LeanProofs.IPRA.Foundations.BoundedReflection.allB, Psh, Pl, BlockSums.Y, fact]
      using hz.shift
  refine .allI (.impI (.impI (.impI ?_)))
  have hle : HCtx x D₁ Dh Γ ⊢[PRAAx] le (var 0) (Syn.shift Dh) := .hyp (by simp [HCtx])
  have st : HCtx x D₁ Dh Γ ⊢[PRAAx] stg x A Ds K L :=
    Prf.impE (Prf.impE (Prf.impE hst.allOpen.wk.wk.wk (.hyp (by simp [HCtx]))) (.hyp (by simp [HCtx])))
      (le_trans hle hh2'.wk.wk.wk)
  have hi := idx_lt (Γ := Γ) (x := x) (E₁ := D₁) (E₂ := Dh)
  have ev := idx_eq (Γ := Γ) (x := x) (E₁ := D₁) (E₂ := Dh)
  have ez := ex_none (offB loB) hz'.wk.wk.wk hi
  have e : HCtx x D₁ Dh Γ ⊢[PRAAx] inst2 loB (var 0) (Psh x D₁ D₂ A Ds K L) ≐ zero :=
    ((congrInst2 loB ev (.eqRefl _)).eqTrans (off_at _ _ _ _).eqSymm).eqTrans ez
  exact .andI st (lo_fail e)

end Halves

end LeanProofs.IPRA.AnalyticNumberTheory.BlockDispatch
