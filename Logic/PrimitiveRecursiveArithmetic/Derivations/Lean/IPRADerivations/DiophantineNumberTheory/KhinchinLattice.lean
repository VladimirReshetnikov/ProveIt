import IPRADerivations.Foundations.LatticeCount

/-!
# Lattice points under a line (`hurwitz_khinchin_ipra`, (K5))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex` (K5): "Let `A(X)` count all
integer pairs `(p, q)` with `1 ≤ q ≤ X` and `p/q ∈ J*` ... An open interval of length `t` contains
between `t − 1` and `t + 1` integers. Consequently `λX²/2 − X ≤ A(X) ≤ λX²/2 + (λ/2 + 1)X`."

Here `J* = (α/β, γ/β)` with `α ≤ γ ≤ β` (so `J* ⊆ (0, 1)`, `λ = (γ − α)/β`), and
`A(X) = Σ_{q=1}^{X} #{p < M : qα < pβ < qγ}` (`latticeA`; the candidates `p < M` with `M ≥ X`
contain all of them). `lattice_bounds` (closed sentence):

  `2β A(X) + α X(X+1) ≤ γ X(X+1) + 2βX` and `γ X(X+1) ≤ 2β A(X) + α X(X+1) + 2βX`,

that is `λX(X+1)/2 − X ≤ A(X) ≤ λX(X+1)/2 + X`, which gives both bounds of (K5). Proof: induction on
`X`, each new denominator `q = X + 1` contributing a count between `qλ − 1` and `qλ + 1`
(`LatticeCount.dilated_bounds`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinLattice

open_ipra exports
open LeanProofs.IPRA.Foundations.LatticeCount

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The parameters `z = ⟨M, ⟨α, ⟨γ, β⟩⟩⟩`. -/
abbrev zM (z : PTm n) : PTm n := fstT z
abbrev zα (z : PTm n) : PTm n := fstT (sndT z)
abbrev zγ (z : PTm n) : PTm n := fstT (sndT (sndT z))
abbrev zβ (z : PTm n) : PTm n := sndT (sndT (sndT z))

/-- The count for the denominator `i + 1` in `(i, z)`. -/
abbrev aK : PTm 2 := Foundations.LatticeCount.dS (zM (var 1)) (succ (var 0) * zα (var 1)) (succ (var 0) * zγ (var 1)) (zβ (var 1))

/-- `A(X) = Σ_{i<X} #{p < M : (i+1)α < pβ < (i+1)γ}`. -/
abbrev latticeA (X M α γ β : PTm n) : PTm n := ap2 (sumF aK) X (pairT M (pairT α (pairT γ β)))

/-- `⌈qγ/β⌉ ≤ q` for `γ ≤ β`. -/
theorem ceil_le_q {q γ β b0 : PTm n} (hβ : Γ ⊢[PRAAx] β ≐ succ b0) (hγ : Γ ⊢[PRAAx] le γ β) :
    Γ ⊢[PRAAx] le (quo (q * γ + b0) β) q := by
  apply Order.le_of_lt_succ (Division.quo_lt_of_lt_mul hβ ?_)
  change Γ ⊢[PRAAx] le (succ (q * γ + b0)) (β * succ q)
  exact le_congr ((congrAdd (.eqRefl _) hβ).eqTrans (add_succ _ _))
    (by ipra_ring) (add_le_add_right β (mul_le_mul_left q hγ))

/-- The invariant. -/
def latInv (X M α γ β : PTm n) : Fm PTm n :=
  le X M ⟶
    (le (two * β * latticeA X M α γ β + α * (X * succ X)) (γ * (X * succ X) + two * β * X) ⋏
      le (γ * (X * succ X)) (two * β * latticeA X M α γ β + α * (X * succ X) + two * β * X))

ipra_subst latInv [subst_ap2]

theorem latticeA_succ (X M α γ β : PTm n) :
    Γ ⊢[PRAAx] latticeA (succ X) M α γ β ≐ latticeA X M α γ β + Foundations.LatticeCount.dS M (succ X * α) (succ X * γ) β := by
  refine (sum_succ' aK X _).eqTrans (congrAdd (.eqRefl _) ?_)
  have e : inst2 aK X (pairT M (pairT α (pairT γ β))) =
      Foundations.LatticeCount.dS (zM (pairT M (pairT α (pairT γ β)))) (succ X * zα (pairT M (pairT α (pairT γ β))))
        (succ X * zγ (pairT M (pairT α (pairT γ β)))) (zβ (pairT M (pairT α (pairT γ β)))) := by
    simp [inst2]
  rw [e]
  have h1 : Γ ⊢[PRAAx] zM (pairT M (pairT α (pairT γ β))) ≐ M := fst_pair _ _
  have h2 : Γ ⊢[PRAAx] zα (pairT M (pairT α (pairT γ β))) ≐ α := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have h3 : Γ ⊢[PRAAx] zγ (pairT M (pairT α (pairT γ β))) ≐ γ :=
    (congrFst (congrSnd (snd_pair _ _))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
  have h4 : Γ ⊢[PRAAx] zβ (pairT M (pairT α (pairT γ β))) ≐ β :=
    (congrSnd (congrSnd (snd_pair _ _))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  exact congrAp2 (sumF dcB) h1 (congrPairT (congrMul (.eqRefl _) h2) (congrPairT (congrMul (.eqRefl _) h3) h4))

/-- One step of the induction. -/
theorem lat_step {X M α γ β b0 : PTm n} (hβ : Γ ⊢[PRAAx] β ≐ succ b0) (hαγ : Γ ⊢[PRAAx] le α γ)
    (hγ : Γ ⊢[PRAAx] le γ β) (ih : Γ ⊢[PRAAx] latInv X M α γ β) : Γ ⊢[PRAAx] latInv (succ X) M α γ β := by
  refine .impI ?_
  let Δ : List (Fm PTm n) := le (succ X) M :: Γ
  have hXM : Δ ⊢[PRAAx] le X M := le_trans (le_succ_self _) Prf.hyp0
  have hI := Prf.impE ih.wk hXM
  have hB : Δ ⊢[PRAAx] le (quo (succ X * γ + b0) β) M := le_trans (ceil_le_q hβ.wk hγ.wk) Prf.hyp0
  have huv : Δ ⊢[PRAAx] le (succ X * α) (succ X * γ) := by
    refine le_of_eq_add (d := succ X * monus γ α) ?_
    ipra_lc (𝔞 X + 1) * natEq (eq_add_of_le hαγ.wk)
  have db := dilated_bounds M hβ.wk hB huv
  refine .andI (le_of_eq_add (d := monus (γ * (X * succ X) + two * β * X) (two * β * latticeA X M α γ β + α * (X * succ X)) +
      two * monus (succ X * γ + β) (β * Foundations.LatticeCount.dS M (succ X * α) (succ X * γ) β + succ X * α)) ?_)
    (le_of_eq_add (d := monus (two * β * latticeA X M α γ β + α * (X * succ X) + two * β * X) (γ * (X * succ X)) +
      two * monus (β * Foundations.LatticeCount.dS M (succ X * α) (succ X * γ) β + succ X * α + β) (succ X * γ)) ?_)
  · ipra_lc natEq (eq_add_of_le (Prf.andE₁ hI)) + 2 * natEq (eq_add_of_le (Prf.andE₁ db)) -
      2 * 𝔞 β * natEq (latticeA_succ X M α γ β)
  · ipra_lc natEq (eq_add_of_le (Prf.andE₂ hI)) + 2 * natEq (eq_add_of_le (Prf.andE₂ db)) +
      2 * 𝔞 β * natEq (latticeA_succ X M α γ β)

/-- (K5) for given `α ≤ γ ≤ β = b0 + 1` and `X ≤ M`. -/
theorem lattice_core {X M α γ b0 : PTm n} (hαγ : Γ ⊢[PRAAx] le α γ) (hγ : Γ ⊢[PRAAx] le γ (succ b0))
    (hXM : Γ ⊢[PRAAx] le X M) :
    Γ ⊢[PRAAx] le (two * succ b0 * latticeA X M α γ (succ b0) + α * (X * succ X)) (γ * (X * succ X) + two * succ b0 * X) ⋏
      le (γ * (X * succ X)) (two * succ b0 * latticeA X M α γ (succ b0) + α * (X * succ X) + two * succ b0 * X) := by
  have hall : Γ ⊢[PRAAx] Fm.all (latInv (var 0) (Syn.shift M) (Syn.shift α) (Syn.shift γ) (Syn.shift (succ b0))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
    · rw [subst_latInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine .impI (.andI ?_ ?_)
      · refine le_of_eq_add (d := zero) ?_
        ipra_lc -2 * (𝔞 b0 + 1) * natEq (sum_zero aK (pairT M (pairT α (pairT γ (succ b0)))))
      · refine le_of_eq_add (d := zero) ?_
        ipra_lc 2 * (𝔞 b0 + 1) * natEq (sum_zero aK (pairT M (pairT α (pairT γ (succ b0)))))
    · rw [subst_latInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hβ : (latInv (var 0) (Syn.shift M) (Syn.shift α) (Syn.shift γ) (Syn.shift (succ b0)) :: Γ.map Fm.shift) ⊢[PRAAx]
          Syn.shift (succ b0) ≐ succ (Syn.shift b0) := by
        rw [show Syn.shift (succ b0) = succ (Syn.shift b0) by simp [Syn.shift]]; exact .eqRefl _
      have hαγ' := hαγ.shift
      have hγ' := hγ.shift
      simp only [Fm.shift, subst_le] at hαγ' hγ'
      exact lat_step hβ hαγ'.wk hγ'.wk Prf.hyp0
  have a := Prf.allE X hall
  rw [subst_latInv] at a
  simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at a
  exact Prf.impE a hXM

/-- Variables `0 = X`, `1 = α`, `2 = γ`, `3 = b0` (`β = b0 + 1`), with `M = X`. -/
def latticeFormula : Fm PTm 4 :=
  le (var 1) (var 2) ⟶ (le (var 2) (succ (var 3)) ⟶
    (le (two * succ (var 3) * latticeA (var 0) (var 0) (var 1) (var 2) (succ (var 3)) + var 1 * (var 0 * succ (var 0)))
        (var 2 * (var 0 * succ (var 0)) + two * succ (var 3) * var 0) ⋏
      le (var 2 * (var 0 * succ (var 0)))
        (two * succ (var 3) * latticeA (var 0) (var 0) (var 1) (var 2) (succ (var 3)) + var 1 * (var 0 * succ (var 0)) +
          two * succ (var 3) * var 0)))

/-- (K5), as a closed sentence of iPRA. -/
theorem lattice_bounds : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 latticeFormula :=
  closeUniv 4 (.impI (.impI (lattice_core Prf.hyp1 Prf.hyp0 (le_refl _))))

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinLattice
