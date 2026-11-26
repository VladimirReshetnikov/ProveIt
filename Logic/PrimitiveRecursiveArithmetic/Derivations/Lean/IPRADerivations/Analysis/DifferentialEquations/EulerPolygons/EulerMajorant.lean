import IPRADerivations.Foundations.OdeRefinement
import IPRADerivations.Foundations.TupleRecursion

/-!
# The scalar majorant of the refinement error, and its Gronwall bound

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, Theorem
`thm:ode-produced-refinement`: "Thus `e_j = ‖V_j − W_j‖` satisfies the produced recurrence
`e_0 = 0`, `e_{j+1} ≤ (1 + K δ) e_j + δ² H`. Iterating this inequality and using `lem:ode-growth` with `2n` in place
of `n` yields, for every `j ≤ 2n`, `e_j ≤ G ∑_{i<j} δ² H ≤ G (2n) δ² H`. This is exactly the point at which the
repository's `OdeRefinement.node_bound` can be instantiated after rational encoding and clearing denominators."

The errors `e_j` are rational numbers whose denominators grow with `j`, so they are compared with a sequence of
natural numbers that satisfies the recurrence with equality. With `κ = 2n` and `δ = 1/κ`, put

    u_0 = 0,    u_{j+1} = (κ + K) u_j + κ^{j+1} H        (`maj`, `maj_zero`, `maj_succ`),

so that `u_j / κ^{j+2}` satisfies `e_{j+1} = (1 + K/κ) e_j + H/κ²`. `EulerPolygons/EulerRefinement` derives
`κ^{j+2} e_j ≤ u_j` for the Euler polygons, and here `node_bound` bounds `u`:

* `maj_bound`: for `N ≤ κ = k₀ + 1`, `u_N ≤ 3^K κ κ^N H`, that is `u_N / κ^{N+2} ≤ 3^K H / κ = G H δ`.

`node_bound` needs a recurrence with a common denominator for all `j < N`. It is instantiated with
`e(j) = u_j κ^{N−j}` and the constant defect `κ^N H`: `κ e(j+1) = (κ + K) e(j) + κ (κ^N H)` for `j < N`
(`maj_rec`). The functions `e`, `dl` of `node_bound` have one parameter, which is the pair of the code of
`(κ, K, H)` and `N`.
-/

namespace LeanProofs.IPRA.Analysis.EulerMajorant

open_ipra
open LeanProofs.IPRA.Foundations.TupleRecursion

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The majorant -/

/-- The step `u' = (κ + K) u + κ^{j+1} H`, with the parameters `κ, K, H`. -/
def uStep : Step 1 3 where
  fn y s p _ := (p 0 + p 1) * s 0 + pw (p 0) (succ y) * p 2
  nat σ y s p _ := by simp only [PTm.subst_add, PTm.subst_mul, subst_ap2, ConciseIPRA.PTm.subst_succ]

/-- `u_j` for the parameters `ps = (κ, K, H)`. -/
def maj (j : PTm n) (ps : Fin 3 → PTm n) : PTm n := vrec uStep 0 j ![zero] ps

theorem maj_zero (ps : Fin 3 → PTm n) : Γ ⊢[PRAAx] maj zero ps ≐ zero :=
  vrec_zero uStep 0 ![zero] ps

theorem maj_succ (j : PTm n) (ps : Fin 3 → PTm n) :
    Γ ⊢[PRAAx] maj (succ j) ps ≐ (ps 0 + ps 1) * maj j ps + pw (ps 0) (succ j) * ps 2 :=
  vrec_succ uStep 0 j ![zero] ps

theorem congrMaj {j j' : PTm n} {ps ps' : Fin 3 → PTm n} (hj : Γ ⊢[PRAAx] j ≐ j')
    (hp : ∀ l, Γ ⊢[PRAAx] ps l ≐ ps' l) : Γ ⊢[PRAAx] maj j ps ≐ maj j' ps' :=
  congrVrec uStep 0 hj (fun _ => .eqRefl _) hp

@[simp] theorem subst_maj {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) (ps : Fin 3 → PTm n) :
    Syn.subst σ (maj j ps) = maj (Syn.subst σ j) fun l => Syn.subst σ (ps l) := by
  have e : (fun l => Syn.subst σ ((![zero] : Fin 1 → PTm n) l)) = ![zero] := by
    funext l; fin_cases l; exact ConciseIPRA.PTm.subst_zero σ
  simp only [maj, subst_vrec, e]

/-! ## The functions for `node_bound` -/

/-- `e(j, X) = u_j κ^{N−j}`, where `X = ⟨code of (κ, K, H), N⟩`. Variables: `0 = j`, `1 = X`. -/
def eT : PTm 2 :=
  maj (var 0) (fun l => prj l (fstT (var 1))) * pw (prj (0 : Fin 3) (fstT (var 1))) (monus (sndT (var 1)) (var 0))

/-- The constant defect `κ^N H`. Variables: `0 = j`, `1 = X`. -/
def dlT : PTm 2 := pw (prj (0 : Fin 3) (fstT (var 1))) (sndT (var 1)) * prj (2 : Fin 3) (fstT (var 1))

theorem inst2_eT (j X : PTm n) :
    inst2 eT j X = maj j (fun l => prj l (fstT X)) * pw (prj (0 : Fin 3) (fstT X)) (monus (sndT X) j) := by
  simp only [inst2, eT, PTm.subst_mul, subst_maj, subst_ap2, subst_prj, subst_fstT, subst_sndT,
    PTm.subst_monus, Syn.subst_var]
  rfl

theorem inst2_dlT (j X : PTm n) :
    inst2 dlT j X = pw (prj (0 : Fin 3) (fstT X)) (sndT X) * prj (2 : Fin 3) (fstT X) := by
  simp only [inst2, dlT, PTm.subst_mul, subst_ap2, subst_prj, subst_fstT, subst_sndT, Syn.subst_var]
  rfl

section Recurrence

variable {X k₀ A N j : PTm n}

/-- The recurrence of `node_bound`, with equality: `κ e(j+1) = (κ + K) e(j) + κ (κ^N H)` for `j < N`. -/
theorem maj_rec (h0 : Γ ⊢[PRAAx] prj (0 : Fin 3) (fstT X) ≐ succ k₀) (h1 : Γ ⊢[PRAAx] prj (1 : Fin 3) (fstT X) ≐ A)
    (hN : Γ ⊢[PRAAx] sndT X ≐ N) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] le (succ k₀ * inst2 eT (succ j) X)
      ((succ k₀ + A) * inst2 eT j X + succ k₀ * inst2 dlT j X) := by
  rw [inst2_eT, inst2_eT, inst2_dlT]
  have hjN : Γ ⊢[PRAAx] le (succ j) (sndT X) := lt_congr (.eqRefl _) hN.eqSymm hj
  have w1 := natEq (eq_add_of_le hjN)
  have w2 := natEq (eq_add_of_le (le_trans (le_succ_self j) hjN))
  have m1 : Γ ⊢[PRAAx] monus (sndT X) j ≐ succ (monus (sndT X) (succ j)) := by
    apply deriveNat; ipra_simps; linear_combination w1 - w2
  have p1 := natEq ((congrAp2 powF m1 (.eqRefl (prj (0 : Fin 3) (fstT X)))).eqTrans (pw_succ _ _))
  have p2 := natEq ((congrAp2 powF (eq_add_of_le hjN) (.eqRefl (prj (0 : Fin 3) (fstT X)))).eqTrans (pw_add _ _ _))
  have ms := natEq (maj_succ (Γ := Γ) j fun l => prj l (fstT X))
  have a0 := natEq h0
  have a1 := natEq h1
  ipra_le 0 using (rw [ms, p1, p2, a0, a1]; ring)

end Recurrence

/-- The defect is the constant `κ^N H`. -/
theorem dl_eq {X κ H N j : PTm n} (h0 : Γ ⊢[PRAAx] prj (0 : Fin 3) (fstT X) ≐ κ)
    (h2 : Γ ⊢[PRAAx] prj (2 : Fin 3) (fstT X) ≐ H) (hN : Γ ⊢[PRAAx] sndT X ≐ N) :
    Γ ⊢[PRAAx] inst2 dlT j X ≐ pw κ N * H := by
  rw [inst2_dlT]
  exact congrMul (congrAp2 powF hN h0) h2

/-! ## The Gronwall bound of the majorant -/

/-- `u_N ≤ 3^K κ κ^N H` for `N ≤ κ = k₀ + 1`: `Foundations/OdeRefinement.node_bound` for the majorant. -/
theorem maj_bound {κ k₀ A H N dd : PTm n} (hκ : Γ ⊢[PRAAx] κ ≐ succ k₀) (hN : Γ ⊢[PRAAx] N + dd ≐ succ k₀) :
    Γ ⊢[PRAAx] le (maj N ![κ, A, H]) (pw (num 3) A * (succ k₀ * (pw κ N * H))) := by
  -- the parameter of `e` and `dl`
  let X : PTm n := pairT (tup ![κ, A, H]) N
  have hp : ∀ l, Γ ⊢[PRAAx] prj l (fstT X) ≐ (![κ, A, H] : Fin 3 → PTm n) l := fun l =>
    (congrPrj l (fst_pair _ _)).eqTrans (prj_tup _ l)
  have hX : Γ ⊢[PRAAx] sndT X ≐ N := snd_pair _ _
  have h0 : Γ ⊢[PRAAx] inst2 eT zero X ≐ zero := by
    rw [inst2_eT]
    have z := natEq (maj_zero (Γ := Γ) fun l => prj l (fstT X))
    apply deriveNat; ipra_simps; rw [z]; ring
  -- the facts about `X` in the context of the induction of `node_bound`
  have s0 : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      prj (0 : Fin 3) (fstT (Syn.shift X)) ≐ succ (Syn.shift k₀) := by
    have a := ((hp 0).eqTrans hκ).shift
    simp only [Fm.shift, Fm.subst_eq, subst_prj, subst_fstT, ConciseIPRA.PTm.subst_succ] at a
    exact a.wk
  have s0' : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      prj (0 : Fin 3) (fstT (Syn.shift X)) ≐ Syn.shift κ := by
    have a := (hp 0).shift
    simp only [Fm.shift, Fm.subst_eq, subst_prj, subst_fstT] at a
    exact a.wk
  have s1 : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      prj (1 : Fin 3) (fstT (Syn.shift X)) ≐ Syn.shift A := by
    have a := (hp 1).shift
    simp only [Fm.shift, Fm.subst_eq, subst_prj, subst_fstT] at a
    exact a.wk
  have s2 : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      prj (2 : Fin 3) (fstT (Syn.shift X)) ≐ Syn.shift H := by
    have a := (hp 2).shift
    simp only [Fm.shift, Fm.subst_eq, subst_prj, subst_fstT] at a
    exact a.wk
  have sN : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] sndT (Syn.shift X) ≐ Syn.shift N := by
    have a := hX.shift
    simp only [Fm.shift, Fm.subst_eq, subst_sndT] at a
    exact a.wk
  have hrec : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift (succ k₀) * inst2 eT (succ (var 0)) (Syn.shift X))
        (Syn.shift (succ k₀ + A) * inst2 eT (var 0) (Syn.shift X) +
          Syn.shift (succ k₀) * inst2 dlT (var 0) (Syn.shift X))) := by
    refine .allI (.impI ?_)
    rw [show Syn.shift (succ k₀ + A) = succ (Syn.shift k₀) + Syn.shift A from by
      simp only [Syn.shift, PTm.subst_add, ConciseIPRA.PTm.subst_succ]]
    exact maj_rec s0 s1 sN Prf.hyp0
  have hdl : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 dlT (var 0) (Syn.shift X) ≐ Syn.shift (pw κ N * H))) := by
    refine .allI (.impI ?_)
    rw [show Syn.shift (pw κ N * H) = pw (Syn.shift κ) (Syn.shift N) * Syn.shift H from by
      simp only [Syn.shift, PTm.subst_mul, subst_ap2]]
    exact dl_eq s0' s2 sN
  have r := Foundations.OdeRefinement.node_bound eT dlT X N dd k₀ A (pw κ N * H) hN h0 hrec hdl
  rw [inst2_eT] at r
  -- `e(N) = u_N`
  have e1 := natEq (congrMaj (Γ := Γ) (.eqRefl N) hp)
  have e2 := natEq ((congrAp2 powF ((congrMonus hX (.eqRefl N)).eqTrans (monus_self N))
    (.eqRefl (prj (0 : Fin 3) (fstT X)))).eqTrans (pw_zero _))
  ipra_le sl r using (rw [e1, e2]; ring)

end LeanProofs.IPRA.Analysis.EulerMajorant
