import IPRADerivations.Core.Powers
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.DiophantineNumberTheory.FLTMultiples
import IPRADerivations.Foundations.ChainViability

/-!
# The finite arithmetic of the Khinchin divergence construction (`hurwitz_khinchin_ipra`, (K2))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §§"One call to the divergence
modulus supplies the block" and "Amplification by the finitely many residual gaps":

* "For any finite nonnegative rational list `(a_k)`, `Σ_k min(a_k, 1) ≥ min(Σ_k a_k, 1)`. This follows by
  induction from its two-term version" (`min_two`, `min_sum`: over a common denominator `D`,
  `Σ_k min(A_k, D) ≥ min(Σ_k A_k, D)`);
* "The rational binomial inequality `(b₀/(b₀−1))^{b₀} ≥ 1 + b₀/(b₀−1) > 2` implies `(1 − 1/b₀)^{b₀} < 1/2`"
  (`bern`: `(x+1)^{k+1} ≥ x^{k+1} + (k+1) x^k`; `half_bound`: `2 x^{x+1} < (x+1)^{x+1}`, i.e.
  `(1 − 1/b)^b < 1/2` for `b = x + 1 ≥ 1`);
* "After `T = b₀(m+1)` rounds …" the residual is below `2^{-(m+1)}` (`pow_amp`: `2X ≤ Y` gives
  `2^j X^j ≤ Y^j`; with `X = (b−1)^b`, `Y = b^b`, `j = m + 1` this is `(1 − 1/b)^{b(m+1)} ≤ 2^{-(m+1)}`).

The interval bookkeeping of the gap lists, the overlap estimate (K9) and the second moment (K10) are
not derived here.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinAmplify

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open LeanProofs.IPRA.Foundations.ChainViability (monus_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `Σ min(a_k, 1) ≥ min(Σ a_k, 1)` -/

/-- `min(a, D) = a ∸ (a ∸ D)`. -/
abbrev mn (a D : PTm n) : PTm n := monus a (monus a D)

theorem mn_left {a D : PTm n} (h : Γ ⊢[PRAAx] le a D) : Γ ⊢[PRAAx] mn a D ≐ a :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

theorem mn_right {a D : PTm n} (h : Γ ⊢[PRAAx] le D a) : Γ ⊢[PRAAx] mn a D ≐ D := by
  have e : Γ ⊢[PRAAx] a ≐ D + monus a D := eq_add_of_le h
  refine (congrMonus e ((congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _))).eqTrans (add_monus _ _)

theorem mn_le_self (a D : PTm n) : Γ ⊢[PRAAx] le (mn a D) a := monus_le _ _

theorem mn_le_bound (a D : PTm n) : Γ ⊢[PRAAx] le (mn a D) D := by
  refine .orE (lt_or_le a D) ?_ ?_
  · exact le_congr (mn_left (le_trans (le_succ_self a) Prf.hyp0)).eqSymm (.eqRefl _)
      (le_trans (le_succ_self a) Prf.hyp0)
  · exact le_congr (mn_right Prf.hyp0).eqSymm (.eqRefl _) (le_refl _)

/-- The two-term version: `min(x + y, D) ≤ min(x, D) + min(y, D)`. -/
theorem min_two (x y D : PTm n) : Γ ⊢[PRAAx] le (mn (x + y) D) (mn x D + mn y D) := by
  refine .orE (lt_or_le x D) ?_ ?_
  · let Δ : List (Fm PTm n) := lt x D :: Γ
    have ex : Δ ⊢[PRAAx] mn x D ≐ x := mn_left (le_trans (le_succ_self x) Prf.hyp0)
    refine .orE (lt_or_le y D) ?_ ?_
    · let Δ' : List (Fm PTm n) := lt y D :: Δ
      have ey : Δ' ⊢[PRAAx] mn y D ≐ y := mn_left (le_trans (le_succ_self y) Prf.hyp0)
      exact le_congr (.eqRefl _) (congrAdd ex.wk ey).eqSymm (mn_le_self _ _)
    · let Δ' : List (Fm PTm n) := le D y :: Δ
      have ey : Δ' ⊢[PRAAx] mn y D ≐ D := mn_right Prf.hyp0
      have b := mn_le_bound (Γ := Δ') (x + y) D
      exact le_trans b (le_congr (.eqRefl _) (congrAdd (.eqRefl _) ey).eqSymm (le_add_right' _ _))
  · let Δ : List (Fm PTm n) := le D x :: Γ
    have ex : Δ ⊢[PRAAx] mn x D ≐ D := mn_right Prf.hyp0
    have b := mn_le_bound (Γ := Δ) (x + y) D
    exact le_trans b (le_congr (.eqRefl _) (congrAdd ex (.eqRefl _)).eqSymm (le_add_right _ _))
where
  le_add_right' {Δ : List (Fm PTm n)} (a b : PTm n) : Δ ⊢[PRAAx] le b (a + b) := by ipra_le 𝔞 a

/-- `min(A_k, D)` over `0 = k`, `1 = ⟨D, x⟩`. -/
def MB (A : PTm 2) : PTm 2 :=
  mn (Syn.subst ![var 0, sndT (var 1)] A) (fstT (var 1))

theorem inst2_MB (A : PTm 2) (k z : PTm n) : inst2 (MB A) k z = mn (inst2 A k (sndT z)) (fstT z) := by
  have h : Syn.subst ![k, z] (Syn.subst ![var 0, sndT (var 1)] A) = inst2 A k (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, MB, PTm.subst_monus, h]
  simp

/-- The invariant: `min(Σ_{k<N} A_k, D) ≤ Σ_{k<N} min(A_k, D)`. -/
def minInv (A : PTm 2) (N D x : PTm n) : Fm PTm n :=
  le (mn (ap2 (sumF A) N x) D) (ap2 (sumF (MB A)) N (pairT D x))

@[simp] theorem subst_minInv {k : ℕ} (σ : Fin n → PTm k) (A : PTm 2) (N D x : PTm n) :
    (minInv A N D x).subst σ = minInv A (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ x) := by
  simp [minInv, subst_ap2]

theorem min_step (A : PTm 2) {N D x : PTm n} (ih : Γ ⊢[PRAAx] minInv A N D x) :
    Γ ⊢[PRAAx] minInv A (succ N) D x := by
  have ih' : Γ ⊢[PRAAx] le (mn (ap2 (sumF A) N x) D) (ap2 (sumF (MB A)) N (pairT D x)) := ih
  have eL : Γ ⊢[PRAAx] mn (ap2 (sumF A) (succ N) x) D ≐ mn (ap2 (sumF A) N x + inst2 A N x) D :=
    congrMonus (sum_succ' A N x) (congrMonus (sum_succ' A N x) (.eqRefl _))
  have eR : Γ ⊢[PRAAx] ap2 (sumF (MB A)) (succ N) (pairT D x) ≐
      ap2 (sumF (MB A)) N (pairT D x) + mn (inst2 A N x) D := by
    refine (sum_succ' (MB A) N (pairT D x)).eqTrans (congrAdd (.eqRefl _) ?_)
    rw [inst2_MB]
    exact congrMonus (congrInst2 A (.eqRefl _) (snd_pair _ _))
      (congrMonus (congrInst2 A (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))
  have t := min_two (Γ := Γ) (ap2 (sumF A) N x) (inst2 A N x) D
  show Γ ⊢[PRAAx] le (mn (ap2 (sumF A) (succ N) x) D) (ap2 (sumF (MB A)) (succ N) (pairT D x))
  exact le_congr eL.eqSymm eR.eqSymm (le_trans t (add_le_add₂ ih' (le_refl _)))

/-- `Σ_{k<N} min(A_k, D) ≥ min(Σ_{k<N} A_k, D)`. -/
theorem min_sum (A : PTm 2) (N D x : PTm n) :
    Γ ⊢[PRAAx] le (mn (ap2 (sumF A) N x) D) (ap2 (sumF (MB A)) N (pairT D x)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (minInv A (var 0) (Syn.shift D) (Syn.shift x)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_minInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      show Γ ⊢[PRAAx] le (mn (ap2 (sumF A) zero x) D) (ap2 (sumF (MB A)) zero (pairT D x))
      exact le_congr ((congrMonus (sum_zero A x).eqSymm (congrMonus (sum_zero A x).eqSymm (.eqRefl _))).eqTrans
        (.eqRefl _)) (sum_zero _ _).eqSymm (le_congr ((zero_monus _).eqSymm) (.eqRefl _) (le_refl _))
    · rw [subst_minInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact min_step A Prf.hyp0
  have a := Prf.allE N hall
  rw [subst_minInv] at a
  simp only [Syn.subst_inst_shift] at a
  exact a

/-! ## `(1 − 1/b)^b < 1/2` -/

/-- `(x+1)^{k+1} ≥ x^{k+1} + (k+1) x^k`. -/
def bernInv (k x : PTm n) : Fm PTm n := le (pw x (succ k) + succ k * pw x k) (pw (succ x) (succ k))

@[simp] theorem subst_bernInv {m : ℕ} (σ : Fin n → PTm m) (k x : PTm n) :
    (bernInv k x).subst σ = bernInv (Syn.subst σ k) (Syn.subst σ x) := by
  simp [bernInv, subst_ap2]

theorem bern_base (x : PTm n) : Γ ⊢[PRAAx] bernInv zero x := by
  have e1 := natEq (pw_succ (Γ := Γ) x zero)
  have e0 := natEq (pw_zero (Γ := Γ) x)
  have f1 := natEq (pw_succ (Γ := Γ) (succ x) zero)
  have f0 := natEq (pw_zero (Γ := Γ) (succ x))
  show Γ ⊢[PRAAx] le (pw x (succ zero) + succ zero * pw x zero) (pw (succ x) (succ zero))
  ipra_le 0 using linear_combination f1 + (𝔞 x + 1) * f0 - e1 - (𝔞 x + 1) * e0

theorem bern_step {k x : PTm n} (ih : Γ ⊢[PRAAx] bernInv k x) : Γ ⊢[PRAAx] bernInv (succ k) x := by
  have ih' : Γ ⊢[PRAAx] le (pw x (succ k) + succ k * pw x k) (pw (succ x) (succ k)) := ih
  have eG := natEq (pw_succ (Γ := Γ) x (succ k))
  have eQ := natEq (pw_succ (Γ := Γ) (succ x) (succ k))
  have eE := natEq (pw_succ (Γ := Γ) x k)
  show Γ ⊢[PRAAx] le (pw x (succ (succ k)) + succ (succ k) * pw x (succ k)) (pw (succ x) (succ (succ k)))
  ipra_le (𝔞 x + 1) * sl ih' + (𝔞 k + 1) * 𝔞 (pw x k) with eQ - eG - (𝔞 k + 1) * eE

theorem bern (k x : PTm n) : Γ ⊢[PRAAx] le (pw x (succ k) + succ k * pw x k) (pw (succ x) (succ k)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (bernInv (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_bernInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact bern_base _
    · rw [subst_bernInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact bern_step Prf.hyp0
  have a := Prf.allE k hall
  rw [subst_bernInv] at a
  simp only [Syn.subst_inst_shift] at a
  exact a

/-- `x^x ≥ 1`. -/
theorem pw_self_pos (x : PTm n) : Γ ⊢[PRAAx] le one (pw x x) := by
  refine .orE (zero_or_succ x) ?_ ?_
  · let Δ : List (Fm PTm n) := (x ≐ zero) :: Γ
    have e : Δ ⊢[PRAAx] pw x x ≐ one :=
      (congrAp2 powF (Prf.hyp0 : Δ ⊢[PRAAx] x ≐ zero) (Prf.hyp0 : Δ ⊢[PRAAx] x ≐ zero)).eqTrans (pw_zero _)
    exact le_congr (.eqRefl _) e.eqSymm (le_refl _)
  · let Δ : List (Fm PTm n) := (x ≐ succ (pred x)) :: Γ
    have hx : Δ ⊢[PRAAx] x ≐ succ (pred x) := Prf.hyp0
    have p := pw_pos (Γ := Δ) (pred x) x
    have e : Δ ⊢[PRAAx] pw x x ≐ succ (pred (pw (succ (pred x)) x)) :=
      (congrAp2 powF (.eqRefl _) hx).eqTrans p
    have e' := natEq e
    ipra_le 𝔞 (pred (pw (succ (pred x)) x)) with e'

/-- `2 x^{x+1} < (x+1)^{x+1}`, i.e. `(1 − 1/b)^b < 1/2` for `b = x + 1`. -/
theorem half_bound (x : PTm n) : Γ ⊢[PRAAx] lt (two * pw x (succ x)) (pw (succ x) (succ x)) := by
  have B := bern (Γ := Γ) x x
  have h1 := pw_self_pos (Γ := Γ) x
  have eE := natEq (pw_succ (Γ := Γ) x x)
  ipra_le sl B + sl h1 with eE

/-- `2X ≤ Y` gives `2^j X^j ≤ Y^j`. -/
def ampInv (j X Y : PTm n) : Fm PTm n := le (pw two j * pw X j) (pw Y j)

@[simp] theorem subst_ampInv {m : ℕ} (σ : Fin n → PTm m) (j X Y : PTm n) :
    (ampInv j X Y).subst σ = ampInv (Syn.subst σ j) (Syn.subst σ X) (Syn.subst σ Y) := by
  simp [ampInv, subst_ap2]

theorem pow_amp {X Y : PTm n} (h : Γ ⊢[PRAAx] le (two * X) Y) (j : PTm n) :
    Γ ⊢[PRAAx] le (pw two j * pw X j) (pw Y j) := by
  have hall : Γ ⊢[PRAAx] Fm.all (ampInv (var 0) (Syn.shift X) (Syn.shift Y)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_ampInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have a := natEq (pw_zero (Γ := Γ) (two : PTm n))
      have b := natEq (pw_zero (Γ := Γ) X)
      have c := natEq (pw_zero (Γ := Γ) Y)
      show Γ ⊢[PRAAx] le (pw two zero * pw X zero) (pw Y zero)
      ipra_le 0 using linear_combination c - 𝔞 (pw X zero) * a - b
    · rw [subst_ampInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := ampInv (var 0) (Syn.shift X) (Syn.shift Y) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (pw two (var 0) * pw (Syn.shift X) (var 0)) (pw (Syn.shift Y) (var 0)) := Prf.hyp0
      have h' : Δ ⊢[PRAAx] le (two * Syn.shift X) (Syn.shift Y) := by
        have s := h.shift
        simp only [Fm.shift, subst_le, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at s
        exact s.wk
      have e2 := natEq (pw_succ (Γ := Δ) (two : PTm (n + 1)) (var 0))
      have eX := natEq (pw_succ (Γ := Δ) (Syn.shift X) (var 0))
      have eY := natEq (pw_succ (Γ := Δ) (Syn.shift Y) (var 0))
      show Δ ⊢[PRAAx] le (pw two (succ (var 0)) * pw (Syn.shift X) (succ (var 0))) (pw (Syn.shift Y) (succ (var 0)))
      ipra_le 𝔞 (pw (Syn.shift Y) (var 0)) * sl h' + 2 * 𝔞 (Syn.shift X) * sl ih
        with eY - 𝔞 (pw two (succ (var 0))) * eX - 𝔞 (pw (Syn.shift X) (var 0)) * 𝔞 (Syn.shift X) * e2
  have a := Prf.allE j hall
  rw [subst_ampInv] at a
  simp only [Syn.subst_inst_shift] at a
  exact a

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinAmplify
