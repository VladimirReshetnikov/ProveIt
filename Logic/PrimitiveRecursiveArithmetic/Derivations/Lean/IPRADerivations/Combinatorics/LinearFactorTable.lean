import IPRADerivations.Combinatorics.Stirling
import IPRADerivations.Combinatorics.BellTouchardPower

/-!
# The coefficients of `(X + 1)(X + 2) ⋯ (X + N)` and their action on a sequence

Support for `combinatorics/bell_numbers_ipra`, `thm:prime-period`, whose proof computes in
`𝔽_p[X]/(X^p − X − 1)` the product "`∏_{r=0}^{p−1} X^{p^r} = ∏_{r=0}^{p−1} (X + r)`". On a
sequence, `X` is the shift `E`, and a product of linear factors `(E + 1) ⋯ (E + N)` acts
through its coefficients.

* `cyc N K`: the coefficient of `X^K` in `(X + 1) ⋯ (X + N)` (an unsigned Stirling number of
  the first kind, `c(N + 1, K + 1)`), by primitive recursion on coded rows, with the row
  machinery of `Combinatorics/Stirling`;
* `cyc_zero`, `cyc_above`, `cyc_succ_zero`, `cyc_succ_succ`:
  `c(0, 0) = 1`, `c(N, K) = 0` for `K > N`, `c(N + 1, 0) = (N + 1) c(N, 0)`,
  `c(N + 1, K + 1) = (N + 1) c(N, K + 1) + c(N, K)` for `K ≤ N`;
* `Act f N m x = ∑_{K ≤ N} c(N, K) f(m + K, x)`: the value at `m` of
  `(E + 1) ⋯ (E + N)` applied to the sequence `f(·, x)`;
* `act_step`: `Act f (N + 1) m x = (N + 1) · Act f N m x + Act f N (m + 1) x`, the factor
  `E + (N + 1)`;
* `act_cong`: if `f₁(m₁ + K) ≡ f₂(m₂ + K + 1) + (N + 1) f₂(m₂ + K) (mod p)` for `K ≤ N`, then
  `Act f₁ N m₁ ≡ Act f₂ (N + 1) m₂ (mod p)`: a relation between two sequences that has the
  form of one factor is absorbed into the product;
* `sum_lin`: `∑ F = ρ ∑ G + ∑ H` from the same relation between the terms.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.LinearFactorTable

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Bell (nth nth_pair_zero monus_monus monus_le')
open LeanProofs.IPRA.Combinatorics.Stirling (build nth_build gle sg gle_of_le gle_above sg_zero
  sg_succ congrNth)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (cong_of_eq cong_mul cong_sum_lin)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The table -/

/-- The entry `(n + 1) c(n, k) + c(n, k − 1)` of row `n + 1`, over `0 = k`, `1 = ⟨n, R_n⟩`. -/
abbrev eC : PTm 2 :=
  succ (fstT (var 1)) *
      (gle (var 0) (fstT (var 1)) * nth (sndT (var 1)) (monus (fstT (var 1)) (var 0))) +
    sg (var 0) * nth (sndT (var 1)) (monus (fstT (var 1)) (pred (var 0)))

theorem inst2_eC (k y : PTm n) : inst2 eC k y =
    succ (fstT y) * (gle k (fstT y) * nth (sndT y) (monus (fstT y) k)) +
      sg k * nth (sndT y) (monus (fstT y) (pred k)) := by
  simp [inst2]

/-- The row step; variables `0 = n`, `1 = R_n`. -/
abbrev rowStep : PTm 2 := build eC (succ (succ (var 0))) (pairT (var 0) (var 1))
abbrev RF : PR 1 := rec1 (pairT one zero) rowStep
/-- The coded row `R_N`. -/
abbrev row (N : PTm n) : PTm n := ap1 RF N

theorem row_zero : Γ ⊢[PRAAx] row (zero : PTm n) ≐ pairT one zero := by
  have h := rec1_zero (Γ := Γ) (pairT one zero) rowStep
  simpa using h

theorem row_succ (N : PTm n) :
    Γ ⊢[PRAAx] row (succ N) ≐ build eC (succ (succ N)) (pairT N (row N)) := by
  have h := rec1_succ (Γ := Γ) (pairT one zero) rowStep N
  simpa using h

/-- `c(N, K)`: the coefficient of `X^K` in `(X + 1) ⋯ (X + N)`. -/
abbrev cyc (N K : PTm n) : PTm n := gle K N * nth (row N) (monus N K)

theorem congrCyc {N N' K K' : PTm n} (hN : Γ ⊢[PRAAx] N ≐ N') (hK : Γ ⊢[PRAAx] K ≐ K') :
    Γ ⊢[PRAAx] cyc N K ≐ cyc N' K' :=
  congrMul (congrMonus (.eqRefl _) (congrMonus hK hN))
    (congrNth (congrAp1 RF hN) (congrMonus hN hK))

/-- `c(0, 0) = 1`. -/
theorem cyc_zero : Γ ⊢[PRAAx] cyc (zero : PTm n) zero ≐ one := by
  have g := gle_of_le (Γ := Γ) (le_refl (zero : PTm n))
  have r : Γ ⊢[PRAAx] nth (row (zero : PTm n)) (monus zero zero) ≐ one :=
    (congrNth row_zero (monus_zero _)).eqTrans (nth_pair_zero _ _)
  exact (congrMul g r).eqTrans (one_mul _)

/-- `c(N, K) = 0` for `K > N`. -/
theorem cyc_above {N K : PTm n} (h : Γ ⊢[PRAAx] le (succ N) K) : Γ ⊢[PRAAx] cyc N K ≐ zero :=
  (congrMul (gle_above h) (.eqRefl _)).eqTrans (zero_mul _)

/-- `c(N + 1, 0) = (N + 1) c(N, 0)`. -/
theorem cyc_succ_zero (N : PTm n) : Γ ⊢[PRAAx] cyc (succ N) zero ≐ succ N * cyc N zero := by
  have g := gle_of_le (Γ := Γ) (zero_le (succ N))
  have r : Γ ⊢[PRAAx] nth (row (succ N)) (monus (succ N) zero) ≐
      inst2 eC zero (pairT N (row N)) :=
    (congrNth (row_succ N) (monus_zero _)).eqTrans
      ((nth_build eC _ (le_refl _)).eqTrans (congrInst2 eC (monus_self _) (.eqRefl _)))
  rw [inst2_eC] at r
  have a₁ : Γ ⊢[PRAAx] gle zero (fstT (pairT N (row N))) ≐ gle zero N :=
    congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (fst_pair _ _))
  have b₁ : Γ ⊢[PRAAx] nth (sndT (pairT N (row N))) (monus (fstT (pairT N (row N))) zero) ≐
      nth (row N) (monus N zero) :=
    congrNth (snd_pair _ _) (congrMonus (fst_pair _ _) (.eqRefl _))
  have r' : Γ ⊢[PRAAx] nth (row (succ N)) (monus (succ N) zero) ≐ succ N * cyc N zero :=
    r.eqTrans ((congrAdd (congrMul (congrSucc (fst_pair _ _)) (congrMul a₁ b₁))
      (congrMul sg_zero (.eqRefl _))).eqTrans
        ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _)))
  exact (congrMul g r').eqTrans (one_mul _)

/-- `c(N + 1, K + 1) = (N + 1) c(N, K + 1) + c(N, K)` for `K ≤ N`. -/
theorem cyc_succ_succ {N K : PTm n} (h : Γ ⊢[PRAAx] le K N) :
    Γ ⊢[PRAAx] cyc (succ N) (succ K) ≐ succ N * cyc N (succ K) + cyc N K := by
  have hs : Γ ⊢[PRAAx] le (succ K) (succ N) := (succ_monus_succ _ _).eqTrans h
  have g₁ := gle_of_le hs
  have n₁ : Γ ⊢[PRAAx] nth (row (succ N)) (monus (succ N) (succ K)) ≐
      inst2 eC (succ K) (pairT N (row N)) :=
    (congrNth (row_succ N) (.eqRefl _)).eqTrans
      ((nth_build eC _ (monus_le' hs)).eqTrans (congrInst2 eC (monus_monus hs) (.eqRefl _)))
  rw [inst2_eC] at n₁
  have a₁ : Γ ⊢[PRAAx] gle (succ K) (fstT (pairT N (row N))) ≐ gle (succ K) N :=
    congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (fst_pair _ _))
  have b₁ : Γ ⊢[PRAAx]
      nth (sndT (pairT N (row N))) (monus (fstT (pairT N (row N))) (succ K)) ≐
        nth (row N) (monus N (succ K)) :=
    congrNth (snd_pair _ _) (congrMonus (fst_pair _ _) (.eqRefl _))
  have d₁ : Γ ⊢[PRAAx]
      nth (sndT (pairT N (row N))) (monus (fstT (pairT N (row N))) (pred (succ K))) ≐
        nth (row N) (monus N K) :=
    congrNth (snd_pair _ _) (congrMonus (fst_pair _ _) (pred_succ _))
  have n₂ := n₁.eqTrans (congrAdd (congrMul (congrSucc (fst_pair _ _)) (congrMul a₁ b₁))
    (congrMul (sg_succ K) d₁))
  have g₂ := natEq (gle_of_le h)
  refine (congrMul g₁ n₂).eqTrans ?_
  apply deriveNat; ipra_simps
  linear_combination -(𝔞 (nth (row N) (monus N K))) * g₂

/-! ## A linear relation between three sums -/

/-- The induction formula of `sum_lin`; variable `0` is the upper limit. -/
abbrev linF (F G H : PTm 2) (ρ x y z N : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift N) ⟶
    (ap2 (sumF F) (var 0) (Syn.shift x) ≐
      Syn.shift ρ * ap2 (sumF G) (var 0) (Syn.shift y) + ap2 (sumF H) (var 0) (Syn.shift z))

/-- `∑ F = ρ ∑ G + ∑ H` from the same relation between the terms below `N`. -/
theorem sum_lin (F G H : PTm 2) {ρ x y z N : PTm n}
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 F (var 0) (Syn.shift x) ≐
        Syn.shift ρ * inst2 G (var 0) (Syn.shift y) + inst2 H (var 0) (Syn.shift z)))) :
    Γ ⊢[PRAAx] ap2 (sumF F) N x ≐ ρ * ap2 (sumF G) N y + ap2 (sumF H) N z := by
  have hall : Γ ⊢[PRAAx] Fm.all (linF F G H ρ x y z N) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      have a := natEq (sum_zero (Γ := le zero N :: Γ) F x)
      have b := natEq (sum_zero (Γ := le zero N :: Γ) G y)
      have c := natEq (sum_zero (Γ := le zero N :: Γ) H z)
      apply deriveNat; ipra_simps
      linear_combination a - 𝔞 ρ * b - c
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have ih := natEq (Prf.impE (Prf.hyp1 (Γ := Γ.map Fm.shift)
        (φ := linF F G H ρ x y z N) (ψ := le (succ (var 0)) (Syn.shift N)))
        (le_trans (le_succ_self _) Prf.hyp0))
      have pt := natEq (Prf.impE hp.allOpen.wk.wk
        (Prf.hyp0 (Γ := linF F G H ρ x y z N :: Γ.map Fm.shift)
          (φ := le (succ (var 0)) (Syn.shift N))))
      have a := natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) ::
        linF F G H ρ x y z N :: Γ.map Fm.shift) F (var 0) (Syn.shift x))
      have b := natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) ::
        linF F G H ρ x y z N :: Γ.map Fm.shift) G (var 0) (Syn.shift y))
      have c := natEq (sum_succ' (Γ := le (succ (var 0)) (Syn.shift N) ::
        linF F G H ρ x y z N :: Γ.map Fm.shift) H (var 0) (Syn.shift z))
      apply deriveNat; ipra_simps
      linear_combination a - 𝔞 (Syn.shift ρ) * b - c + ih + pt
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-! ## The action on a sequence -/

open LeanProofs.IPRA.Combinatorics.BellTouchardPower (shift_pair shift_succ le_of_lt_succ)

section Action

variable (f : PTm 2)

/-- `c(fst y, K) · f(fst (snd y) + K, snd (snd y))`, over `0 = K`, `1 = ⟨N, ⟨m, x⟩⟩`. -/
def actB : PTm 2 :=
  cyc (fstT (var 1)) (var 0) *
    Syn.subst ![fstT (sndT (var 1)) + var 0, sndT (sndT (var 1))] f

/-- The parameter `⟨N, ⟨m, x⟩⟩`. -/
abbrev par (N m x : PTm n) : PTm n := pairT N (pairT m x)

theorem inst2_actB (K y : PTm n) : inst2 (actB f) K y =
    cyc (fstT y) K * inst2 f (fstT (sndT y) + K) (sndT (sndT y)) := by
  have h : Syn.subst ![K, y]
      (Syn.subst ![fstT (sndT (var 1)) + var 0, sndT (sndT (var 1))] f) =
      inst2 f (fstT (sndT y) + K) (sndT (sndT y)) := by
    simp only [inst2, Syn.subst_subst]
    congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, actB, PTm.subst_mul, h]
  simp [inst2]

theorem act_at (K N m x : PTm n) :
    Γ ⊢[PRAAx] inst2 (actB f) K (par N m x) ≐ cyc N K * inst2 f (m + K) x := by
  rw [inst2_actB]
  exact congrMul (congrCyc (fst_pair _ _) (.eqRefl _))
    (congrInst2 f (congrAdd ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _))
      ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))

/-- `Act f N m x = ∑_{K ≤ N} c(N, K) f(m + K, x)`. -/
abbrev Act (N m x : PTm n) : PTm n := ap2 (sumF (actB f)) (succ N) (par N m x)

theorem pair_congr {a a' c c' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hc : Γ ⊢[PRAAx] c ≐ c') :
    Γ ⊢[PRAAx] pairT a c ≐ pairT a' c' :=
  congrAdd (congrMul (congrAdd ha hc) (congrAdd ha hc)) ha

theorem congrAct {N m m' x x' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hx : Γ ⊢[PRAAx] x ≐ x') :
    Γ ⊢[PRAAx] Act f N m x ≐ Act f N m' x' :=
  congrAp2 _ (.eqRefl _) (pair_congr (.eqRefl _) (pair_congr hm hx))

/-- The empty product is the identity. -/
theorem act_zero (m x : PTm n) : Γ ⊢[PRAAx] Act f zero m x ≐ inst2 f m x := by
  have t : Γ ⊢[PRAAx] inst2 (actB f) zero (par zero m x) ≐ inst2 f m x :=
    (act_at f zero zero m x).eqTrans
      ((congrMul cyc_zero (congrInst2 f (add_zero m) (.eqRefl x))).eqTrans (one_mul _))
  have a := natEq (sum_succ' (Γ := Γ) (actB f) zero (par zero m x))
  have b := natEq (sum_zero (Γ := Γ) (actB f) (par zero m x))
  have d := natEq t
  apply deriveNat; ipra_simps
  linear_combination a + b + d

theorem act_pt_succ {N K m x : PTm n} (h : Γ ⊢[PRAAx] lt K (succ N)) :
    Γ ⊢[PRAAx] inst2 (shiftBody (actB f)) K (par (succ N) m x) ≐
      succ N * inst2 (shiftBody (actB f)) K (par N m x) + inst2 (actB f) K (par N (succ m) x) := by
  rw [inst2_shiftBody, inst2_shiftBody]
  have c := natEq (cyc_succ_succ (le_of_lt_succ h))
  have ef := natEq (congrInst2 f (Γ := Γ) (i := m + succ K) (i' := succ m + K) (x := x) (x' := x)
    (by apply deriveNat; ipra_simps; ring) (.eqRefl x))
  refine (act_at f (succ K) (succ N) m x).eqTrans (.eqTrans ?_
    (congrAdd (congrMul (.eqRefl _) (act_at f (succ K) N m x)) (act_at f K N (succ m) x)).eqSymm)
  apply deriveNat; ipra_simps
  linear_combination 𝔞 (inst2 f (m + succ K) x) * c + (𝔞 (gle K N) * 𝔞 (nth (row N) (monus N K))) * ef

/-- The factor `E + (N + 1)`:
`Act f (N + 1) m x = (N + 1) · Act f N m x + Act f N (m + 1) x`. -/
theorem act_step (N m x : PTm n) :
    Γ ⊢[PRAAx] Act f (succ N) m x ≐ succ N * Act f N m x + Act f N (succ m) x := by
  have s1 := natEq (sum_shift (Γ := Γ) (actB f) (succ N) (par (succ N) m x))
  have s2 := natEq (sum_shift (Γ := Γ) (actB f) (succ N) (par N m x))
  have s3 := natEq (sum_succ' (Γ := Γ) (actB f) (succ N) (par N m x))
  have top : Γ ⊢[PRAAx] inst2 (actB f) (succ N) (par N m x) ≐ zero :=
    (act_at f (succ N) N m x).eqTrans
      ((congrMul (cyc_above (le_refl _)) (.eqRefl _)).eqTrans (zero_mul _))
  have t0 : Γ ⊢[PRAAx] inst2 (actB f) zero (par (succ N) m x) ≐
      succ N * inst2 (actB f) zero (par N m x) := by
    refine (act_at f zero (succ N) m x).eqTrans (.eqTrans ?_
      (congrMul (.eqRefl _) (act_at f zero N m x)).eqSymm)
    have c := natEq (cyc_succ_zero (Γ := Γ) N)
    apply deriveNat; ipra_simps
    linear_combination 𝔞 (inst2 f (m + zero) x) * c
  have mid := natEq (sum_lin (Γ := Γ) (shiftBody (actB f)) (shiftBody (actB f)) (actB f)
    (ρ := succ N) (x := par (succ N) m x) (y := par N m x) (z := par N (succ m) x) (N := succ N)
    (.allI (.impI (by
      simp only [shift_pair, shift_succ]
      exact act_pt_succ f Prf.hyp0))))
  have tp := natEq top
  have t := natEq t0
  apply deriveNat; ipra_simps
  linear_combination s1 + t + mid - (𝔞 N + 1) * s2 + (𝔞 N + 1) * s3 + (𝔞 N + 1) * tp

end Action

/-! ## Absorbing a congruence into the product -/

theorem act_pt_cong (f₁ f₂ : PTm 2) {p ρ N K m₁ x₁ m₂ x₂ : PTm n}
    (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (h : Γ ⊢[PRAAx] rem (inst2 f₁ (m₁ + K) x₁) p ≐
      rem (inst2 f₂ (succ (m₂ + K)) x₂ + ρ * inst2 f₂ (m₂ + K) x₂) p) :
    Γ ⊢[PRAAx] rem (inst2 (actB f₁) K (par N m₁ x₁)) p ≐
      rem (inst2 (actB f₂) K (par N (succ m₂) x₂) + ρ * inst2 (actB f₂) K (par N m₂ x₂)) p := by
  have r : Γ ⊢[PRAAx]
      cyc N K * (inst2 f₂ (succ (m₂ + K)) x₂ + ρ * inst2 f₂ (m₂ + K) x₂) ≐
        inst2 (actB f₂) K (par N (succ m₂) x₂) + ρ * inst2 (actB f₂) K (par N m₂ x₂) := by
    refine .eqTrans ?_ (congrAdd (act_at f₂ K N (succ m₂) x₂)
      (congrMul (.eqRefl ρ) (act_at f₂ K N m₂ x₂))).eqSymm
    have es := natEq (congrInst2 f₂ (Γ := Γ) (i := succ (m₂ + K)) (i' := succ m₂ + K)
      (x := x₂) (x' := x₂) (by apply deriveNat; ipra_simps; ring) (.eqRefl x₂))
    apply deriveNat; ipra_simps
    linear_combination (𝔞 (gle K N) * 𝔞 (nth (row N) (monus N K))) * es
  exact (cong_of_eq (act_at f₁ K N m₁ x₁)).eqTrans ((cong_mul _ hq h).eqTrans (cong_of_eq r))

/-- If `f₁(m₁ + K) ≡ f₂(m₂ + K + 1) + (N + 1) f₂(m₂ + K) (mod p)` for all `K ≤ N`, then
`Act f₁ N m₁ ≡ Act f₂ (N + 1) m₂ (mod p)`. -/
theorem act_cong (f₁ f₂ : PTm 2) {p N m₁ x₁ m₂ x₂ : PTm n}
    (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (H : Γ ⊢[PRAAx] Fm.all (lt (var 0) (succ (Syn.shift N)) ⟶
      (rem (inst2 f₁ (Syn.shift m₁ + var 0) (Syn.shift x₁)) (Syn.shift p) ≐
        rem (inst2 f₂ (succ (Syn.shift m₂ + var 0)) (Syn.shift x₂) +
          succ (Syn.shift N) * inst2 f₂ (Syn.shift m₂ + var 0) (Syn.shift x₂)) (Syn.shift p)))) :
    Γ ⊢[PRAAx] rem (Act f₁ N m₁ x₁) p ≐ rem (Act f₂ (succ N) m₂ x₂) p := by
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hq.shift
  refine (cong_sum_lin (actB f₁) (actB f₂) (actB f₂) (ρ := succ N) (x := par N m₁ x₁)
    (y := par N (succ m₂) x₂) (z := par N m₂ x₂) hq (.allI (.impI ?_))).eqTrans (cong_of_eq ?_)
  · simp only [shift_pair, shift_succ]
    exact act_pt_cong f₁ f₂ hq'.wk (.impE H.allOpen.wk Prf.hyp0)
  · have e := natEq (act_step (Γ := Γ) f₂ N m₂ x₂)
    apply deriveNat; ipra_simps
    linear_combination -e

end LeanProofs.IPRA.Combinatorics.LinearFactorTable
