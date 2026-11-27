import IPRADerivations.AnalyticNumberTheory.DivisorExchange
import IPRADerivations.Foundations.SignedSums
import IPRADerivations.Core.CertificateTactics

/-!
# Expanding a product of two divisor sums over a weighted range

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, proof of `thm:finite-sieve`:
"Sum `eq:sieve-majorant` over the progression. Expanding its square …" — the sum over `n` of
`(Σ_{d ∣ n} λ_d)(Σ_{e ∣ n} λ_e)` becomes a sum over the pairs `(d, e)` of `λ_d λ_e` times the number of `n`
divisible by both.

For natural bodies `c(n, p)`, `u(d, p)`, `v(e, p)` with a common parameter `p`:

  `Σ_{n<X} c(n) (Σ_{e<Z} [e ∣ n] v(e)) (Σ_{d<Z} [d ∣ n] u(d))
     = Σ_{d<Z} u(d) Σ_{e<Z} v(e) Σ_{n<X} c(n) [d ∣ n] [e ∣ n]`                            (`square_exchange`),

by two applications of `DivisorExchange.div_exchange`: first with the weight `c(n) Σ_e [e ∣ n] v(e)`, then, for each
`d`, with the weight `c(n) [d ∣ n]`.

* `sqL_pt`: the summand on the left in plain form;
* `SqR_at`, `inR_pt`, `K_pt`: the summands on the right: the outer body `SqR`, the inner body
  `RW (mdB c) (sndB v)`, and the innermost summand `c(n) [d ∣ n] [e ∣ n]`;
* `Tsnd`: a divisor sum does not depend on an extra parameter component.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveSquare

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorExchange (dvB dvB_at mdB mdB_at LW LW_at RW RW_at div_exchange)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `(C T) E = (C E) T'` for `T' = T`. -/
theorem sw {C T T' E : PTm n} (h : Γ ⊢[PRAAx] T' ≐ T) : Γ ⊢[PRAAx] (C * T) * E ≐ (C * E) * T' := by
  ipra_lc -𝔞 C * 𝔞 E * natEq h

/-! ## A parameter component that is not used -/

/-- `v(e, snd z)` at `z = ⟨w, p⟩`. -/
theorem snd_at (v : PTm 2) (e w p : PTm n) : Γ ⊢[PRAAx] inst2 (sndB v) e (pairT w p) ≐ inst2 v e p := by
  rw [inst2_sndB]
  exact congrInst2 v (.eqRefl _) (snd_pair w p)

theorem dv_snd (v : PTm 2) (e m w p : PTm n) :
    Γ ⊢[PRAAx] inst2 (dvB (sndB v)) e (pairT m (pairT w p)) ≐ inst2 (dvB v) e (pairT m p) :=
  (dvB_at (sndB v) e m (pairT w p)).eqTrans ((congrMul (.eqRefl _) (snd_at v e w p)).eqTrans (dvB_at v e m p).eqSymm)

/-- `Σ_{e<Z} [e ∣ m] v(e, p)` with an unused parameter component `w`. -/
theorem Tsnd (v : PTm 2) (Z m w p : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (dvB (sndB v))) Z (pairT m (pairT w p)) ≐ ap2 (sumF (dvB v)) Z (pairT m p) := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact dv_snd v _ _ _ _

section Square

variable (c u v : PTm 2)

/-! ## The summand on the left -/

/-- `c(m) (Σ_{e<Z} [e ∣ m] v(e)) (Σ_{d<Z} [d ∣ m] u(d))`. -/
theorem sqL_pt (m Z p : PTm n) :
    Γ ⊢[PRAAx] inst2 (LW (LW c v) (sndB u)) m (pairT Z (pairT Z p)) ≐
      (inst2 c m p * ap2 (sumF (dvB v)) Z (pairT m p)) * ap2 (sumF (dvB u)) Z (pairT m p) :=
  (LW_at (LW c v) (sndB u) m Z (pairT Z p)).eqTrans (congrMul (LW_at c v m Z p) (Tsnd u Z m Z p))

/-! ## The inner exchange -/

/-- The weight `c(m) (Σ_e [e ∣ m] v(e)) [d ∣ m]` as the weight `c(m) [d ∣ m]` times the divisor sum. -/
theorem in_pt (m d Z p : PTm n) :
    Γ ⊢[PRAAx] inst2 (mdB (LW c v)) m (pairT d (pairT Z p)) ≐
      inst2 (LW (mdB c) (sndB v)) m (pairT Z (pairT d p)) := by
  have l : Γ ⊢[PRAAx] inst2 (mdB (LW c v)) m (pairT d (pairT Z p)) ≐
      (inst2 c m p * ap2 (sumF (dvB v)) Z (pairT m p)) * eqb (rem m d) zero :=
    (mdB_at (LW c v) m d (pairT Z p)).eqTrans (congrMul (LW_at c v m Z p) (.eqRefl _))
  have r : Γ ⊢[PRAAx] inst2 (LW (mdB c) (sndB v)) m (pairT Z (pairT d p)) ≐
      (inst2 c m p * eqb (rem m d) zero) * ap2 (sumF (dvB (sndB v))) Z (pairT m (pairT d p)) :=
    (LW_at (mdB c) (sndB v) m Z (pairT d p)).eqTrans (congrMul (mdB_at c m d p) (.eqRefl _))
  exact l.eqTrans ((sw (Tsnd v Z m d p)).eqTrans r.eqSymm)

/-- For each `d`: `Σ_{m<X} c(m) (Σ_e [e ∣ m] v(e)) [d ∣ m] = Σ_{e<Z} v(e) Σ_{m<X} c(m) [d ∣ m] [e ∣ m]`. -/
theorem inner (d X Z p : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (mdB (LW c v))) X (pairT d (pairT Z p)) ≐
      ap2 (sumF (RW (mdB c) (sndB v))) Z (pairT X (pairT d p)) := by
  have e1 : Γ ⊢[PRAAx] ap2 (sumF (mdB (LW c v))) X (pairT d (pairT Z p)) ≐
      ap2 (sumF (LW (mdB c) (sndB v))) X (pairT Z (pairT d p)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact in_pt c v _ _ _ _
  exact e1.eqTrans (div_exchange (mdB c) (sndB v) X Z (pairT d p))

/-! ## The right side -/

/-- `u(d, p) · Σ_{e<Z} v(e) Σ_{m<X} c(m) [d ∣ m] [e ∣ m]` over `0 = d`, `1 = ⟨X, ⟨Z, p⟩⟩`. -/
def SqR : PTm 2 :=
  Syn.subst ![var 0, sndT (sndT (var 1))] u *
    ap2 (sumF (RW (mdB c) (sndB v))) (fstT (sndT (var 1)))
      (pairT (fstT (var 1)) (pairT (var 0) (sndT (sndT (var 1)))))

theorem inst2_SqR (d z : PTm n) :
    inst2 (SqR c u v) d z = inst2 u d (sndT (sndT z)) *
      ap2 (sumF (RW (mdB c) (sndB v))) (fstT (sndT z)) (pairT (fstT z) (pairT d (sndT (sndT z)))) := by
  have hf : Syn.subst ![d, z] (Syn.subst ![var 0, sndT (sndT (var 1))] u) = inst2 u d (sndT (sndT z)) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, SqR, PTm.subst_mul, hf]
  simp

theorem SqR_at (d X Z p : PTm n) :
    Γ ⊢[PRAAx] inst2 (SqR c u v) d (pairT X (pairT Z p)) ≐
      inst2 u d p * ap2 (sumF (RW (mdB c) (sndB v))) Z (pairT X (pairT d p)) := by
  rw [inst2_SqR]
  have f1 := fst_pair (Γ := Γ) X (pairT Z p)
  have s1 := snd_pair (Γ := Γ) X (pairT Z p)
  have sZ : Γ ⊢[PRAAx] fstT (sndT (pairT X (pairT Z p))) ≐ Z := (congrFst s1).eqTrans (fst_pair Z p)
  have sp : Γ ⊢[PRAAx] sndT (sndT (pairT X (pairT Z p))) ≐ p := (congrSnd s1).eqTrans (snd_pair Z p)
  exact congrMul (congrInst2 u (.eqRefl _) sp) (congrAp2 _ sZ (congrPairT f1 (congrPairT (.eqRefl _) sp)))

/-- The column `d` of the first exchange is the outer body `SqR`. -/
theorem col_pt (d X Z p : PTm n) :
    Γ ⊢[PRAAx] inst2 (RW (LW c v) (sndB u)) d (pairT X (pairT Z p)) ≐ inst2 (SqR c u v) d (pairT X (pairT Z p)) :=
  (RW_at (LW c v) (sndB u) d X (pairT Z p)).eqTrans
    ((congrMul (snd_at u d Z p) (inner c v d X Z p)).eqTrans (SqR_at c u v d X Z p).eqSymm)

/-- The inner body at `e`: `v(e) · Σ_{m<X} c(m) [d ∣ m] [e ∣ m]`. -/
theorem inR_pt (e X d p : PTm n) :
    Γ ⊢[PRAAx] inst2 (RW (mdB c) (sndB v)) e (pairT X (pairT d p)) ≐
      inst2 v e p * ap2 (sumF (mdB (mdB c))) X (pairT e (pairT d p)) :=
  (RW_at (mdB c) (sndB v) e X (pairT d p)).eqTrans (congrMul (snd_at v e d p) (.eqRefl _))

/-- The innermost summand: `c(m) [d ∣ m] [e ∣ m]`. -/
theorem K_pt (m e d p : PTm n) :
    Γ ⊢[PRAAx] inst2 (mdB (mdB c)) m (pairT e (pairT d p)) ≐
      inst2 c m p * eqb (rem m d) zero * eqb (rem m e) zero :=
  (mdB_at (mdB c) m e (pairT d p)).eqTrans (congrMul (mdB_at c m d p) (.eqRefl _))

/-! ## The expansion -/

/-- `Σ_{m<X} c(m) (Σ_{e<Z} [e ∣ m] v(e)) (Σ_{d<Z} [d ∣ m] u(d)) = Σ_{d<Z} u(d) Σ_{e<Z} v(e) Σ_{m<X} c(m) [d ∣ m] [e ∣ m]`. -/
theorem square_exchange (X Z p : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (LW (LW c v) (sndB u))) X (pairT Z (pairT Z p)) ≐
      ap2 (sumF (SqR c u v)) Z (pairT X (pairT Z p)) := by
  have e1 := div_exchange (Γ := Γ) (LW c v) (sndB u) X Z (pairT Z p)
  have e2 : Γ ⊢[PRAAx] ap2 (sumF (RW (LW c v) (sndB u))) Z (pairT X (pairT Z p)) ≐
      ap2 (sumF (SqR c u v)) Z (pairT X (pairT Z p)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact col_pt c u v _ _ _ _
  exact e1.eqTrans e2

end Square

end LeanProofs.IPRA.AnalyticNumberTheory.SieveSquare
