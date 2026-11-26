import IPRADerivations.AnalyticNumberTheory.FactorialLambda
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Reindex
import IPRADerivations.Core.Header

/-!
# The Leibniz rule for the weighted derivation of Dirichlet convolution

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:dirichlet-leibniz`.
For arithmetic functions given by bodies `f(d, y)`, `g(d, y)` (with a parameter `y`), the finite
Dirichlet convolution `(f * g)(m) = ∑_{d ∣ m} f(d) g(m/d)` (`conv`) and the weighted derivation
`(D_w f)(d) = L_w(d) f(d)` (`DwB`) satisfy

  `L_w(m) (f * g)(m) = ((D_w f) * g)(m) + (f * (D_w g))(m)`   for `m ≥ 1`   (`dirichlet_leibniz`).

Each divisor term splits by complete additivity `L_w(m) = L_w(d) + L_w(m/d)` (`leib_pt`, via
`lw_mul`). Signed (integer-valued) functions, coded as pairs of natural functions, follow by
applying the theorem to each of the four sign combinations.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (congrLw lw_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Leibniz

variable (w : PTm 2)

/-- `[d ∣ m] f(d) g(m/d)`, over `0 = d`, `1 = ⟨m, y⟩`. -/
def cvB (f g : PTm 2) : PTm 2 := (sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) *
  (Syn.subst ![var 0, sndT (var 1)] f * Syn.subst ![quo (fstT (var 1)) (var 0), sndT (var 1)] g)

/-- The Dirichlet convolution `(f * g)(m) = ∑_{d ∣ m} f(d) g(m/d)`. -/
abbrev conv (f g : PTm 2) (m y : PTm n) : PTm n := ap2 (sumF (cvB f g)) (succ m) (pairT m y)

/-- The weighted derivation `(D_w f)(d) = L_w(d) f(d)`, over `0 = d`, `1 = y`. -/
def DwB (f : PTm 2) : PTm 2 := ap2 (sumF (ellB w)) (succ (var 0)) (pairT (var 0) (var 1)) * f

theorem inst2_cvB (f g : PTm 2) (d z : PTm n) : inst2 (cvB f g) d z =
    (sg d * eqb (rem (fstT z) d) zero) * (inst2 f d (sndT z) * inst2 g (quo (fstT z) d) (sndT z)) := by
  simp only [inst2, cvB, PTm.subst_mul, subst_reindex2]
  simp

theorem inst2_DwB (f : PTm 2) (d y : PTm n) : inst2 (DwB w f) d y = Lw w d y * inst2 f d y := by
  simp [inst2, DwB]

theorem cv_at (f g : PTm 2) (d m y : PTm n) : Γ ⊢[PRAAx] inst2 (cvB f g) d (pairT m y) ≐
    (sg d * eqb (rem m d) zero) * (inst2 f d y * inst2 g (quo m d) y) := by
  rw [inst2_cvB]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT m y) ≐ m := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT m y) ≐ y := snd_pair _ _
  exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF f₁ (.eqRefl _)) (.eqRefl _)))
    (congrMul (congrInst2 f (.eqRefl _) s₁) (congrInst2 g (congrAp2 quoF f₁ (.eqRefl _)) s₁))

/-- A divisor term: `[d ∣ m] (L_w(d) f(d) g(m/d) + f(d) L_w(m/d) g(m/d)) = L_w(m) [d ∣ m] f(d) g(m/d)`. -/
theorem leib_pt (f g : PTm 2) {d m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] inst2 (cvB (DwB w f) g) d (pairT m y) + inst2 (cvB f (DwB w g)) d (pairT m y) ≐
      Lw w m y * inst2 (cvB f g) d (pairT m y) := by
  refine (congrAdd (cv_at _ _ _ _ _) (cv_at _ _ _ _ _)).eqTrans
    (.eqTrans ?_ (congrMul (.eqRefl _) (cv_at _ _ _ _ _)).eqSymm)
  rw [inst2_DwB, inst2_DwB]
  refine .orE (zero_or_succ d) ?_ ?_
  · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    have z : ∀ {X : PTm n}, ((d ≐ zero) :: Γ) ⊢[PRAAx] (sg d * eqb (rem m d) zero) * X ≐ zero :=
      fun {X} => zero_mul_l (zero_mul_l s0 _) _
    exact (congrAdd z z).eqTrans ((add_zero _).eqTrans
      ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqSymm)
  · refine .orE (eq_or_ne (rem m d) zero) ?_ ?_
    · let C : List (Fm PTm n) := (rem m d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
      have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
      have eN := eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd d m)
      have hk := pos_of_eq_mul hm.wk.wk eN
      ipra_lc -(𝔞 (sg d) * 𝔞 (eqb (rem m d) zero) * 𝔞 (inst2 f d y) * 𝔞 (inst2 g (quo m d) y)) * natEq ((congrLw w y eN).eqTrans (lw_mul w hd hk))
    · let C : List (Fm PTm n) := neg (rem m d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
      have zz : C ⊢[PRAAx] sg d * eqb (rem m d) zero ≐ zero :=
        (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by ipra_ring)
      have z : ∀ {X : PTm n}, C ⊢[PRAAx] (sg d * eqb (rem m d) zero) * X ≐ zero :=
        fun {X} => zero_mul_l zz _
      exact (congrAdd z z).eqTrans ((add_zero _).eqTrans
        ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqSymm)

/-- `thm:dirichlet-leibniz`: `D_w(f * g) = (D_w f) * g + f * (D_w g)`, at every `m ≥ 1`. -/
theorem dirichlet_leibniz (f g : PTm 2) {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] Lw w m y * conv f g m y ≐ conv (DwB w f) g m y + conv f (DwB w g) m y := by
  have hm' := shift_pos hm
  have h2 : Syn.shift (Lw w m y) = Lw w (Syn.shift m) (Syn.shift y) := by simp [Syn.shift]
  have sc : Γ ⊢[PRAAx] ap2 (sumF (addBody (cvB (DwB w f) g) (cvB f (DwB w g)))) (succ m) (pairT m y) ≐
      Lw w m y * conv f g m y := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, h2, shift_pairT]
    exact leib_pt w f g hm'.wk
  exact sc.eqSymm.eqTrans (sum_add _ _ _ _)

end Leibniz

end LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz
