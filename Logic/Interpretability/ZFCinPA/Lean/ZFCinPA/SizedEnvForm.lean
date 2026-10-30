import ZFCinPA.SizedLNumOK

/-!
# The environment transform has a linear level bound

`EnvTransform.envForm d p` is the `L`-relativized environment transform of a
formula code `p` at binder depth `d`, the predicate placeholder of the
`hSchema` driver (`LDriver.driver`). In every model of `𝗜𝚺₁`:

`envForm d p ≤ lvB (Eb + 100 d + 200 p)` for every semiformula `p` (`envForm_le`).

A connective adds four levels and a quantifier twelve, and both are paid by
the growth of the code (`p < p ^⋏ q`, `p < ^∀ p`). An atom reads two numeral
chains at environment slots `idx d t ≤ d + t` (`idx_le`), each at level
`Cn + 6 · idx` (`SizedLNumOK.numChain_le`). A negated atom costs the factor
`10` of `neg_level` once.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedEnvForm

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.EnvTransform
open LeanProofs.ZFCinPA.SizedLNumOK (Cn numChain_le)
open LeanProofs.ZFCinPA.SizedCongruence (le_of_add_eq)
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence (conn_le verum_le)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Constants -/

/-- The fixed codes of the environment transform. -/
def Ef0 : V := (appXCode : V) + ((appYCode : V) + ((eqXYCode : V) + ((memXYCode : V) +
  ((⌜econsP⌝ : V) + ((⌜∼econsP⌝ : V) + ((⌜domYP⌝ : V) + ((⌜∼domYP⌝ : V) + (Cn + 2))))))))

theorem appX_le : ((appXCode : ℕ) : V) ≤ Ef0 := le_self_add
theorem appY_le : ((appYCode : ℕ) : V) ≤ Ef0 := le_trans le_self_add le_add_self
theorem eqXY_le : ((eqXYCode : ℕ) : V) ≤ Ef0 :=
  le_trans le_self_add (le_trans le_add_self le_add_self)
theorem memXY_le : ((memXYCode : ℕ) : V) ≤ Ef0 :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self le_add_self))
theorem econs_le : (⌜econsP⌝ : V) ≤ Ef0 :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    le_add_self)))
theorem necons_le : (⌜∼econsP⌝ : V) ≤ Ef0 :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    (le_trans le_add_self le_add_self))))
theorem domY_le : (⌜domYP⌝ : V) ≤ Ef0 :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    (le_trans le_add_self (le_trans le_add_self le_add_self)))))
theorem ndomY_le : (⌜∼domYP⌝ : V) ≤ Ef0 :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self le_add_self))))))
theorem Cn_le_Ef0 : (Cn : V) ≤ Ef0 :=
  le_trans le_self_add (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
      le_add_self)))))))
theorem two_le_Ef0 : (2 : V) ≤ Ef0 :=
  le_trans le_add_self (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
    (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
      le_add_self)))))))

/-- The constant of the transform bound. -/
def Eb : V := 10 * Ef0 + 200

/-! ## Atoms -/

theorem idx_le {d t : V} (ht : IsUTerm ℒₛₑₜ t) : idx d t ≤ d + t := by
  rcases term_var ht with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · rw [idx_bvar]
    exact le_trans (show z ≤ (^#z : V) from le_trans (le_pair_right _ _) le_self_add) le_add_self
  · rw [idx_fvar]
    exact _root_.add_le_add le_rfl (show x ≤ (^&x : V) from le_trans (le_pair_right _ _) le_self_add)

/-- The transformed atom reading slots `a` and `b`, eighteen levels above them. -/
theorem atomCode_le {R a b u : V} (ha : Ef0 + 6 * a ≤ u) (hb : Ef0 + 6 * b ≤ u) :
    atomCode R a b ≤ lvB (u + 18) := by
  have hE : Ef0 ≤ u := le_trans le_self_add ha
  have h2 : (2 : V) ≤ u := le_trans two_le_Ef0 hE
  have hc : ∀ {c : V}, c ≤ Ef0 → c ≤ lvB u := fun h => le_trans (le_trans h hE) (le_lvB_self u)
  have hNa : numChainCode a ≤ lvB u :=
    lift_lvB (numChain_le a) (le_trans (_root_.add_le_add Cn_le_Ef0 le_rfl) ha)
  have hNb : numChainCode b ≤ lvB u :=
    lift_lvB (numChain_le b) (le_trans (_root_.add_le_add Cn_le_Ef0 le_rfl) hb)
  have up : ∀ k : V, (2 : V) ≤ u + k := fun k => le_trans h2 le_self_add
  -- `∃ (N_a ∧ appX)` and `∃ (N_b ∧ appY)`, six levels each
  have x1 := pair_lvB (up 4) (tag_le_lvB (k := 7) (by norm_num) (up 4))
    (conn_le (tag := 4) h2 (by norm_num) hNa (hc appX_le))
  have x2 := pair_lvB (up 4) (tag_le_lvB (k := 7) (by norm_num) (up 4))
    (conn_le (tag := 4) h2 (by norm_num) hNb (hc appY_le))
  have hm : ∀ {m : V}, u ≤ m → (2 : V) ≤ m := fun h => le_trans h2 h
  have hr : (if R = 0 then ((eqXYCode : ℕ) : V) else ((memXYCode : ℕ) : V)) ≤ lvB (u + 4 + 2) := by
    split
    · exact lift_lvB (hc eqXY_le) (le_trans le_self_add le_self_add)
    · exact lift_lvB (hc memXY_le) (le_trans le_self_add le_self_add)
  have y := conn_le (tag := 4) (hm (show u ≤ u + 4 + 2 from le_of_add_eq (y := 6) (by ring)))
    (by norm_num) x2 hr
  have z := conn_le (tag := 4) (hm (show u ≤ u + 4 + 2 + 4 from le_of_add_eq (y := 10) (by ring)))
    (by norm_num) (lift_lvB x1 le_self_add) y
  have w1 := pair_lvB (hm (show u ≤ u + 4 + 2 + 4 + 4 from le_of_add_eq (y := 14) (by ring)))
    (tag_le_lvB (k := 7) (by norm_num)
      (hm (show u ≤ u + 4 + 2 + 4 + 4 from le_of_add_eq (y := 14) (by ring)))) z
  have w2 := pair_lvB (hm (show u ≤ u + 4 + 2 + 4 + 4 + 2 from le_of_add_eq (y := 16) (by ring)))
    (tag_le_lvB (k := 7) (by norm_num)
      (hm (show u ≤ u + 4 + 2 + 4 + 4 + 2 from le_of_add_eq (y := 16) (by ring)))) w1
  unfold atomCode
  exact le_trans w2 (lvB_mono (le_of_eq (by ring)))

theorem atomOf_le {n k r v : V} (hR : (ℒₛₑₜ).IsRel k r) (hv : IsSemitermVec ℒₛₑₜ k n v) :
    atomOf n r v ≤ lvB (Ef0 + 6 * (n + ⟪k, r, v⟫) + 18) := by
  obtain ⟨rfl, -⟩ := isRel_set hR
  have hvX : v ≤ ⟪(2 : V), r, v⟫ := le_trans (le_pair_right r v) (le_pair_right 2 _)
  have hi : ∀ i < (2 : V), idx n v.[i] ≤ n + ⟪(2 : V), r, v⟫ := fun i hi =>
    le_trans (idx_le (hv.nth hi).isUTerm)
      (_root_.add_le_add le_rfl (le_trans (nth_lt_self (by simpa [hv.lh] using hi)).le hvX))
  have hb : ∀ i < (2 : V), Ef0 + 6 * idx n v.[i] ≤ Ef0 + 6 * (n + ⟪(2 : V), r, v⟫) := fun i h =>
    _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left (hi i h) (by norm_num))
  exact atomCode_le (hb 0 (by norm_num)) (hb 1 (by norm_num))

/-! ## The transform -/

theorem falsum_le {m : V} (hm : 2 ≤ m) : (^⊥ : V) ≤ lvB m :=
  le_trans (show (^⊥ : V) ≤ 16 by simp [qqFalsum, pair]; norm_num)
    (le_trans (le_of_eq lvB_two.symm) (lvB_mono hm))

theorem two_le_Eb (n p : V) : (2 : V) ≤ Eb + 100 * n + 200 * p :=
  le_trans (le_of_add_eq (y := 10 * Ef0 + 198) (by unfold Eb; ring)) (le_trans le_self_add le_self_add)

/-- The quantifier case of `envForm_le`: `Q Q (A ⊙ (B ⊙ e))` with outer tag `k`,
inner connective tag `j` and two constants bounded by `Ef0`. -/
theorem quant_le {n p e a b k j : V} (hk : k ≤ 16) (hj : j ≤ 16) (ha : a ≤ Ef0) (hb : b ≤ Ef0)
    (ih : e ≤ lvB (Eb + 100 * (n + 1) + 200 * p)) :
    ⟪k, ⟪k, ⟪j, ⟪a, ⟪j, ⟪b, e⟫⟫ + 1⟫⟫ + 1⟫ + 1⟫ + 1 ≤
      lvB (Eb + 100 * n + 200 * (⟪k, p⟫ + 1)) := by
  have hpx : p ≤ ⟪k, p⟫ := le_pair_right k p
  set u := Eb + 100 * n + 200 * ⟪k, p⟫ + 100 with hu
  have h2 : (2 : V) ≤ u := le_trans (two_le_Eb n ⟪k, p⟫) le_self_add
  have hEu : Ef0 ≤ u := le_trans (show Ef0 ≤ Eb from le_of_add_eq (y := 9 * Ef0 + 200) (by unfold Eb; ring))
    (show Eb ≤ u by rw [hu]; exact le_trans le_self_add (le_trans le_self_add le_self_add))
  have hc : ∀ {c : V}, c ≤ Ef0 → c ≤ lvB u := fun h => le_trans (le_trans h hEu) (le_lvB_self u)
  have ihu : e ≤ lvB u := lift_lvB ih (by
    rw [hu]
    exact le_trans (le_of_eq (by ring))
      (_root_.add_le_add (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hpx (by norm_num)))
        le_rfl))
  have b1 := conn_le (tag := j) h2 hj (hc hb) ihu
  have b2 := conn_le (tag := j) (le_trans h2 le_self_add) hj (lift_lvB (hc ha) le_self_add) b1
  have b3 := pair_lvB (le_trans h2 (le_trans le_self_add le_self_add))
    (tag_le_lvB (k := k) hk (le_trans h2 (le_trans le_self_add le_self_add))) b2
  have b4 := pair_lvB (le_trans h2 (le_trans le_self_add (le_trans le_self_add le_self_add)))
    (tag_le_lvB (k := k) hk (le_trans h2 (le_trans le_self_add (le_trans le_self_add le_self_add))))
    b3
  exact le_trans b4 (lvB_mono (le_of_add_eq (y := 88) (by rw [hu]; ring)))

set_option maxHeartbeats 4000000 in
/-- **The environment transform grows linearly in depth and code.** -/
theorem envForm_le {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) :
    envForm n p ≤ lvB (Eb + 100 * n + 200 * p) := by
  refine IsSemiformula.sigma1_structural_induction (L := ℒₛₑₜ)
    (P := fun n p => envForm n p ≤ lvB (Eb + 100 * n + 200 * p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · simp only [lvB]
    definability
  · -- atoms
    intro n k r v hR hv
    rw [envForm_rel hR hv.isUTerm]
    refine le_trans (atomOf_le hR hv) (lvB_mono ?_)
    have hX : ⟪k, r, v⟫ ≤ (^rel k r v : V) := le_trans (le_pair_right 0 _) le_self_add
    exact le_trans (le_of_add_eq (y := 9 * Ef0 + 182 + 94 * n + 194 * ⟪k, r, v⟫) (by unfold Eb; ring))
      (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hX (by norm_num)))
  · -- negated atoms
    intro n k r v hR hv
    rw [envForm_nrel hR hv.isUTerm]
    refine le_trans (neg_level _ _ (atomOf_le hR hv) (isSemiformula_atomOf n r v).isUFormula)
      (lvB_mono ?_)
    have hX : ⟪k, r, v⟫ ≤ (^nrel k r v : V) := le_trans (le_pair_right 1 _) le_self_add
    exact le_trans (le_of_add_eq (y := 10 + 40 * n + 140 * ⟪k, r, v⟫) (by unfold Eb; ring))
      (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hX (by norm_num)))
  · intro n
    rw [envForm_verum]
    exact verum_le (two_le_Eb n _)
  · intro n
    rw [envForm_falsum]
    exact falsum_le (two_le_Eb n _)
  · -- conjunction
    intro n p q hp hq ihp ihq
    rw [envForm_and hp.isUFormula hq.isUFormula,
      show (p ^⋏ q : V) = ⟪4, p, q⟫ + 1 from rfl]
    have hpx : p ≤ ⟪4, p, q⟫ := le_trans (le_pair_left p q) (le_pair_right 4 _)
    have hqx : q ≤ ⟪4, p, q⟫ := le_trans (le_pair_right p q) (le_pair_right 4 _)
    have l := conn_le (tag := 4) (two_le_Eb n ⟪4, p, q⟫) (by norm_num)
      (lift_lvB ihp (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hpx (by norm_num))))
      (lift_lvB ihq (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hqx (by norm_num))))
    exact le_trans l (lvB_mono (le_of_add_eq (y := 196) (by ring)))
  · -- disjunction
    intro n p q hp hq ihp ihq
    rw [envForm_or hp.isUFormula hq.isUFormula,
      show (p ^⋎ q : V) = ⟪5, p, q⟫ + 1 from rfl]
    have hpx : p ≤ ⟪5, p, q⟫ := le_trans (le_pair_left p q) (le_pair_right 5 _)
    have hqx : q ≤ ⟪5, p, q⟫ := le_trans (le_pair_right p q) (le_pair_right 5 _)
    have l := conn_le (tag := 5) (two_le_Eb n ⟪5, p, q⟫) (by norm_num)
      (lift_lvB ihp (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hpx (by norm_num))))
      (lift_lvB ihq (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hqx (by norm_num))))
    exact le_trans l (lvB_mono (le_of_add_eq (y := 196) (by ring)))
  · -- universal quantifier
    intro n p hp ih
    rw [envForm_all hp.isUFormula, show (^∀ p : V) = ⟪6, p⟫ + 1 from rfl]
    exact quant_le (k := 6) (j := 5) (by norm_num) (by norm_num) necons_le ndomY_le ih
  · -- existential quantifier
    intro n p hp ih
    rw [envForm_exs hp.isUFormula, show (^∃ p : V) = ⟪7, p⟫ + 1 from rfl]
    exact quant_le (k := 7) (j := 4) (by norm_num) (by norm_num) econs_le domY_le ih

end LeanProofs.ZFCinPA.SizedEnvForm
