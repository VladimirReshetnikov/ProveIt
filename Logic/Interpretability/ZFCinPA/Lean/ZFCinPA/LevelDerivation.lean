import ZFCinPA.SetCodeLevels

/-!
# Bounded derivations on the level scale

`SizedDerivation.DerivableLe T s (2^e)` costs a factor `1024` in `e` per
rule. When `e = lvB w = 2^(2^w)` and `w ≥ 4` this is at most one level:
`1024·lvB w ≤ lvB w ^ 2 = lvB (w + 1)`. So on the scale

  `DLv T s w := DerivableLe T s (2^(lvB w))`

every primitive rule costs `+1` level, provided every member of the conclusion
is below `lvB w` (`SeqLt s w`). Formula levels are the `SetCodeLevels` levels,
so the two calculi compose. This is the bookkeeping for derivations built by
internal recursion, such as the congruence proofs of `SizedCongruence`.

`spec` is the bounded counterpart of `TDerivation.specialize`: it instantiates
a universal member of a sequent at a term in three levels.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.LevelDerivation

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ## The scale -/

theorem lvB_three : lvB (3 : V) = 256 := by
  rw [show (3 : V) = 2 + 1 by norm_num, lvB_succ, lvB_two]
  norm_num

theorem lvB_four : lvB (4 : V) = 65536 := by
  rw [show (4 : V) = 3 + 1 by norm_num, lvB_succ, lvB_three]
  norm_num

theorem k1024_le_lvB {w : V} (hw : 4 ≤ w) : 1024 ≤ lvB w :=
  le_trans (by rw [lvB_four]; norm_num) (lvB_mono hw)

theorem four_le_lvB' {w : V} (hw : 4 ≤ w) : 4 ≤ lvB w :=
  le_trans (by norm_num) (k1024_le_lvB hw)

theorem step_le {w : V} (hw : 4 ≤ w) : Exp.exp (1024 * lvB w) ≤ Exp.exp (lvB (w + 1)) := by
  refine exp_monotone_le.mpr ?_
  rw [lvB_succ]
  exact mul_le_mul (k1024_le_lvB hw) le_rfl (Arithmetic.zero_le _) (Arithmetic.zero_le _)

/-- `s` has a `T`-derivation with code at most `2^(lvB w)`. -/
def DLv (T : Theory L) [T.Δ₁] (s w : V) : Prop := DerivableLe T s (Exp.exp (lvB w))

/-- Every member of `s` is below `lvB w`. -/
def SeqLt (s w : V) : Prop := ∀ y ∈ s, y < lvB w

namespace SeqLt

theorem le {s w : V} (h : SeqLt s w) : s ≤ Exp.exp (lvB w) := DerivableLe.seq_le le_rfl h

theorem mono {s w w' : V} (h : SeqLt s w) (hw : w ≤ w') : SeqLt s w' :=
  fun y hy => lt_of_lt_of_le (h y hy) (lvB_mono hw)

theorem insert {x s w : V} (hx : x < lvB w) (h : SeqLt s w) : SeqLt (insert x s) w :=
  DerivableLe.insert_lt hx h

theorem of_subset {s s' w : V} (h : SeqLt s w) (hs : s' ⊆ s) : SeqLt s' w :=
  fun y hy => h y (hs hy)

theorem empty (w : V) : SeqLt (∅ : V) w := fun y hy => by simp at hy

end SeqLt

namespace DLv

variable {T : Theory L} [T.Δ₁]

theorem mono {s w w' : V} (h : DLv T s w) (hw : w ≤ w') : DLv T s w' :=
  DerivableLe.mono h (exp_monotone_le.mpr (lvB_mono hw))

theorem isFormulaSet {s w : V} (h : DLv T s w) : IsFormulaSet L s := DerivableLe.isFormulaSet h

theorem ofSetEq {s s' w : V} (h : ∀ x, x ∈ s' ↔ x ∈ s) (hd : DLv T s' w) : DLv T s w :=
  DerivableLe.ofSetEq h hd

theorem em {s w : V} (hw : 4 ≤ w) (hs : SeqLt s w) (hfs : IsFormulaSet L s) (p : V)
    (h : p ∈ s) (hn : neg L p ∈ s) : DLv T s (w + 1) :=
  (DerivableLe.em (four_le_lvB' hw) hs.le hfs p h hn).mono (step_le hw)

theorem verum {s w : V} (hw : 4 ≤ w) (hs : SeqLt s w) (hfs : IsFormulaSet L s)
    (h : ^⊤ ∈ s) : DLv T s (w + 1) :=
  (DerivableLe.verum (four_le_lvB' hw) hs.le hfs h).mono (step_le hw)

theorem and_m {s p q w : V} (hw : 4 ≤ w) (hs : SeqLt s w) (h : p ^⋏ q ∈ s)
    (hp : DLv T (insert p s) w) (hq : DLv T (insert q s) w) : DLv T s (w + 1) :=
  (DerivableLe.and_m (four_le_lvB' hw) hs.le h hp hq).mono (step_le hw)

theorem or_m {s p q w : V} (hw : 4 ≤ w) (hs : SeqLt s w) (h : p ^⋎ q ∈ s)
    (hpq : DLv T (insert p (insert q s)) w) : DLv T s (w + 1) :=
  (DerivableLe.or_m (four_le_lvB' hw) hs.le h hpq).mono (step_le hw)

theorem all_m {s p w : V} (hw : 4 ≤ w) (hs : SeqLt s w) (h : ^∀ p ∈ s)
    (hp : DLv T (insert (free L p) (setShift L s)) w) : DLv T s (w + 1) :=
  (DerivableLe.all_m (four_le_lvB' hw) hs.le h hp).mono (step_le hw)

theorem ex_m {s p t w : V} (hw : 4 ≤ w) (hs : SeqLt s w) (htb : t < lvB w)
    (h : ^∃ p ∈ s) (ht : IsTerm L t) (hp : DLv T (insert (substs1 L t p) s) w) : DLv T s (w + 1) :=
  (DerivableLe.ex_m (four_le_lvB' hw) hs.le
    (le_trans (le_of_lt htb) (le_of_lt (lt_exp _))) h ht hp).mono (step_le hw)

theorem wk {s s' w : V} (hw : 4 ≤ w) (hs : SeqLt s w) (hfs : IsFormulaSet L s) (h : s' ⊆ s)
    (hd : DLv T s' w) : DLv T s (w + 1) :=
  (DerivableLe.wk (four_le_lvB' hw) hs.le hfs h hd).mono (step_le hw)

theorem cut {s w : V} (hw : 4 ≤ w) (hs : SeqLt s w) (p : V) (hpb : p < lvB w)
    (hd₁ : DLv T (insert p s) w) (hd₂ : DLv T (insert (neg L p) s) w) : DLv T s (w + 1) :=
  (DerivableLe.cut (four_le_lvB' hw) hs.le p
    (le_trans (le_of_lt hpb) (le_of_lt (lt_exp _))) hd₁ hd₂).mono (step_le hw)

theorem by_axm {s w : V} (hw : 4 ≤ w) (hs : SeqLt s w) (hfs : IsFormulaSet L s) (p : V)
    (hp : p ∈ s) (hT : p ∈ T.Δ₁Class) : DLv T s (w + 1) :=
  (DerivableLe.by_axm (four_le_lvB' hw) hs.le hfs p hp hT).mono (step_le hw)

/-- A derivation with a standard numeral code `d` sits at level `d`. -/
theorem of_derivationOf {s d : V} (h : DerivationOf T d s) : DLv T s d :=
  ⟨d, le_trans (le_lvB_self d) (le_of_lt (lt_exp _)), h⟩

end DLv

/-! ## Bounded specialization -/

variable {T : Theory L} [T.Δ₁]

theorem formulaSet_insert {φ : Bootstrapping.Formula V L} {s : V} (hs : IsFormulaSet L s) :
    IsFormulaSet L (insert φ.val s) := by
  simp [hs, φ.isSemiformula]

set_option maxHeartbeats 1000000 in
/-- **Specialization, bounded.** A universal member `∀ φ` of a sequent can be
replaced by its instance `φ(t)` at a cost of three levels, provided the
members involved are below `lvB w`. -/
theorem spec {φ : Bootstrapping.Semiformula V L 1} {t : Bootstrapping.Term V L} {Γ w : V}
    (hw : 4 ≤ w) (hΓ : SeqLt Γ w) (hfs : IsFormulaSet L Γ)
    (hA : (∀⁰ φ).val < lvB w) (hI : (φ.subst ![t]).val < lvB w)
    (hE : (∃⁰ ∼φ).val < lvB w) (hN : (∼(φ.subst ![t])).val < lvB w) (ht : t.val < lvB w)
    (h : DLv T (insert (∀⁰ φ).val Γ) w) : DLv T (insert (φ.subst ![t]).val Γ) (w + 3) := by
  set S := insert (φ.subst ![t]).val Γ with hS
  have hSl : SeqLt S w := hΓ.insert hI
  have hSf : IsFormulaSet L S := formulaSet_insert hfs
  -- the universal side, weakened
  have hl : DLv T (insert (∀⁰ φ).val S) (w + 1) :=
    DLv.wk hw (hSl.insert hA) (formulaSet_insert hSf)
      (insert_subset_insert_of_subset _ (by simp [hS])) h
  -- the existential side: `em` then `ex`
  have hsub : substs1 L t.val (∼φ).val = (∼(φ.subst ![t])).val := by
    simp only [substs1, Bootstrapping.Semiformula.val_neg, Bootstrapping.Semiformula.val_substs]
    exact Bootstrapping.substs_neg φ.isSemiformula
      (Bootstrapping.SemitermVec.isSemitermVec (![t] : Bootstrapping.SemitermVec V L 1 0))
  have hex : (∃⁰ ∼φ).val = ^∃ (∼φ).val := by simp
  have hr0 : DLv T (insert (substs1 L t.val (∼φ).val) (insert (∃⁰ ∼φ).val S)) (w + 1) := by
    rw [hsub]
    refine DLv.em hw ((hSl.insert hE).insert hN) (formulaSet_insert (formulaSet_insert hSf))
      (φ.subst ![t]).val (mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr
        (mem_bitInsert_iff.mpr (Or.inl rfl)))))) ?_
    rw [← Bootstrapping.Semiformula.val_neg]
    exact mem_bitInsert_iff.mpr (Or.inl rfl)
  have hr : DLv T (insert (∃⁰ ∼φ).val S) (w + 1 + 1) := by
    refine DLv.ex_m (le_trans hw le_self_add) ((hSl.insert hE).mono le_self_add)
      (lt_of_lt_of_le ht (lvB_mono le_self_add)) (by rw [hex]; simp)
      t.isSemiterm hr0
  have hneg : neg L (∀⁰ φ).val = (∃⁰ ∼φ).val := by
    rw [← Bootstrapping.Semiformula.neg_all]
    simp [Bootstrapping.Semiformula.val_neg]
  have h2 : w ≤ w + 1 + 1 := le_trans le_self_add le_self_add
  have := DLv.cut (T := T) (le_trans hw h2) (hSl.mono h2) (∀⁰ φ).val
    (lt_of_lt_of_le hA (lvB_mono h2)) (hl.mono le_self_add) (by rw [hneg]; exact hr)
  rwa [show w + 1 + 1 + 1 = w + 3 by ring] at this

end LeanProofs.ZFCinPA.LevelDerivation
