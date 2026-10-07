import GowersSzemeredi.Proofs13FejerSurvival

/-! A finite family of intended signed relations gives a lower bound for
Fejer survival. Independent short offsets provide the multiplicity gain. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def fejerShiftedPair {L M : Nat} (hML : 2 * M ≤ L) (positive : Bool)
    (d j : Fin M) : Fin L × Fin L :=
  if positive then (⟨j + d, by omega⟩, ⟨j, by omega⟩)
  else (⟨j, by omega⟩, ⟨j + d, by omega⟩)

theorem fejerShiftedPair_difference {N L M : Nat} (hML : 2 * M ≤ L)
    (positive : Bool) (d j : Fin M) :
    ((fejerShiftedPair hML positive d j).1 - (fejerShiftedPair hML positive d j).2 : ZMod N) =
      (if positive then 1 else -1) * (d : ZMod N) := by
  cases positive <;> simp only [fejerShiftedPair, Bool.false_eq_true, if_false, if_true,
    Fin.val_mk, Nat.cast_add] <;> ring

theorem fejerShiftedPair_injective {L M : Nat} (hML : 2 * M ≤ L) (positive : Bool) :
    Function.Injective (fun v : Fin M × Fin M => fejerShiftedPair hML positive v.1 v.2) := by
  intro v w h
  have h1 := congrArg (fun z : Fin L × Fin L => (z.1 : Nat)) h
  have h2 := congrArg (fun z : Fin L × Fin L => (z.2 : Nat)) h
  cases positive <;> simp only [fejerShiftedPair, Bool.false_eq_true, if_false, if_true,
    Fin.val_mk] at h1 h2 <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

theorem fejerPairRelation_shifted {N L M : Nat} {I : Type*} [Fintype I] [DecidableEq I]
    (hML : 2 * M ≤ L) (positive : I → Bool) (d : Fin M) (w : I → Fin M) (phi : I → ZMod N) :
    fejerPairRelation (fun i => fejerShiftedPair hML (positive i) d (w i)) phi =
      (d : ZMod N) * ∑ i, (if positive i then 1 else -1) * phi i := by
  simp only [fejerPairRelation, fejerShiftedPair_difference, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fejerRelation_count_signal {N L M : Nat}
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (hML : 2 * M ≤ L) (positive : I → Bool) (phi feature : I → ZMod N)
    (hphi : ∑ i, (if positive i then 1 else -1) * phi i = 0)
    (hfeature : ∑ i, (if positive i then 1 else -1) * feature i = 0) :
    M ^ (Fintype.card I + 1) ≤
      countWhere (fun v : I → Fin L × Fin L =>
        fejerPairRelation v phi = 0 ∧ fejerPairRelation v feature = 0) := by
  classical
  let V := {v : I → Fin L × Fin L //
    fejerPairRelation v phi = 0 ∧ fejerPairRelation v feature = 0}
  let f : Fin M × (I → Fin M) → V := fun z =>
    ⟨fun i => fejerShiftedPair hML (positive i) z.1 (z.2 i), by
      constructor <;> rw [fejerPairRelation_shifted]
      · rw [hphi, mul_zero]
      · rw [hfeature, mul_zero]⟩
  have hinj : Function.Injective f := by
    intro v w h
    have heq : ∀ i, (v.1, v.2 i) = (w.1, w.2 i) := by
      intro i
      apply fejerShiftedPair_injective hML (positive i)
      exact congrArg (fun z : V => z.1 i) h
    exact Prod.ext (congrArg (fun z : Fin M × Fin M => z.1) (heq (Classical.arbitrary I)))
      (funext fun i => congrArg (fun z : Fin M × Fin M => z.2) (heq i))
  have hcard := Fintype.card_le_of_injective f hinj
  have hV : Fintype.card V = countWhere (fun v : I → Fin L × Fin L =>
      fejerPairRelation v phi = 0 ∧ fejerPairRelation v feature = 0) := by
    simp only [V, countWhere, Fintype.card_subtype]
    congr 1
    ext v
    simp
  rw [hV] at hcard
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_succ, Nat.mul_comm] using hcard

theorem fejer_kernel_mean_signal_lower {N L M : Nat} [NeZero N]
    {I X : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq X]
    (hL : 0 < L) (hML : 2 * M ≤ L) (positive : I → Bool)
    (vertex : I → X) (phi feature : X → ZMod N)
    (hphi : ∑ i, (if positive i then 1 else -1) * phi (vertex i) = 0)
    (hfeature : ∑ i, (if positive i then 1 else -1) * feature (vertex i) = 0) :
    (((L : Real) ^ 2)⁻¹) ^ Fintype.card I * (M : Real) ^ (Fintype.card I + 1) ≤
      𝔼 c : ZMod N × ZMod N,
        ∏ x ∈ Finset.univ.image vertex,
          finiteFejerKernel L (c.1 * phi x + c.2 * feature x) := by
  have hcount := fejerRelation_count_signal hML positive (phi ∘ vertex) (feature ∘ vertex) hphi hfeature
  have hcountR : (M : Real) ^ (Fintype.card I + 1) ≤
      (countWhere (fun v : I → Fin L × Fin L =>
        fejerPairRelation v (phi ∘ vertex) = 0 ∧
          fejerPairRelation v (feature ∘ vertex) = 0) : Real) := by exact_mod_cast hcount
  exact (mul_le_mul_of_nonneg_left hcountR (by positivity)).trans
    (fejer_kernel_mean_carrier_lower hL vertex phi feature)

end LeanProofs.GowersSzemeredi
