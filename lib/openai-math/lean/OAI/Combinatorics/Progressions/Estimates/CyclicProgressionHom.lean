-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import OAI.Combinatorics.Progressions.Geometry.CyclicProgressionCoordinates
import OAI.Compat.Core

namespace OAI

section

namespace Erdos3.BohrProgression.CyclicCenteredGAP

open scoped BigOperators

variable {N : ℕ} {G : Type*} [AddCommGroup G]

lemma sum_predParam_smul_add (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) (v : Fin Q.rank → G) :
    (∑ j, (Q.predParam x i hi j : ℕ) • v j) + v i = ∑ j, (x j : ℕ) • v j := by
  classical
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ)
    (fun j => (x j : ℕ) • v j) (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i, (Q.predParam x i hi j : ℕ) • v j =
      ∑ j ∈ Finset.univ.erase i, (x j : ℕ) • v j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)]
  have hterm : ((x i : ℕ) - 1) • v i + v i = (x i : ℕ) • v i := by
    simpa only [add_nsmul, one_nsmul] using
      congrArg (fun n : ℕ => n • v i) (Nat.sub_add_cancel hi)
  rw [hrest, Q.predParam_apply_self, add_assoc, hterm]

noncomputable def freimanStep (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (i : Fin Q.rank) : G :=
  if hi : 0 < Q.radius i then L (Q.eval (Q.unitParam i hi)) - L (Q.eval Q.minParam)
  else 0

noncomputable def freimanAffine (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (x : Q.Param) : G :=
  L (Q.eval Q.minParam) + ∑ i, (x i : ℕ) • Q.freimanStep L i

lemma freimanAffine_pred_add_step (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (x : Q.Param) (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    Q.freimanAffine L x = Q.freimanAffine L (Q.predParam x i hi) + Q.freimanStep L i := by
  unfold freimanAffine
  rw [add_assoc, Q.sum_predParam_smul_add]

theorem freimanAffine_eq [NeZero N] (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t))
    (x : Q.Param) : Q.freimanAffine L x = L (Q.eval x) := by
  classical
  induction hweight : (∑ i, (x i : ℕ)) using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases hk : k = 0
    · have hsumzero : ∑ i, (x i : ℕ) = 0 := hweight.trans hk
      have hxzero (i : Fin Q.rank) : (x i : ℕ) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp
          hsumzero i (Finset.mem_univ i)
      have hx : x = Q.minParam := by
        funext i
        apply Fin.ext
        exact hxzero i
      subst x
      simp [freimanAffine, minParam]
    · have hsumpos : 0 < ∑ i, (x i : ℕ) := by omega
      rw [Finset.sum_pos_iff_of_nonneg (by simp)] at hsumpos
      obtain ⟨i, _hiuniv, hi⟩ := hsumpos
      have hradius : 0 < Q.radius i := by
        have hix := (x i).isLt
        change (x i : ℕ) < 2 * Q.radius i + 1 at hix
        omega
      let y := Q.predParam x i hi
      have hyweight : (∑ j, (y j : ℕ)) + 1 = ∑ j, (x j : ℕ) :=
        Q.sum_predParam_add_one x i hi
      have hylt : (∑ j, (y j : ℕ)) < k := by omega
      have ihy : Q.freimanAffine L y = L (Q.eval y) := ih _ hylt y rfl
      have hrel := hadd y (Q.unitParam i hradius) x Q.minParam
        (Q.eval_predParam_add_eval_unitParam x i hi hradius)
      rw [Q.freimanAffine_pred_add_step L x i hi, ihy]
      simp only [freimanStep, dite_eq_left hradius]
      calc
        L (Q.eval y) + (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) =
            (L (Q.eval y) + L (Q.eval (Q.unitParam i hradius))) - L (Q.eval Q.minParam) := by abel
        _ = L (Q.eval x) := by rw [hrel, add_sub_cancel_right]

end Erdos3.BohrProgression.CyclicCenteredGAP

end

section

namespace Erdos3.BohrProgression.CyclicCenteredGAP

open scoped BigOperators

variable {N : ℕ} {G : Type*} [AddCommGroup G]

def centerParam (Q : CyclicCenteredGAP N) : Q.Param := fun i => ⟨Q.radius i, by omega⟩

@[simp] lemma eval_centerParam (Q : CyclicCenteredGAP N) : Q.eval Q.centerParam = 0 := by
  simp [eval, coeff, centerParam]

lemma eval_mem_carrier (Q : CyclicCenteredGAP N) (x : Q.Param) : Q.eval x ∈ Q.carrier :=
  Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

lemma coeff_injective (Q : CyclicCenteredGAP N) : Function.Injective Q.coeff := by
  intro x y h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  simp only [coeff] at hi
  omega

noncomputable def coefficientBox (Q : CyclicCenteredGAP N) : Finset (Fin Q.rank → ℤ) :=
  Finset.univ.image Q.coeff

lemma mem_coefficientBox (Q : CyclicCenteredGAP N) {z : Fin Q.rank → ℤ} :
    z ∈ Q.coefficientBox ↔ ∃ x : Q.Param, Q.coeff x = z := by
  simp [coefficientBox]

lemma mem_coefficientBox_iff_abs_le (Q : CyclicCenteredGAP N) {z : Fin Q.rank → ℤ} :
    z ∈ Q.coefficientBox ↔ ∀ i, |z i| ≤ (Q.radius i : ℤ) := by
  rw [Q.mem_coefficientBox]
  constructor
  · rintro ⟨x, rfl⟩
    exact Q.coeff_abs_le x
  · intro hz
    let x : Q.Param := fun i => ⟨(z i + Q.radius i).toNat, by
      have hi := abs_le.mp (hz i)
      omega⟩
    refine ⟨x, ?_⟩
    funext i
    have hi := abs_le.mp (hz i)
    dsimp [coeff, x]
    omega

noncomputable def freimanHom (Q : CyclicCenteredGAP N) (L : ZMod N → G) :
    (Fin Q.rank → ℤ) →+ G where
  toFun z := ∑ i, z i • Q.freimanStep L i
  map_zero' := by simp
  map_add' x y := by simp [add_zsmul, Finset.sum_add_distrib]

theorem freimanHom_coeff [NeZero N] (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (hzero : L 0 = 0)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t))
    (x : Q.Param) : Q.freimanHom L (Q.coeff x) = L (Q.eval x) := by
  have hx := Q.freimanAffine_eq L hadd x
  have hc := Q.freimanAffine_eq L hadd Q.centerParam
  simp only [freimanAffine, centerParam, eval_centerParam, hzero] at hc
  have heq : Q.freimanHom L (Q.coeff x) =
      (∑ i, (x i : ℕ) • Q.freimanStep L i) -
        ∑ i, Q.radius i • Q.freimanStep L i := by
    change (∑ i, Q.coeff x i • Q.freimanStep L i) = _
    simp only [coeff, sub_zsmul, natCast_zsmul]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [heq]
  change L (Q.eval Q.minParam) + (∑ i, (x i : ℕ) • Q.freimanStep L i) = _ at hx
  have hbase : L (Q.eval Q.minParam) = -(∑ i, Q.radius i • Q.freimanStep L i) :=
    eq_neg_of_add_eq_zero_left hc
  rw [hbase] at hx
  simpa only [sub_eq_add_neg, add_comm] using hx

theorem freimanHom_injOn [NeZero N] (Q : CyclicCenteredGAP N) (hQ : Q.Proper)
    (L : ZMod N → G) (hL : Set.InjOn L (Q.carrier : Set _)) (hzero : L 0 = 0)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t)) :
    Set.InjOn (Q.freimanHom L) (Q.coefficientBox : Set _) := by
  intro z hz w hw hzw
  obtain ⟨x, rfl⟩ := Q.mem_coefficientBox.mp hz
  obtain ⟨y, rfl⟩ := Q.mem_coefficientBox.mp hw
  rw [Q.freimanHom_coeff L hzero hadd, Q.freimanHom_coeff L hzero hadd] at hzw
  exact congrArg Q.coeff (hQ (hL (Q.eval_mem_carrier x) (Q.eval_mem_carrier y) hzw))

theorem image_freimanHom [NeZero N] [DecidableEq G] (Q : CyclicCenteredGAP N) (L : ZMod N → G)
    (hzero : L 0 = 0)
    (hadd : ∀ x y z t : Q.Param,
      Q.eval x + Q.eval y = Q.eval z + Q.eval t →
        L (Q.eval x) + L (Q.eval y) = L (Q.eval z) + L (Q.eval t)) :
    Q.coefficientBox.image (Q.freimanHom L) = Q.carrier.image L := by
  classical
  simp only [coefficientBox, carrier, Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact Q.freimanHom_coeff L hzero hadd x

end Erdos3.BohrProgression.CyclicCenteredGAP

end

end OAI
