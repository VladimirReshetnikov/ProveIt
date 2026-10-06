import GowersSzemeredi.Proofs13EdgeModels
import GowersSzemeredi.Proofs13QuadraticRecurrence

/-! Density of the vertical-edge domain at a strong height. Retaining one
actual edge in the arrangement encoding gives the needed linear cardinality
bound, rather than only the ambient bound `N^31`. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- One edge and twenty-nine free residue coordinates determine an additive
sixteen-edge tuple at a fixed height. -/
theorem section13_height_count_le_edge_card {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N) :
    arrangementCountAtHeight 8 A h ≤ (verticalEdgeDomain A h).card * N ^ 29 := by
  classical
  let T := {x : Fin 16 → Section13Edges A h //
    HasEqualHalfSums (k := 8) (fun i ↦ (section13VerticalDomain A h).index (x i))}
  let Code := Section13Edges A h × (Fin 14 → ZMod N) × (Fin 15 → ZMod N)
  let encode : T → Code := fun x ↦
    (x.val (Fin.last 15), (fun i ↦ (x.val i.succ.castSucc).val.1),
      fun i ↦ (x.val i.castSucc).val.2)
  have hinj : Function.Injective encode := by
    intro x y hxy
    have hlast : x.val (Fin.last 15) = y.val (Fin.last 15) := congrArg Prod.fst hxy
    have hxrest (i : Fin 14) : (x.val i.succ.castSucc).val.1 =
        (y.val i.succ.castSucc).val.1 :=
      congrFun (congrArg (fun c : Code ↦ c.2.1) hxy) i
    have hyrest (i : Fin 15) : (x.val i.castSucc).val.2 = (y.val i.castSucc).val.2 :=
      congrFun (congrArg (fun c : Code ↦ c.2.2) hxy) i
    have hxall : (fun i ↦ (x.val i).val.1) = (fun i ↦ (y.val i).val.1) := by
      apply stage135_additive_ext x.property y.property
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact congrArg (fun z : Section13Edges A h ↦ z.val.1) hlast
      · exact hxrest j
    have hyall : (fun i ↦ (x.val i).val.2) = (fun i ↦ (y.val i).val.2) := by
      funext i
      refine Fin.lastCases ?_ (fun j ↦ hyrest j) i
      exact congrArg (fun z : Section13Edges A h ↦ z.val.2) hlast
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact Prod.ext (congrFun hxall i) (congrFun hyall i)
  have hcount : arrangementCountAtHeight 8 A h = Fintype.card T := by
    rw [← section13_domain_additive_count]
    unfold domainAdditiveTupleCount countWhere
    rw [Finset.filter_congr_decidable, ← Fintype.card_subtype]
  calc
    _ = Fintype.card T := hcount
    _ ≤ Fintype.card Code := Fintype.card_le_of_injective encode hinj
    _ = (verticalEdgeDomain A h).card * N ^ 29 := by
      simp [Code, Fintype.card_coe, ← pow_add]

/-- A strong height has the claimed edge-domain density `alpha^32/16`. -/
theorem section13_strong_height_edge_density {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h) :
    S.alpha ^ 32 / 16 * (N : Real) ^ 2 ≤ (verticalEdgeDomain S.A h).card := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hbound : (section13C S h : Real) ≤
      ((verticalEdgeDomain S.A h).card : Real) * (N : Real) ^ 29 := by
    exact_mod_cast section13_height_count_le_edge_card S.A h
  apply le_of_mul_le_mul_right (a := (N : Real) ^ 29) _ (pow_pos hN _)
  calc
    _ = S.alpha ^ 32 * (N : Real) ^ 31 / 16 := by ring
    _ ≤ section13C S h := hh.1
    _ ≤ _ := hbound

/-- The actual normalized size of the height-edge domain. -/
def section13EdgeDensity {N : Nat} [NeZero N] (S : Section13Context N) (h : ZMod N) : Real :=
  (verticalEdgeDomain S.A h).card / (N : Real) ^ 2

/-- Normalizing the edge cardinality preserves its exact value. -/
theorem section13_edge_density_card {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) :
    ((verticalEdgeDomain S.A h).card : Real) = section13EdgeDensity S h * (N : Real) ^ 2 := by
  unfold section13EdgeDensity
  rw [div_mul_cancel₀ _ (by exact_mod_cast pow_ne_zero 2 (NeZero.ne N))]

/-- At a strong height the actual edge density lies between `alpha^32/16`
and `alpha`, rather than being equal to the lower bound. -/
theorem section13_edge_density_bounds {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h) :
    0 < section13EdgeDensity S h ∧
      S.alpha ^ 32 / 16 ≤ section13EdgeDensity S h ∧ section13EdgeDensity S h ≤ S.alpha := by
  classical
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hlo : S.alpha ^ 32 / 16 ≤ section13EdgeDensity S h := by
    apply (le_div_iff₀ (pow_pos hN 2)).mpr
    exact section13_strong_height_edge_density S h hh
  refine ⟨lt_of_lt_of_le (by have := S.alpha_pos; positivity) hlo, hlo, ?_⟩
  apply (div_le_iff₀ (pow_pos hN 2)).mpr
  have hsub : verticalEdgeDomain S.A h ⊆ S.A := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2.1
  calc
    ((verticalEdgeDomain S.A h).card : Real) ≤ S.A.card := by
      exact_mod_cast Finset.card_le_card hsub
    _ = S.alpha * (N : Real) ^ 2 := S.card_A

/-- Strong-height Bohr models with the corrected Stage 13.6 set-size bound.
The density range used by the checked Theorem 10.13 remains explicit, and
the spectrum and radius use the actual edge density. -/
theorem section13_strong_height_bohr_model {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h)
    (hαsixth : S.alpha ≤ 1 / 6) :
    let beta := section13EdgeDensity S h
    let K := domainLargeSpectrum (section13VerticalDomain S.A h)
      (section10Lambda beta * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta beta) Y psi := by
  have hbounds := section13_edge_density_bounds S h hh
  obtain ⟨Y, psi, hsub, hmass, hmodel⟩ := section13_good_height_bohr_model S h hh.2
    (section13EdgeDensity S h) hbounds.1 (hbounds.2.2.trans hαsixth)
    (section13_edge_density_card S h)
  refine ⟨Y, psi, hsub, ?_, hmodel⟩
  let a : Real := S.alpha ^ 32 / 16
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpow : a ^ 6 ≤ section13EdgeDensity S h ^ 6 :=
    pow_le_pow_left₀ ha hbounds.2.1 6
  have hedge : a * (N : Real) ^ 2 ≤ (verticalEdgeDomain S.A h).card :=
    section13_strong_height_edge_density S h hh
  have hproduct : a ^ 6 * (a * (N : Real) ^ 2) ≤
      section13EdgeDensity S h ^ 6 * (verticalEdgeDomain S.A h).card :=
    mul_le_mul hpow hedge (by positivity) (by positivity)
  have hpower : a ^ 6 * a = S.alpha ^ 224 / (2 : Real) ^ 28 := by
    dsimp only [a]
    ring
  calc
    _ ≤ (S.alpha ^ 224 / (2 : Real) ^ 28) * (N : Real) ^ 2 / 20000 := by
      norm_num [zpow_neg]
      have hnonneg : 0 ≤ S.alpha ^ 224 * (N : Real) ^ 2 :=
        mul_nonneg (pow_nonneg S.alpha_pos.le 224) (sq_nonneg _)
      nlinarith only [hnonneg]
    _ = a ^ 6 * (a * (N : Real) ^ 2) / 20000 := by rw [← hpower]; ring
    _ ≤ section13EdgeDensity S h ^ 6 * (verticalEdgeDomain S.A h).card / 20000 :=
      div_le_div_of_nonneg_right hproduct (by norm_num)
    _ ≤ Y.card := hmass

end LeanProofs.GowersSzemeredi
