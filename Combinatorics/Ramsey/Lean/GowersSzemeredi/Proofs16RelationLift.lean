import GowersSzemeredi.Proofs16WithCoordinateLifts
import GowersSzemeredi.Proofs16FamilyAffineLift

/-! Lifting a relation cover across an unused final coordinate.

`MultiplyLinearWith.lift_last` lifts covers of partial functions. The
union of the remainders of many pieces is a relation: in dimension two
each remainder `φ_c(x₀_c, x)` depends only on one coordinate, and their
union is a cylinder over a dimension-one relation. Here the lift is done
for relations.
* `lastLiftRelation Λ = {(z, y) : (init z, y) ∈ Λ}` and its fibre bound.
* `MultiplyLinearWith.relation_unused_coordinate_cover`: synchronized
  retiling. The values `y` play the role of the family index of
  `section16_synchronize_base_cover_family`.
* `MultiplyLinearWith.relation_lift_last`: every scale, with count
  `max (Qb θ) (3^(k+1)·M)` (`M` the fibre bound) and exponent `Eb θ / 16`.
  Short boxes use `section16_coarse_relation_cover`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The cylinder of a relation over an unused final coordinate. -/
def lastLiftRelation {N k : Nat} [NeZero N] (Λ : Finset (Point N k × ZMod N)) :
    Finset (Point N (k + 1) × ZMod N) := by
  classical
  exact Finset.univ.filter fun z => (section16Init z.1, z.2) ∈ Λ

theorem mem_lastLiftRelation {N k : Nat} [NeZero N] {Λ : Finset (Point N k × ZMod N)}
    {z : Point N (k + 1) × ZMod N} :
    z ∈ lastLiftRelation Λ ↔ (section16Init z.1, z.2) ∈ Λ := by
  simp [lastLiftRelation]

theorem lastLiftRelation_fiber_le {N k : Nat} [NeZero N] {Λ : Finset (Point N k × ZMod N)}
    {M : Nat} (hfib : ∀ x : Point N k, (Λ.filter fun z => z.1 = x).card ≤ M)
    (w : Point N (k + 1)) :
    ((lastLiftRelation Λ).filter fun z => z.1 = w).card ≤ M := by
  refine le_trans ?_ (hfib (section16Init w))
  refine Finset.card_le_card_of_injOn (fun z => (section16Init z.1, z.2)) (fun z hz => ?_) ?_
  · obtain ⟨hzΛ, hzw⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨mem_lastLiftRelation.mp hzΛ, ?_⟩
    change section16Init z.1 = section16Init w
    rw [hzw]
  · intro z hz z' hz' heq
    have h1 := (Finset.mem_filter.mp hz).2
    have h1' := (Finset.mem_filter.mp hz').2
    have h2 : z.2 = z'.2 := by
      simpa using congrArg Prod.snd heq
    exact Prod.ext (h1.trans h1'.symm) h2

/-- **A relation cover lifted across an unused final coordinate, at every
scale.** -/
theorem MultiplyLinearWith.relation_lift_last {N k : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {Λ : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinearWith Qb Eb Λ)
    (M : Nat) (hfib : ∀ x : Point N k, (Λ.filter fun z => z.1 = x).card ≤ M)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) (hk : 0 < k) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ (k + 1) * M : Nat) : Real))
      (fun t => Eb t / 16) (lastLiftRelation Λ) := by
  intro theta ht ht1 P hP
  obtain ⟨ha, ha1⟩ := hE theta ht ht1
  have hA : 0 < Eb theta / 16 := by positivity
  have hmass : (1 - theta) * (P.carrier.card : Real) ≤ P.carrier.card := by
    nlinarith
  by_cases hsmall : (P.width : Real) ^ (Eb theta / 16) ≤ 2
  · obtain ⟨L, R, mu, hpart, hproper, hw, hmu, hcov⟩ :=
      section16_coarse_relation_cover (by omega : 0 < k + 1) (lastLiftRelation Λ) M
        (lastLiftRelation_fiber_le hfib) P hP
    refine ⟨L, 3 ^ (k + 1) * M, P.carrier, R, mu, Finset.Subset.rfl, hmass, hpart, hproper,
      le_max_right _ _, ?_, hmu, fun j x hx _ y hy => hcov j x hx y hy⟩
    intro j
    have hmin : (P.width : Real) ^ (Eb theta / 16) ≤ ((min 2 P.width : Nat) : Real) := by
      rcases Nat.lt_or_ge P.width 2 with hlt | hge
      · rw [min_eq_right hlt.le]
        interval_cases _ : P.width
        · simp [Real.zero_rpow hA.ne']
        · simp
      · rw [min_eq_left hge]
        exact_mod_cast hsmall
    exact hmin.trans (by exact_mod_cast hw j)
  · have hlarge : 2 < (P.width : Real) ^ (Eb theta / 16) := lt_of_not_ge hsmall
    obtain ⟨hm4, hw16, hwidth⟩ := with_lift_width_budget ha ha1 P.width hlarge
    obtain ⟨v, hv, hvfit, hvwidth⟩ := section16_lift_width_rounding hw16
    let T := boxInit P
    let I := P.axis (Fin.last k)
    have hI : I.IsProper := hP _
    have hmI : P.width ≤ I.length := P.width_le_axis_length _
    obtain ⟨u, hu⟩ := I.step_isUnit_of_prime hI (by omega)
    have hstep : I.step = T.commonDiff := P.axis_step _
    obtain ⟨q, G, M', Q, mu, hq, hG, hGm, hpart, hproper, hmu, hc⟩ :=
      hML.relation_unused_coordinate_cover theta ht ht1 (hQ theta ht ht1) ha.le T I
        (boxInit_isProper P hP) hI hstep u hu.symm hk hm4 (boxInit_width P hk) hmI hv hvfit
    have hprod : lastProductSet T.carrier I.carrier = P.carrier :=
      (boxInit_last_product P).1.symm
    rw [hprod] at hG hGm hpart
    refine ⟨M', q, G, Q, mu, hG, hGm, hpart, fun j => (hproper j).1,
      hq.trans (le_max_left _ _), fun j => ?_, hmu, ?_⟩
    · exact hwidth.trans (hvwidth.trans (by exact_mod_cast (hproper j).2))
    · intro j z hz hzG y hy
      exact hc j z hz hzG y (mem_lastLiftRelation.mp hy)

end LeanProofs.GowersSzemeredi
