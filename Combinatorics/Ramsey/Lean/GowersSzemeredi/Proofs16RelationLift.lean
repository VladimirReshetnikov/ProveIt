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
  classical
  simp [lastLiftRelation]

theorem lastLiftRelation_fiber_le {N k : Nat} [NeZero N] {Λ : Finset (Point N k × ZMod N)}
    {M : Nat} (hfib : ∀ x : Point N k, (Λ.filter fun z => z.1 = x).card ≤ M)
    (w : Point N (k + 1)) :
    ((lastLiftRelation Λ).filter fun z => z.1 = w).card ≤ M := by
  classical
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
      have h3 := congrArg Prod.snd heq
      simpa using h3
    exact Prod.ext (h1.trans h1'.symm) h2

/-- **Synchronized retiling of a relation across one unused coordinate.** -/
theorem MultiplyLinearWith.relation_unused_coordinate_cover {N k m v : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Λ : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinearWith Qb Eb Λ)
    (epsilon : Real) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hQ : 0 ≤ Qb epsilon) (hE : 0 ≤ Eb epsilon)
    (T : Box N k) (I : ModAP N) (hT : T.IsProper) (hI : I.IsProper)
    (hstep : I.step = T.commonDiff) (u : (ZMod N)ˣ) (hu : I.step = (↑u : ZMod N))
    (hk : 0 < k) (hm : 4 ≤ m) (hmT : m ≤ T.width) (hmI : m ≤ I.length)
    (hv : 1 ≤ v)
    (hfit : (v : Real) ^ 2 + 1 ≤ ((m : Real) / 8) ^ (Eb epsilon)) :
    ∃ (q : Nat) (G : Finset (Point N (k + 1))) (L : Nat)
      (S : Fin L → Box N (k + 1)) (mu : Fin L → Fin q → Point N (k + 1) → ZMod N),
      (q : Real) ≤ Qb epsilon ∧
      G ⊆ lastProductSet T.carrier I.carrier ∧
      (1 - epsilon) * ((lastProductSet T.carrier I.carrier).card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (S j).carrier → z ∈ G → ∀ y, (section16Init z, y) ∈ Λ →
        ∃ i, y = mu j i z := by
  classical
  obtain ⟨q, H, b, P, n, R, mu, hq, hH, hHm, hPpart, hPproper,
      hPaxes, hPstep, hRpart, hRproper, hRwidth, hmu, hc⟩ :=
    hML.short_parent_cover epsilon he he1 hQ hE T I hT hI hk hm hmT hmI
  let e := section5NatFlattenEquiv n
  let R' := boxFlatten n R
  have hR'part : IsBoxPartition R' T := boxFlatten_partition T P n R hPpart hRpart
  have hvfit (j : Fin (∑ a, n a)) : v ^ 2 ≤ (R' j).width - 1 := by
    have hh := hfit.trans (hRwidth (e.symm j).1 (e.symm j).2)
    have hh' : v ^ 2 + 1 ≤ (R' j).width := by exact_mod_cast hh
    omega
  have hne (j : Fin (∑ a, n a)) : (R' j).carrier.Nonempty := by
    apply Box.carrier_nonempty_of_axis_pos
    intro a
    have hw := (R' j).width_le_axis_length a
    have hh := hvfit j
    have hv2 : 1 ≤ v ^ 2 := by nlinarith
    omega
  let axis : Fin k := ⟨0, hk⟩
  let parent := fun j : Fin (∑ a, n a) => (P (e.symm j).1).axis axis
  have hsub (j : Fin (∑ a, n a)) : ((R' j).axis axis).carrier ⊆ (parent j).carrier :=
    (R' j).axis_carrier_subset_of_carrier_subset (P (e.symm j).1) (hne j)
      (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) axis
  have hparentstep (j : Fin (∑ a, n a)) : (parent j).step = (↑u : ZMod N) := by
    dsimp only [parent]
    rw [(P _).axis_step, hPstep, ← hstep, hu]
  have hparallel (j : Fin (∑ a, n a)) : I.step = (parent j).step := by
    rw [hparentstep, hu]
  let G := lastProductSet H I.carrier
  let D : ZMod N → Finset (Point N (k + 1)) := fun y =>
    Finset.univ.filter fun z => (section16Init z, y) ∈ Λ
  let nu := fun j : Fin (∑ a, n a) => fun i : Fin q =>
    fun z : Point N (k + 1) => mu (e.symm j).1 (e.symm j).2 i (section16Init z)
  have hnu : ∀ j i, IsMultilinear (nu j i) := by
    intro j i
    exact (hmu (e.symm j).1 (e.symm j).2 i).lift_last
  have hcover : ∀ (y : ZMod N) j z, section16Init z ∈ (R' j).carrier → z ∈ D y →
      z ∈ (fun _ : ZMod N => G) y → ∃ i, (fun (y : ZMod N) (_ : Point N (k + 1)) => y) y z =
        nu j i z := by
    intro y j z hzR hzD hzG
    have hzΛ := (Finset.mem_filter.mp hzD).2
    have hzH := (Finset.mem_filter.mp hzG).2.1
    exact hc (e.symm j).1 (e.symm j).2 (section16Init z) hzR hzH y hzΛ
  obtain ⟨L, S, nu', hSpart, hSproper, hnu', hc'⟩ := section16_synchronize_base_cover_family
    T I hI R' hR'part (fun j => hRproper _ _) parent axis (fun _ => u)
    hparentstep hparallel hsub (fun j => (hPaxes (e.symm j).1 axis).2.1)
    (fun j => (hPaxes (e.symm j).1 axis).2.2) hv hvfit D (fun _ => G)
    (fun (y : ZMod N) (_ : Point N (k + 1)) => y) nu hnu hcover
  obtain ⟨hG, hGm⟩ := lastProductSet_good_mass T.carrier H I.carrier epsilon hH hHm
  refine ⟨q, G, L, S, nu', hq, hG, hGm, hSpart, hSproper, hnu', ?_⟩
  intro j z hz hzG y hy
  exact hc' y j z hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩) hzG

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
  classical
  intro theta ht ht1 P hP
  obtain ⟨ha, ha1⟩ := hE theta ht ht1
  have hA : 0 < Eb theta / 16 := by positivity
  have hmass : (1 - theta) * (P.carrier.card : Real) ≤ P.carrier.card := by
    have hnonneg : (0 : Real) ≤ P.carrier.card := by positivity
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
        interval_cases h : P.width
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
