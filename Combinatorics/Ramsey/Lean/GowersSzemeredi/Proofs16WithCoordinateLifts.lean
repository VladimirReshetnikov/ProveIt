import GowersSzemeredi.Proofs16UnusedCoordinateLift
import GowersSzemeredi.Proofs16PolyBaseCase
import GowersSzemeredi.Proofs16EmbeddedLift
import GowersSzemeredi.Proofs16CubicCoverControls

/-! Coordinate lifts for covers with arbitrary controls (`MultiplyLinearWith`),
toward a polynomial-control `PolyCoverAt 2` (Notes L.3, step (A)).

The corpus lifts covers across unused coordinates only with Gowers's printed
controls (`MultiplyLinearFunction.lift_last`). Here the same constructions
are carried out for `MultiplyLinearWith Qb Eb`:
* The preliminary partitions are `MultiplyLinearWith.on_partition` and
  `MultiplyLinearWith.short_parent_cover` (`Proofs16WithLemma6`).
* `MultiplyLinearWith.unused_coordinate_cover` is synchronized retiling
  across one unused final coordinate.
* `MultiplyLinearWith.lift_last` covers at every scale, with count
  `max (Qb θ) 3^(k+1)` and width exponent `Eb θ / 16`. Small boxes are
  covered exactly by the coarse cover, large boxes by synchronized
  retiling.
* `MultiplyLinearWith.coordinateReindex` permutes coordinates with the
  controls unchanged.
* `MultiplyLinearWith.lift_prefix` and `MultiplyLinearWith.lift_embedding`
  extend a cover across any set of unused coordinates. The count becomes
  `max (Qb θ) 3^d` and the width exponent `Eb θ / 16^(d-l)`.

The controls stay polynomial when `Qb` and `Eb` are. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- **Synchronized retiling across one unused final coordinate**, for
arbitrary controls. -/
theorem MultiplyLinearWith.unused_coordinate_cover {N k m v : Nat} [NeZero N]
    {Qb Eb : Real → Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hML : MultiplyLinearWith Qb Eb (partialGraph B phi))
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
      ∀ j z, z ∈ (S j).carrier → section16Init z ∈ B → z ∈ G →
        ∃ i, phi (section16Init z) = mu j i z := by
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
  let D := lastProductSet B Finset.univ
  let nu := fun j : Fin (∑ a, n a) => fun i : Fin q =>
    fun z : Point N (k + 1) => mu (e.symm j).1 (e.symm j).2 i (section16Init z)
  have hnu : ∀ j i, IsMultilinear (nu j i) := by
    intro j i
    exact (hmu (e.symm j).1 (e.symm j).2 i).lift_last
  have hcover : ∀ j z, section16Init z ∈ (R' j).carrier → z ∈ D → z ∈ G →
      ∃ i, phi (section16Init z) = nu j i z := by
    intro j z hzR hzD hzG
    have hzB := (Finset.mem_filter.mp hzD).2.1
    have hzH := (Finset.mem_filter.mp hzG).2.1
    exact hc (e.symm j).1 (e.symm j).2 (section16Init z) hzR hzH
      (phi (section16Init z)) (Finset.mem_image.mpr ⟨section16Init z, hzB, rfl⟩)
  obtain ⟨L, S, nu', hSpart, hSproper, hnu', hc'⟩ := section16_synchronize_base_cover
    T I hI R' hR'part (fun j => hRproper _ _) parent axis (fun _ => u)
    hparentstep hparallel hsub (fun j => (hPaxes (e.symm j).1 axis).2.1)
    (fun j => (hPaxes (e.symm j).1 axis).2.2) hv hvfit D G
    (fun z => phi (section16Init z)) nu hnu hcover
  obtain ⟨hG, hGm⟩ := lastProductSet_good_mass T.carrier H I.carrier epsilon hH hHm
  refine ⟨q, G, L, S, nu', hq, hG, hGm, hSpart, hSproper, hnu', ?_⟩
  intro j z hz hzB hzG
  exact hc' j z hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzB, Finset.mem_univ _⟩) hzG


/-- The width budget of the all-scale lift: above the small-box branch the
retiled width dominates `m^(a/16)`. -/
theorem with_lift_width_budget {a : Real} (ha : 0 < a) (ha1 : a ≤ 1) (m : Nat)
    (hlarge : 2 < (m : Real) ^ (a / 16)) :
    4 ≤ m ∧ 16 ≤ ((m : Real) / 8) ^ a ∧
      (m : Real) ^ (a / 16) ≤ Real.sqrt (((m : Real) / 8) ^ a) / 4 := by
  have hm0 : (0 : Real) < m := by
    by_contra h
    have h0 : (m : Real) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, Real.zero_rpow (by positivity)] at hlarge
    linarith
  have hm1 : (1 : Real) ≤ m := by
    have : 0 < m := by exact_mod_cast hm0
    exact_mod_cast this
  set X := (m : Real) ^ (a / 16) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hma : (m : Real) ^ a = X ^ 16 := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    congr 1
    push_cast
    ring
  have hX16 : (2 : Real) ^ 16 < X ^ 16 := pow_lt_pow_left₀ hlarge (by norm_num) (by norm_num)
  have hmle : (m : Real) ^ a ≤ m := by
    have h := Real.rpow_le_rpow_of_exponent_le hm1 ha1
    simpa using h
  have h8 : (8 : Real) ^ a ≤ 8 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 8) ha1
    simpa using h
  have h8pos : (0 : Real) < (8 : Real) ^ a := by positivity
  have hw : ((m : Real) / 8) ^ a = (m : Real) ^ a / (8 : Real) ^ a :=
    Real.div_rpow hm0.le (by norm_num) a
  have hwX : X ^ 16 / 8 ≤ ((m : Real) / 8) ^ a := by
    rw [hw, hma]
    exact div_le_div_of_nonneg_left (by positivity) h8pos h8
  refine ⟨?_, ?_, ?_⟩
  · have : (4 : Real) ≤ m := by nlinarith
    exact_mod_cast this
  · nlinarith
  · have hX2 : (2 : Real) < X := hlarge
    have hX14 : (128 : Real) ≤ X ^ 14 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hX2.le 14
      norm_num at h
      linarith
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 4)]
    apply Real.le_sqrt_of_sq_le
    have hsq : (X * 4) ^ 2 = 16 * X ^ 2 := by ring
    rw [hsq]
    have h16 : 16 * X ^ 2 ≤ X ^ 16 / 8 := by
      have hX2sq : 0 ≤ X ^ 2 := by positivity
      have : X ^ 16 = X ^ 14 * X ^ 2 := by ring
      rw [this]
      nlinarith
    linarith

/-- **An unused final coordinate, at every scale, for arbitrary controls.** -/
theorem MultiplyLinearWith.lift_last {N k : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hML : MultiplyLinearWith Qb Eb (partialGraph B phi))
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) (hk : 0 < k) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ (k + 1) : Nat) : Real)) (fun t => Eb t / 16)
      (partialGraph (lastProductSet B Finset.univ) (fun z => phi (section16Init z))) := by
  classical
  intro theta ht ht1 P hP
  obtain ⟨ha, ha1⟩ := hE theta ht ht1
  have hA : 0 < Eb theta / 16 := by positivity
  have hmass : (1 - theta) * (P.carrier.card : Real) ≤ P.carrier.card := by
    have hnonneg : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  have hgraph : ∀ z y, (z, y) ∈ partialGraph (lastProductSet B Finset.univ)
      (fun z => phi (section16Init z)) → y = phi (section16Init z) ∧ section16Init z ∈ B := by
    intro z y hz
    obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp hz
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hwy
    exact ⟨rfl, (Finset.mem_filter.mp hw).2.1⟩
  have h3 : (1 : Real) ≤ ((3 ^ (k + 1) : Nat) : Real) := by
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  by_cases hsmall : (P.width : Real) ^ (Eb theta / 16) ≤ 2
  · by_cases htwo : 2 ≤ P.width
    · obtain ⟨M, Q, mu, hpart, hproper, hmu, hc⟩ :=
        section16_coarse_function_cover P hP (by omega) htwo (fun z => phi (section16Init z))
      refine ⟨M, 3 ^ (k + 1), P.carrier, Q, mu, Finset.Subset.rfl, hmass, hpart,
        fun j => (hproper j).1, le_max_right _ _, ?_, hmu, ?_⟩
      · intro j
        exact hsmall.trans (by exact_mod_cast (hproper j).2)
      · intro j z hz _ y hy
        rw [(hgraph z y hy).1]
        exact hc j z hz
    · obtain ⟨M, Q, mu, hpart, hproper, hmu, hc⟩ :=
        section16_singleton_function_cover P (by omega) (fun z => phi (section16Init z))
      refine ⟨M, 1, P.carrier, Q, mu, Finset.Subset.rfl, hmass, hpart,
        fun j => (hproper j).1, ?_, ?_, hmu, ?_⟩
      · exact_mod_cast h3.trans (le_max_right _ _)
      · intro j
        rw [(hproper j).2, Nat.cast_one]
        exact Real.rpow_le_one (Nat.cast_nonneg _)
          (by exact_mod_cast (show P.width ≤ 1 by omega)) hA.le
      · intro j z hz _ y hy
        rw [(hgraph z y hy).1]
        exact hc j z hz
  · have hlarge : 2 < (P.width : Real) ^ (Eb theta / 16) := lt_of_not_ge hsmall
    obtain ⟨hm4, hw16, hwidth⟩ := with_lift_width_budget ha ha1 P.width hlarge
    obtain ⟨v, hv, hvfit, hvwidth⟩ := section16_lift_width_rounding hw16
    let T := boxInit P
    let I := P.axis (Fin.last k)
    have hI : I.IsProper := hP _
    have hmI : P.width ≤ I.length := P.width_le_axis_length _
    obtain ⟨u, hu⟩ := I.step_isUnit_of_prime hI (by omega)
    have hstep : I.step = T.commonDiff := P.axis_step _
    obtain ⟨q, G, M, Q, mu, hq, hG, hGm, hpart, hproper, hmu, hc⟩ :=
      hML.unused_coordinate_cover theta ht ht1 (hQ theta ht ht1) ha.le T I
        (boxInit_isProper P hP) hI hstep u hu.symm hk hm4 (boxInit_width P hk) hmI hv hvfit
    have hprod : lastProductSet T.carrier I.carrier = P.carrier :=
      (boxInit_last_product P).1.symm
    rw [hprod] at hG hGm hpart
    refine ⟨M, q, G, Q, mu, hG, hGm, hpart, fun j => (hproper j).1,
      hq.trans (le_max_left _ _), fun j => ?_, hmu, ?_⟩
    · exact hwidth.trans (hvwidth.trans (by exact_mod_cast (hproper j).2))
    · intro j z hz hzG y hy
      obtain ⟨hyval, hzB⟩ := hgraph z y hy
      rw [hyval]
      exact hc j z hz hzB hzG


theorem MultiplyLinearWith.coordinateReindex {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : MultiplyLinearWith Qb Eb Gamma) (e : Fin k ≃ Fin k) :
    MultiplyLinearWith Qb Eb
      (Gamma.image (fun z => (LeanProofs.GowersSzemeredi.coordinateReindex e z.1, z.2))) := by
  classical
  intro theta ht ht1 P hP
  obtain ⟨M, q, H, Q, mu, hH, hHcard, hpart, hproper, hq, hwidth, hmu, hcover⟩ :=
    h theta ht ht1 (P.coordinateReindex e.symm) (hP.coordinateReindex e.symm)
  refine ⟨M, q, H.image (LeanProofs.GowersSzemeredi.coordinateReindex e),
    fun j => (Q j).coordinateReindex e,
    fun j i x => mu j i (LeanProofs.GowersSzemeredi.coordinateReindex e.symm x),
    ?_, ?_, ?_, fun j => (hproper j).coordinateReindex e, hq, ?_,
    fun j i => (hmu j i).coordinateReindex e.symm, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hh := (Box.coordinateReindex_mem_carrier (P.coordinateReindex e.symm) e y).mpr (hH hy)
    simpa only [Box.coordinateReindex_symm'] using hh
  · rw [Finset.card_image_of_injective _ (LeanProofs.GowersSzemeredi.coordinateReindex e).injective]
    simpa using hHcard
  · simpa using hpart.coordinateReindex e
  · intro j
    simpa using hwidth j
  · intro j x hx hh y hxy
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hxy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have haQ := (Box.coordinateReindex_mem_carrier (Q j) e a).mp hx
    have haH := (LeanProofs.GowersSzemeredi.coordinateReindex e).injective.mem_finset_image.mp hh
    obtain ⟨i, hi⟩ := hcover j a haQ haH b hab
    exact ⟨i, by simpa using hi⟩

theorem MultiplyLinearWith.coordinateReindex_graph {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (h : MultiplyLinearWith Qb Eb (partialGraph B phi)) (e : Fin k ≃ Fin k) :
    MultiplyLinearWith Qb Eb
      (partialGraph (B.image (LeanProofs.GowersSzemeredi.coordinateReindex e))
        (fun x => phi (LeanProofs.GowersSzemeredi.coordinateReindex e.symm x))) := by
  classical
  have hh := MultiplyLinearWith.coordinateReindex h e
  have heq : (partialGraph B phi).image
      (fun z => (LeanProofs.GowersSzemeredi.coordinateReindex e z.1, z.2)) =
      partialGraph (B.image (LeanProofs.GowersSzemeredi.coordinateReindex e))
        (fun x => phi (LeanProofs.GowersSzemeredi.coordinateReindex e.symm x)) := by
    simp [partialGraph, Finset.image_image, Function.comp_def]
  rw [heq] at hh
  exact hh

/-- **Unused final coordinates, any number of them, for arbitrary controls.** -/
theorem MultiplyLinearWith.lift_prefix {N l d : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {B : Finset (Point N l)} {phi : Point N l → ZMod N}
    (hML : MultiplyLinearWith Qb Eb (partialGraph B phi))
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) (hl : 0 < l) (hld : l ≤ d) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ d : Nat) : Real))
      (fun t => Eb t / 16 ^ (d - l))
      (partialGraph (prefixDomain hld B) (fun z => phi (coordinatePrefix hld z))) := by
  classical
  induction d with
  | zero => omega
  | succ d ih =>
    by_cases heq : l = d + 1
    · subst heq
      have hB : prefixDomain hld B = B := by
        ext z
        simp
      simp only [hB, coordinatePrefix_self, Nat.sub_self, pow_zero, div_one]
      exact MultiplyLinearWith.weaken hML (fun s _ _ => le_max_left _ _) (fun s hs hs1 => (hE s hs hs1).1)
        (fun s _ _ => le_rfl)
    · have hld' : l ≤ d := by omega
      have hIH := ih hld'
      have hQ' : ∀ t, 0 < t → t ≤ 1 → 0 ≤ max (Qb t) ((3 ^ d : Nat) : Real) :=
        fun t _ _ => le_trans (Nat.cast_nonneg _) (le_max_right _ _)
      have hE' : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t / 16 ^ (d - l) ∧ Eb t / 16 ^ (d - l) ≤ 1 := by
        intro t ht ht1
        obtain ⟨h1, h2⟩ := hE t ht ht1
        refine ⟨by positivity, ?_⟩
        rw [div_le_one (by positivity)]
        exact h2.trans (one_le_pow₀ (by norm_num))
      have hp := hIH.lift_last hQ' hE' (by omega)
      have hdom : lastProductSet (prefixDomain hld' B) Finset.univ = prefixDomain hld B := by
        ext z
        simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and,
          and_true, mem_prefixDomain]
        rfl
      have hfun : (fun z : Point N (d + 1) => phi (coordinatePrefix hld' (section16Init z))) =
          fun z => phi (coordinatePrefix hld z) := by
        funext z
        rfl
      rw [hdom, hfun] at hp
      refine MultiplyLinearWith.weaken hp ?_ ?_ ?_
      · intro s _ _
        apply max_le (max_le (le_max_left _ _) ?_) (le_max_right _ _)
        exact le_trans (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d))
          (le_max_right _ _)
      · intro s hs hs1
        have := (hE s hs hs1).1
        positivity
      · intro s _ _
        rw [show d + 1 - l = d - l + 1 by omega, pow_succ, div_div]

/-- **Any embedded set of active coordinates, for arbitrary controls.** -/
theorem MultiplyLinearWith.lift_embedding {N l d : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {B : Finset (Point N l)} {phi : Point N l → ZMod N}
    (hML : MultiplyLinearWith Qb Eb (partialGraph B phi))
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) (hl : 0 < l) (f : Fin l ↪ Fin d) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ d : Nat) : Real))
      (fun t => Eb t / 16 ^ (d - l))
      (partialGraph (selectedDomain f B) (fun z => phi (selectedCoordinates f z))) := by
  classical
  have hld : l ≤ d := by simpa using Fintype.card_le_of_injective f f.injective
  obtain ⟨sigma, hsigma⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin l => i.castLE hld) f (Fin.castLE_injective hld) f.injective
  let e : Point N d ≃ Point N d := LeanProofs.GowersSzemeredi.coordinateReindex sigma.symm
  have hinv : ∀ z, coordinatePrefix hld (e.symm z) = selectedCoordinates f z := by
    intro z
    funext i
    exact congrArg z (hsigma i)
  have hp := (hML.lift_prefix hE hl hld).coordinateReindex_graph sigma.symm
  change MultiplyLinearWith _ _ (partialGraph ((prefixDomain hld B).image e)
    (fun z => phi (coordinatePrefix hld (e.symm z)))) at hp
  have hdom : (prefixDomain hld B).image e = selectedDomain f B := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      rw [mem_selectedDomain, ← hinv, e.symm_apply_apply]
      exact (mem_prefixDomain hld B w).mp hw
    · intro hz
      refine Finset.mem_image.mpr ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      rw [mem_prefixDomain, hinv]
      exact (mem_selectedDomain f B z).mp hz
  simpa only [hdom, hinv] using hp

end LeanProofs.GowersSzemeredi
