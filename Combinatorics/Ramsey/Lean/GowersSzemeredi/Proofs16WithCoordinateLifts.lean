import GowersSzemeredi.Proofs16PolyBaseCase
import GowersSzemeredi.Proofs16EmbeddedLift
import GowersSzemeredi.Proofs16CubicCoverControls
import GowersSzemeredi.Proofs16UnusedCoordinateCover

/-! Coordinate lifts for covers with arbitrary controls (`MultiplyLinearWith`),
toward a polynomial-control `PolyCoverAt 2` (Notes L.3, step (A)).

The shared unused-coordinate cover in `Proofs16UnusedCoordinateCover`
provides synchronized retiling for arbitrary controls. This owner extends
that construction to all-scale lifts and reindexing for `MultiplyLinearWith Qb Eb`:
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

/-- The width budget of the all-scale lift: above the small-box branch the
retiled width dominates `m^(a/16)`. -/
theorem with_lift_width_budget {a : Real} (ha : 0 < a) (ha1 : a ≤ 1) (m : Nat)
    (hlarge : 2 < (m : Real) ^ (a / 16)) :
    4 ≤ m ∧ 16 ≤ ((m : Real) / 8) ^ a ∧
      (m : Real) ^ (a / 16) ≤ Real.sqrt (((m : Real) / 8) ^ a) / 4 := by
  have hm0 : (0 : Real) ≤ m := Nat.cast_nonneg m
  have hm1 : (1 : Real) ≤ m := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (by
    rintro rfl; norm_num [Real.zero_rpow (by positivity : a / 16 ≠ 0)] at hlarge))
  set X := (m : Real) ^ (a / 16) with hXdef
  have hma : (m : Real) ^ a = X ^ 16 := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hm0]; congr 1; push_cast; ring
  have hX16 : (2 : Real) ^ 16 < X ^ 16 := pow_lt_pow_left₀ hlarge (by norm_num) (by norm_num)
  have hX14 : (2 : Real) ^ 14 ≤ X ^ 14 := pow_le_pow_left₀ (by norm_num) hlarge.le 14
  have hmle : (m : Real) ^ a ≤ m := by simpa using Real.rpow_le_rpow_of_exponent_le hm1 ha1
  have h8 : (8 : Real) ^ a ≤ 8 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 8) ha1
  have hwX : X ^ 16 / 8 ≤ ((m : Real) / 8) ^ a := by
    rw [Real.div_rpow hm0 (by norm_num : (0 : Real) ≤ 8), hma]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h8
  refine ⟨by exact_mod_cast (show (4 : Real) ≤ m by linarith), by linarith, ?_⟩
  rw [le_div_iff₀ (by norm_num : (0 : Real) < 4)]
  apply Real.le_sqrt_of_sq_le
  nlinarith [mul_le_mul_of_nonneg_right hX14 (sq_nonneg X), sq_nonneg X]

/-- **An unused final coordinate, at every scale, for arbitrary controls.** -/
theorem MultiplyLinearWith.lift_last {N k : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hML : MultiplyLinearWith Qb Eb (partialGraph B phi))
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) (hk : 0 < k) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ (k + 1) : Nat) : Real)) (fun t => Eb t / 16)
      (partialGraph (lastProductSet B Finset.univ) (fun z => phi (section16Init z))) := by
  intro theta ht ht1 P hP
  obtain ⟨ha, ha1⟩ := hE theta ht ht1
  have hmass : (1 - theta) * (P.carrier.card : Real) ≤ P.carrier.card :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith)
  have hgraph : ∀ z y, (z, y) ∈ partialGraph (lastProductSet B Finset.univ)
      (fun z => phi (section16Init z)) → y = phi (section16Init z) ∧ section16Init z ∈ B := by
    intro z y hz
    obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp hz
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hwy
    exact ⟨rfl, (Finset.mem_filter.mp hw).2.1⟩
  by_cases hsmall : (P.width : Real) ^ (Eb theta / 16) ≤ 2
  · by_cases htwo : 2 ≤ P.width
    · obtain ⟨M, Q, mu, hpart, hproper, hmu, hc⟩ :=
        section16_coarse_function_cover P hP (by omega) htwo (fun z => phi (section16Init z))
      exact ⟨M, 3 ^ (k + 1), P.carrier, Q, mu, Finset.Subset.rfl, hmass, hpart,
        fun j => (hproper j).1, le_max_right _ _,
        fun j => hsmall.trans (by exact_mod_cast (hproper j).2), hmu,
        fun j z hz _ y hy => (hgraph z y hy).1 ▸ hc j z hz⟩
    · obtain ⟨M, Q, mu, hpart, hproper, hmu, hc⟩ :=
        section16_singleton_function_cover P (by omega) (fun z => phi (section16Init z))
      refine ⟨M, 1, P.carrier, Q, mu, Finset.Subset.rfl, hmass, hpart, fun j => (hproper j).1,
        le_max_of_le_right (Nat.cast_le.mpr (Nat.one_le_pow _ _ (by norm_num))), fun j => ?_,
        hmu, fun j z hz _ y hy => (hgraph z y hy).1 ▸ hc j z hz⟩
      rw [(hproper j).2, Nat.cast_one]
      exact Real.rpow_le_one (Nat.cast_nonneg _) (by exact_mod_cast (show P.width ≤ 1 by omega))
        (div_pos ha (by norm_num)).le
  · obtain ⟨hm4, hw16, hwidth⟩ := with_lift_width_budget ha ha1 P.width (not_le.mp hsmall)
    obtain ⟨v, hv, hvfit, hvwidth⟩ := section16_lift_width_rounding hw16
    have hmI := P.width_le_axis_length (Fin.last k)
    obtain ⟨u, hu⟩ := (P.axis (Fin.last k)).step_isUnit_of_prime (hP _) (by omega)
    obtain ⟨q, G, M, Q, mu, hq, hG, hGm, hpart, hproper, hmu, hc⟩ :=
      hML.unused_coordinate_cover theta ht ht1 (hQ theta ht ht1) ha.le (boxInit P)
        (P.axis (Fin.last k)) (boxInit_isProper P hP) (hP _) (P.axis_step _) u hu.symm hk hm4
        (boxInit_width P hk) hmI hv hvfit
    rw [show lastProductSet _ _ = P.carrier from (boxInit_last_product P).1.symm] at hG hGm hpart
    exact ⟨M, q, G, Q, mu, hG, hGm, hpart, fun j => (hproper j).1, hq.trans (le_max_left _ _),
      fun j => hwidth.trans (hvwidth.trans (by exact_mod_cast (hproper j).2)), hmu,
      fun j z hz hzG y hy => (hgraph z y hy).1 ▸ hc j z hz (hgraph z y hy).2 hzG⟩

theorem MultiplyLinearWith.coordinateReindex {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)}
    (h : MultiplyLinearWith Qb Eb Gamma) (e : Fin k ≃ Fin k) :
    MultiplyLinearWith Qb Eb
      (Gamma.image (fun z => (LeanProofs.GowersSzemeredi.coordinateReindex e z.1, z.2))) := by
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
  induction d with
  | zero => omega
  | succ d ih =>
    by_cases heq : l = d + 1
    · subst heq
      have hB : prefixDomain hld B = B := by ext; simp
      simp only [hB, coordinatePrefix_self, Nat.sub_self, pow_zero, div_one]
      exact hML.weaken (fun s _ _ => le_max_left _ _) (fun s hs hs1 => (hE s hs hs1).1)
        (fun s _ _ => le_rfl)
    · have hld' : l ≤ d := by omega
      have hE' : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t / 16 ^ (d - l) ∧ Eb t / 16 ^ (d - l) ≤ 1 := by
        intro t ht ht1
        obtain ⟨h1, h2⟩ := hE t ht ht1
        exact ⟨by positivity, (div_le_self h1.le (one_le_pow₀ (by norm_num))).trans h2⟩
      have hp := (ih hld').lift_last (fun t _ _ => le_max_of_le_right (Nat.cast_nonneg _)) hE'
        (by omega)
      have hdom : lastProductSet (prefixDomain hld' B) Finset.univ = prefixDomain hld B := by
        ext z; simp [lastProductSet]; rfl
      rw [hdom] at hp
      refine hp.weaken (fun s _ _ => ?_) (fun s hs hs1 => div_pos (hE s hs hs1).1 (by positivity))
        (fun s _ _ => by rw [show d + 1 - l = d - l + 1 by omega, pow_succ, div_div])
      exact max_le (max_le (le_max_left _ _) ((Nat.cast_le.mpr (Nat.pow_le_pow_right
        (by norm_num) (Nat.le_succ d))).trans (le_max_right _ _))) (le_max_right _ _)

/-- **Any embedded set of active coordinates, for arbitrary controls.** -/
theorem MultiplyLinearWith.lift_embedding {N l d : Nat} [NeZero N] [Fact N.Prime]
    {Qb Eb : Real → Real} {B : Finset (Point N l)} {phi : Point N l → ZMod N}
    (hML : MultiplyLinearWith Qb Eb (partialGraph B phi))
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) (hl : 0 < l) (f : Fin l ↪ Fin d) :
    MultiplyLinearWith (fun t => max (Qb t) ((3 ^ d : Nat) : Real))
      (fun t => Eb t / 16 ^ (d - l))
      (partialGraph (selectedDomain f B) (fun z => phi (selectedCoordinates f z))) := by
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
