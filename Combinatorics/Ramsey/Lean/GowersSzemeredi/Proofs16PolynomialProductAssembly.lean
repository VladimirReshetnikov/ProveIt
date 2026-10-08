import GowersSzemeredi.Proofs16PolynomialRetiledLinearity
import GowersSzemeredi.Proofs16WithLemma6

/-! Polynomial recurrence applied to a controlled spectrum cover.

The short-parent construction gives spectrum-cover boxes of width at least
`(m/8)^(Eb sigma)`. Any positive integer `n` below this width and above the
new recurrence threshold supplies a product partition of minimum width
`(zeta/2)*sqrt(n^epsilon(q))`. The good base set loses at most `sigma` of
the mass, and the actual graph count remains bounded by `Qb sigma`.

The threshold is tested at `floor (Qb sigma)`, so it is independent of the
particular cover returned by MultiplyLinearWith. No spectrum structure or
local Bohr linearity premise is discharged by this assembly result.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The simultaneous recurrence threshold is nondecreasing in family size. -/
theorem section16SimultaneousThreshold_mono_count {k K p q r : Nat}
    (hK : 1 ≤ K) (hqr : q ≤ r) :
    section16SimultaneousThreshold k K p q ≤ section16SimultaneousThreshold k K p r := by
  unfold section16SimultaneousThreshold
  have hbase : K * (q + 1) ≤ K * (r + 1) := Nat.mul_le_mul_left K (by omega)
  have hexp : 2 * (p * (q + 1) ^ (2 * 2 ^ (k + 1))) ≤
      2 * (p * (r + 1) ^ (2 * 2 ^ (k + 1))) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left p (Nat.pow_le_pow_left (by omega) _))
  exact (Nat.pow_le_pow_left hbase _).trans
    (Nat.pow_le_pow_right (Nat.mul_pos (by omega) (by omega)) hexp)

/-- The improved recurrence propagates through the localized spectrum
cover and product assembly, with an explicit input-scale condition. -/
theorem exists_polynomial_spectrum_product_linearity (k : Nat) :
    ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
    ∀ (N m n : Nat) [NeZero N] (Qb Eb : Real → Real)
      (Gamma : Finset (Point N k × ZMod N)),
    MultiplyLinearWith Qb Eb Gamma →
    ∀ sigma zeta : Real, 0 < sigma → sigma ≤ 1 → 0 < zeta → zeta ≤ 1 / 2 →
    0 ≤ Qb sigma → 0 ≤ Eb sigma →
    ∀ (P : Box N k) (I : ModAP N) (u : (ZMod N)ˣ),
    P.IsProper → I.IsProper → I.step = P.commonDiff → I.step = (↑u : ZMod N) →
    1 ≤ k → 4 ≤ m → m ≤ P.width → m ≤ I.length →
    0 < n → (n : Real) ≤ ((m : Real) / 8) ^ (Eb sigma) →
    section16SimultaneousThreshold k C p (Nat.floor (Qb sigma)) ≤ n →
    ∀ (H : Finset (Point N k)) (K : Point N k → Finset (ZMod N))
      (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N),
    (∀ x ∈ H, ∀ r ∈ K x, (x, r) ∈ Gamma) →
    (∀ x ∈ H, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K x) (zeta / v) → LinearOn (J.carrier ∩ A x) (f x)) →
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ M : Nat,
      ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k, ∃ J : Fin M → ModAP N,
      (q : Real) ≤ Qb sigma ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (zeta / 2) *
        Real.sqrt ((n : Real) ^ section16SimultaneousExponent k p q) ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ G → x ∈ H → x ∈ (T j).carrier →
        LinearOn ((J j).carrier ∩ A x) (f x) := by
  classical
  obtain ⟨C, p, hC, hp, hprofile⟩ := exists_polynomial_retiled_linearity_profile k
  refine ⟨C, p, hC, hp, ?_⟩
  intro N m n _ Qb Eb Gamma hML sigma zeta hs hs1 hz hzHalf hQ ha P I u
    hP hI hstep hu hk hm hmP hmI hn hnscale hnthreshold H K A f hK hlinear
  obtain ⟨q, G, b, B, c, R, mu, hq, hGsub, hGmass, hBpart, hBproper,
      hBaxes, hBstep, hRpart, hRproper, hRwidth, hmu, hcover⟩ :=
    hML.short_parent_cover sigma hs hs1 hQ ha P I hP hI (by omega) hm hmP hmI
  let l := (zeta / 2) * Real.sqrt ((n : Real) ^ section16SimultaneousExponent k p q)
  by_cases hl : l ≤ 1
  · obtain ⟨M, S, hpart, hproper, hwidth, hlin⟩ :=
      section16_local_linearity_singletons (boxAppend P I hstep) l hl A f
    refine ⟨q, G, M, S, fun j => boxInit (S j), fun j => (S j).axis (Fin.last k),
      hq, hGsub, hGmass, ?_, fun j => ⟨hproper j, hwidth j⟩,
      fun j => boxInit_last_product (S j), ?_⟩
    · change IsPartition (fun j => (S j).carrier) _ at hpart ⊢
      simpa only [(boxAppend_product P I hstep).1, lastProductSet] using hpart
    · intro j x _ _ _
      simpa only [Finset.filter_mem_eq_inter] using hlin j x
  · have hlarge : 1 < l := lt_of_not_ge hl
    have hthreshold : section16SimultaneousThreshold k C p q ≤ n :=
      (section16SimultaneousThreshold_mono_count (by omega : 1 ≤ C) (Nat.le_floor hq)).trans hnthreshold
    let e := section5NatFlattenEquiv c
    let R' := boxFlatten c R
    have hR'part : IsBoxPartition R' P := boxFlatten_partition P B c R hBpart hRpart
    let i : Fin k := ⟨0, by omega⟩
    have hnR (j : Fin (∑ z, c z)) : n ≤ (R' j).width := by
      exact_mod_cast hnscale.trans (hRwidth (e.symm j).1 (e.symm j).2)
    have hne (j : Fin (∑ z, c z)) : (R' j).carrier.Nonempty := by
      apply Box.carrier_nonempty_of_axis_pos
      intro z
      exact hn.trans_le ((hnR j).trans ((R' j).width_le_axis_length z))
    have hsub (j : Fin (∑ z, c z)) :
        ((R' j).axis i).carrier ⊆ ((B (e.symm j).1).axis i).carrier :=
      (R' j).axis_carrier_subset_of_carrier_subset (B (e.symm j).1) (hne j)
        (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) i
    have hBunit (j : Fin (∑ z, c z)) : ((B (e.symm j).1).axis i).step = (↑u : ZMod N) := by
      rw [(B _).axis_step, hBstep, ← hstep, hu]
    have hIparallel (j : Fin (∑ z, c z)) : I.step = ((B (e.symm j).1).axis i).step := by
      rw [(B _).axis_step, hBstep, hstep]
    have hlocal (j : Fin (∑ z, c z)) :
        ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
          ∃ J : Fin M → ModAP N,
          IsPartition (fun z => (S z).carrier) (lastProductSet (R' j).carrier I.carrier) ∧
          (∀ z, (S z).IsProper ∧ l ≤ (S z).width) ∧
          (∀ z, IsLastCoordinateBoxProduct (S z) (T z) (J z)) ∧
          ∀ z x, x ∈ (T z).carrier → x ∈ G ∩ H → LinearOn ((J z).carrier ∩ A x) (f x) := by
      apply hprofile q N n (R' j) ((B (e.symm j).1).axis i) I i u
        (hRproper _ _) hI (hBunit j) (hIparallel j) (hsub j)
        (hBaxes _ i).2.1 (hBaxes _ i).2.2 (mu (e.symm j).1 (e.symm j).2)
        (hmu _ _) hthreshold (hnR j) K (G ∩ H) A f zeta hz hzHalf
      · intro x hx hxGH r hr
        exact hcover (e.symm j).1 (e.symm j).2 x hx (Finset.mem_inter.mp hxGH).1 r
          (hK x (Finset.mem_inter.mp hxGH).2 r hr)
      · intro x hxGH v hv J hJ hd
        exact hlinear x (Finset.mem_inter.mp hxGH).2 v hv J hJ hd
      · exact hlarge
    choose L S T J hSpart hSproper hSproduct hSlin using hlocal
    let fidx := section5NatFlattenEquiv L
    refine ⟨q, G, ∑ j, L j, boxFlatten L S,
      (fun j => T (fidx.symm j).1 (fidx.symm j).2),
      (fun j => J (fidx.symm j).1 (fidx.symm j).2), hq, hGsub, hGmass,
      finsetPartition_flatten L (fun j => lastProductSet (R' j).carrier I.carrier)
        (lastProductSet P.carrier I.carrier) (fun j z => (S j z).carrier)
        (lastProductSet_partition _ _ _ hR'part) hSpart, ?_, ?_, ?_⟩
    · intro j
      exact hSproper _ _
    · intro j
      exact hSproduct _ _
    · intro j x hxG hxH hxT
      exact hSlin _ _ x hxT (Finset.mem_inter.mpr ⟨hxG, hxH⟩)

end LeanProofs.GowersSzemeredi
