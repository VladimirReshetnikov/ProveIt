import GowersSzemeredi.Proofs16LocalizedThreshold

/-! # Assembling the localized Section 16 product partition

The short-parent cover supplies a single good set and frequency count.
Each refined base cell is retiled with the original final axis, and the
resulting finite partitions are flattened without changing the target width.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Assemble the complete product partition at initial scales at least four.
The exponent range and the short-Bohr-progression linearity input are explicit
here so that the geometric construction can be reused with Section 16's
actual parameters. -/
theorem MultiplyLinear.product_linearity_large_m {N k m : Nat} [NeZero N]
    {delta t : Real} {Gamma : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinear delta t Gamma) (sigma theta gamma : Real)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ha : 0 < (multipleC (t⁻¹ * sigma) delta k) ^ t)
    (ha1 : (multipleC (t⁻¹ * sigma) delta k) ^ t ≤ 1)
    (P : Box N k) (I : ModAP N) (u : (ZMod N)ˣ)
    (hP : P.IsProper) (hI : I.IsProper) (hstep : I.step = P.commonDiff)
    (hu : I.step = (↑u : ZMod N)) (hk : 1 ≤ k)
    (hm : 4 ≤ m) (hmP : m ≤ P.width) (hmI : m ≤ I.length)
    (H : Finset (Point N k)) (K : Point N k → Finset (ZMod N))
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
    (hK : ∀ x ∈ H, ∀ r ∈ K x, (x, r) ∈ Gamma)
    (hlinear : ∀ x ∈ H, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K x) (section16Zeta theta gamma k / v) →
      LinearOn (J.carrier ∩ A x) (f x)) :
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ M : Nat,
      ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k, ∃ J : Fin M → ModAP N,
      (q : Real) ≤ (multipleQ (t⁻¹ * sigma) delta k) ^ t ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (section16Zeta theta gamma k / 2) *
        Real.sqrt ((m : Real) ^ ((multipleC (t⁻¹ * sigma) delta k) ^ t *
          section16RecurrenceExponent k q)) ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ G → x ∈ H → x ∈ (T j).carrier →
        LinearOn ((J j).carrier ∩ A x) (f x) := by
  classical
  obtain ⟨q, G, b, B, n, R, mu, hq, hGsub, hGmass, hBpart, hBproper,
      hBaxes, hBstep, hRpart, hRproper, hRwidth, hmu, hcover⟩ :=
    hML.short_parent_cover sigma hs hs1 P I hP hI (by omega) hm hmP hmI
  let a := (multipleC (t⁻¹ * sigma) delta k) ^ t
  let l := (section16Zeta theta gamma k / 2) *
    Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q))
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
    obtain ⟨_, hp, hthreshold, v, hv, hvwidth, hvscale, hvbudget⟩ :=
      section16_localized_parameters hk (by omega : 1 ≤ m) ht ht1 hg hg1 ha ha1 hlarge
    let p := Nat.floor (((m : Real) / 8) ^ a)
    let e := section5NatFlattenEquiv n
    let R' := boxFlatten n R
    have hR'part : IsBoxPartition R' P := boxFlatten_partition P B n R hBpart hRpart
    let i : Fin k := ⟨0, by omega⟩
    have hpR (j : Fin (∑ z, n z)) : p ≤ (R' j).width := by
      have hfloor : (p : Real) ≤ ((m : Real) / 8) ^ a := Nat.floor_le (by positivity)
      have h := hfloor.trans (hRwidth (e.symm j).1 (e.symm j).2)
      exact_mod_cast h
    have hne (j : Fin (∑ z, n z)) : (R' j).carrier.Nonempty := by
      apply Box.carrier_nonempty_of_axis_pos
      intro z
      exact hp.trans_le ((hpR j).trans ((R' j).width_le_axis_length z))
    have hsub (j : Fin (∑ z, n z)) :
        ((R' j).axis i).carrier ⊆ ((B (e.symm j).1).axis i).carrier :=
      (R' j).axis_carrier_subset_of_carrier_subset (B (e.symm j).1) (hne j)
        (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) i
    have hBunit (j : Fin (∑ z, n z)) : ((B (e.symm j).1).axis i).step = (↑u : ZMod N) := by
      rw [(B _).axis_step, hBstep, ← hstep, hu]
    have hIparallel (j : Fin (∑ z, n z)) : I.step = ((B (e.symm j).1).axis i).step := by
      rw [(B _).axis_step, hBstep, hstep]
    have hlocal (j : Fin (∑ z, n z)) :
        ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
          ∃ J : Fin M → ModAP N,
          IsPartition (fun z => (S z).carrier) (lastProductSet (R' j).carrier I.carrier) ∧
          (∀ z, (S z).IsProper ∧ v - 1 ≤ (S z).width) ∧
          (∀ z, IsLastCoordinateBoxProduct (S z) (T z) (J z)) ∧
          ∀ z x, x ∈ (T z).carrier → x ∈ G ∩ H → LinearOn ((J z).carrier ∩ A x) (f x) := by
      apply proper_retiled_product_linearity (R' j) ((B (e.symm j).1).axis i) I i u
        (hRproper _ _) hI (hBunit j) (hIparallel j) (hsub j)
        (hBaxes _ i).2.1 (hBaxes _ i).2.2 (mu (e.symm j).1 (e.symm j).2)
        (hmu _ _) hthreshold (hpR j) hv hvscale K (section16Zeta theta gamma k)
        (G ∩ H) A f ?_ ?_ hvbudget
      · intro x hx hxGH r hr
        exact hcover (e.symm j).1 (e.symm j).2 x hx (Finset.mem_inter.mp hxGH).1 r
          (hK x (Finset.mem_inter.mp hxGH).2 r hr)
      · intro x hxGH J hJ hd
        exact hlinear x (Finset.mem_inter.mp hxGH).2 v (by omega) J hJ hd
    choose L S T J hSpart hSproper hSproduct hSlin using hlocal
    let fidx := section5NatFlattenEquiv L
    refine ⟨q, G, ∑ j, L j, boxFlatten L S,
      (fun j => T (fidx.symm j).1 (fidx.symm j).2),
      (fun j => J (fidx.symm j).1 (fidx.symm j).2), hq, hGsub, hGmass,
      finsetPartition_flatten L (fun j => lastProductSet (R' j).carrier I.carrier)
        (lastProductSet P.carrier I.carrier) (fun j z => (S j z).carrier)
        (lastProductSet_partition _ _ _ hR'part) hSpart, ?_, ?_, ?_⟩
    · intro j
      exact ⟨(hSproper _ _).1, hvwidth.trans (by exact_mod_cast (hSproper (fidx.symm j).1 (fidx.symm j).2).2)⟩
    · intro j
      exact hSproduct _ _
    · intro j x hxG hxH hxT
      exact hSlin _ _ x hxT (Finset.mem_inter.mpr ⟨hxG, hxH⟩)

end LeanProofs.GowersSzemeredi
