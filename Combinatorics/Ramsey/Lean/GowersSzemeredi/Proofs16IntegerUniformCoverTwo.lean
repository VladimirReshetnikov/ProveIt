import GowersSzemeredi.Proofs16IntegerClassPieceCover

/-! Dimension-two Freiman piece families have genuine integer covers.
The existing class data, counts, widths and decomposition are preserved. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

theorem RelFreimanCover.integer_cubic_cover {N q : Nat} [NeZero N] [Fact N.Prime]
    {R : Finset (Point N 1 × ZMod N)} (h : RelFreimanCover q R) (hq : 0 < q) :
    IntegerMultiplyLinearWith (fun _ => ((3 * q : Nat) : Real)) (cubicBaseExponent q) R := by
  obtain ⟨D, f, hf, hc⟩ := h
  exact section16_integer_freiman_family_cubic_cover hq D f hf R hc

theorem IntegerMultiplyLinearWith.last_cylinder {N : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Λ : Finset (Point N 1 × ZMod N)}
    (hML : IntegerMultiplyLinearWith Qb Eb Λ)
    (M : Nat) (hfib : ∀ x : Point N 1, (Λ.filter fun z => z.1 = x).card ≤ M)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Qb t)
    (hE : ∀ t, 0 < t → t ≤ 1 → 0 < Eb t ∧ Eb t ≤ 1) :
    IntegerMultiplyLinearWith (fun t => max (Qb t) ((3 ^ (1 + 1) * M : Nat) : Real))
      (fun t => Eb t / 16) (lastCylinder Λ) := by
  classical
  have h := hML.relation_lift_last M hfib hQ hE (by norm_num)
  have h2 := IntegerMultiplyLinearWith.coordinateReindex h (Equiv.swap 0 1)
  refine IntegerMultiplyLinearWith.mono h2 ?_
  intro z hz
  have hzΛ := mem_lastCylinder.mp hz
  refine Finset.mem_image.mpr ⟨(LeanProofs.GowersSzemeredi.coordinateReindex (Equiv.swap (0 : Fin 2) 1) z.1, z.2), ?_, ?_⟩
  · apply mem_lastLiftRelation.mpr
    have heq : section16Init (LeanProofs.GowersSzemeredi.coordinateReindex (Equiv.swap (0 : Fin 2) 1) z.1) = lastPt z.1 := by
      funext i
      fin_cases i
      rfl
    rw [heq]
    exact hzΛ
  · refine Prod.ext ?_ rfl
    funext i
    fin_cases i <;> rfl
theorem section16_integer_poly_family_two_cover
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : IntegerAbstractFamilyLemma166At 1 (section16PowerWidth A Bq))
    {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {mass : Real} {qs qr ql : Nat}
    {N : Nat} [NeZero N] [Fact N.Prime] {Gamma : Finset (Point N 2 × ZMod N)}
    {m : Nat} (P : Fin m → PolyPieceTwoData Gamma zeta mass qs qr ql) :
    IntegerMultiplyLinearWith
      (fun rho => max (famPieceGraphBound (famTwoQr m qr) (famTwoPb m ql) m rho)
        ((3 ^ (1 + 1) * m : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq (famTwoQb m qs) (famTwoEb m qs) (famTwoEr m qr) rho *
          famPieceSliceExponent (famTwoQr m qr) (famTwoEs m ql) m rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A (famTwoQb m qs) zeta rho)
          (pieceLineExponent Bq (famTwoQb m qs) (famTwoEb m qs) (famTwoEr m qr) rho)
          (famPieceSliceExponent (famTwoQr m qr) (famTwoEs m ql) m rho)))
      (Finset.univ.biUnion fun c => partialGraph (P c).D (P c).phi) := by
  classical
  -- spectra
  set Gspec := Finset.univ.biUnion fun c : Fin m =>
    ((P c).H1 ×ˢ (Finset.univ : Finset (ZMod N))).filter fun z => z.2 ∈ (P c).K z.1 with hGspec
  have hspec : RelFreimanCover (m * qs + 1) Gspec :=
    (relFreimanCover_union _ (fun c => (P c).spec)).pad (Nat.le_succ _)
  have hMLspec : IntegerMultiplyLinearWith (famTwoQb m qs) (famTwoEb m qs) Gspec :=
    hspec.integer_cubic_cover (Nat.succ_pos _)
  -- remainders
  set Λ := Finset.univ.biUnion fun c : Fin m =>
    (P c).D.image fun w => (lastPt w, (P c).rem w) with hΛ
  have hrem1 : RelFreimanCover (m * qr + 1) Λ :=
    (relFreimanCover_union _ (fun c => (P c).remc)).pad (Nat.le_succ _)
  have hMLrem := (hrem1.integer_cubic_cover (Nat.succ_pos _)).last_cylinder (m * qr + 1)
    hrem1.fiber_le (fun t _ _ => by positivity)
    (fun t ht ht1 => ⟨cubicBaseExponent_pos (Nat.succ_pos _) ht,
      cubicBaseExponent_le_one (Nat.succ_pos _) ht ht1⟩)
  have hMLrem' : IntegerMultiplyLinearWith (famTwoQr m qr) (famTwoEr m qr) (lastCylinder Λ) := hMLrem
  -- stacked slices
  let Gs : (r : Nat) → (Fin m → Fin r → ZMod N) → Finset (Point N 1 × ZMod N) :=
    fun r sample => Finset.univ.biUnion fun c =>
      section16StackedSlices (P c).D (P c).phi (sample c)
  have hslice : ∀ r sample, IntegerMultiplyLinearWith (famTwoPb m ql r) (famTwoEs m ql r) (Gs r sample) := by
    intro r sample
    have h := (relFreimanCover_union _ (fun c => stackedSlices_relFreimanCover (P c).slices
      (sample c))).pad (Nat.le_succ (m * (r * ql)))
    exact h.integer_cubic_cover (Nat.succ_pos _)
  have hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ (P c).D →
      (h, (P c).phi (appendCoordinate h (sample c i))) ∈ Gs r sample := by
    intro r sample c h i hi
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, section16StackedSlices_mem h i hi⟩
  have hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ famTwoQb m qs s ∧ 0 < famTwoEb m qs s ∧
      famTwoEb m qs s ≤ 1 := fun s hs hs1 =>
    ⟨Nat.cast_nonneg _, cubicBaseExponent_pos (Nat.succ_pos _) hs,
      cubicBaseExponent_le_one (Nat.succ_pos _) hs hs1⟩
  have hEr : ∀ s, 0 < s → s ≤ 1 → 0 < famTwoEr m qr s := by
    intro s hs _
    have := cubicBaseExponent_pos (Nat.succ_pos (m * qr)) hs
    simp only [famTwoEr]
    positivity
  have hcover := integer_abstract_family_piece_cover_with (k := 1) le_rfl hA hB hlemma6 hz hzHalf hQb hEr
    hMLspec hMLrem' (ι := Fin m) (H1 := fun c => (P c).H1) (K := fun c => (P c).K)
    (Adom := fun c => (P c).A) (f := fun c => (P c).f) (D := fun c => (P c).D)
    (phi := fun c => (P c).phi) (rem := fun c => (P c).rem)
    (fun c x hx r hr => Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, hr⟩⟩)
    (fun c => (P c).linear) (fun c => (P c).dom) (fun c => (P c).ident)
    (fun c z hz => mem_lastCylinder.mpr (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩))
    Gs hslice hGs (famTwo_slice_ranges m ql) (fun ε => famTwoPb_monotone m ql ε)
    (fun ε hε => famTwoEs_antitone m ql hε)
  simpa only [Fintype.card_fin] using hcover

theorem section16_integer_poly_piece_two_family_cover {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : IntegerAbstractFamilyLemma166At 1 (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {M : Nat} (P : Fin M → PolyPieceTwo N theta gamma) :
    IntegerMultiplyLinearWith (uniTwoCount theta gamma M) (uniTwoExp A Bq theta gamma M)
      (polyPieceTwoGraphs P) := by
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half 1 ht ht1 hg hg1
  exact section16_integer_poly_family_two_cover hA hB hlemma6 hz hzHalf P

/-- **The uniform family cover in dimension two.** A family of `n` relations,
each decomposed into `m` pieces of the class, has one cover of the union of
their restrictions, with the controls at `n·m` pieces. -/
theorem section16_integer_uniform_cover_two {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : IntegerAbstractFamilyLemma166At 1 (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {n m : Nat}
    (Gammas : Fin n → Finset (Point N 2 × ZMod N)) (J : Fin n → Finset (Point N 2))
    (P : Fin n → Fin m → PolyPieceTwo N theta gamma)
    (hcov : ∀ i, restrictRelation (Gammas i) (J i) ⊆ polyPieceTwoGraphs (P i)) :
    IntegerMultiplyLinearWith (uniTwoCount theta gamma (n * m)) (uniTwoExp A Bq theta gamma (n * m))
      (Finset.univ.biUnion fun i => restrictRelation (Gammas i) (J i)) := by
  classical
  let e : Fin (n * m) ≃ Fin n × Fin m := finProdFinEquiv.symm
  let R : Fin (n * m) → PolyPieceTwo N theta gamma := fun c => P (e c).1 (e c).2
  refine IntegerMultiplyLinearWith.mono
    (section16_integer_poly_piece_two_family_cover hA hB hlemma6 ht ht1 hg hg1 R) ?_
  intro z hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (hcov i hi)
  refine Finset.mem_biUnion.mpr ⟨e.symm (i, c), Finset.mem_univ _, ?_⟩
  simp only [R, Equiv.apply_symm_apply]
  exact hc

end LeanProofs.GowersSzemeredi
