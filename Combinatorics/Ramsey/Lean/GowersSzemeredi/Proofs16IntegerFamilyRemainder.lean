import GowersSzemeredi.Proofs16IntegerFamilyLemma6

/-! The family remainder step retains genuine integer boxes.
The common partition, graph count, good-set mass and width transfer are
unchanged. Both relation-cover inputs are explicit induction hypotheses. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem Box.IsAscendingInteger.axis_hasIntegerRepresentatives {N k : Nat} [NeZero N]
    {P : Box N k} (hP : P.IsAscendingInteger) (i : Fin k) :
    (P.axis i).HasIntegerRepresentatives := by
  obtain ⟨d, A, hd, hcommon, hA⟩ := hP
  rw [← (hA i).2.2.2]
  exact (A i).toModAP_hasIntegerRepresentatives (hA i).1 (hA i).2.2.1

def IntegerSection16LineCoverFamily {N k : Nat} [NeZero N] {ι : Type}
    (P : Box N (k + 1)) (B1 : ι → Finset (Point N (k + 1)))
    (phi1 : ι → Point N (k + 1) → ZMod N)
    (sigma l : Real) (q : Nat) : Prop :=
  ∃ E : Finset (Point N (k + 1)), ∃ M : Nat,
    ∃ S : Fin M → Box N (k + 1),
      ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
        ∃ ell : ι → Fin M → Point N k → Fin q → ZMod N → ZMod N,
          E ⊆ P.carrier ∧ (1 - sigma) * P.carrier.card ≤ E.card ∧
          IsBoxPartition S P ∧ (∀ u, (S u).IsAscendingInteger) ∧
          (∀ u, (T u).IsAscendingInteger) ∧ (∀ u, (A u).HasIntegerRepresentatives) ∧
          (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
          (∀ u, l ≤ (S u).width) ∧
          (∀ a u h i, LinearOn Finset.univ (ell a u h i)) ∧
          ∀ a u h x, h ∈ (T u).carrier →
            appendCoordinate h x ∈ B1 a → appendCoordinate h x ∈ E →
            appendCoordinate h x ∈ (S u).carrier →
            ∃ i, phi1 a (appendCoordinate h x) = ell a u h i x

/-- **Lemma 16.9 for abstract members.** -/
def IntegerAbstractFamilyLemma169At (k : Nat) (W : Nat → Nat → Real → Real → Real) : Prop :=
  ∀ (N m : Nat) [NeZero N], 1 ≤ k →
    ∀ (zeta sigma : Real), 0 < zeta → zeta ≤ 1 / 2 → 0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb Qr Er : Real → Real), 0 ≤ Qb (sigma / 2) → 0 < Eb (sigma / 2) →
      Eb (sigma / 2) ≤ 1 → 0 ≤ Er (sigma / 2) →
    ∀ (Gamma : Finset (Point N k × ZMod N)), IntegerMultiplyLinearWith Qb Eb Gamma →
    ∀ (Gr : Finset (Point N (k + 1) × ZMod N)), IntegerMultiplyLinearWith Qr Er Gr →
    ∀ (ι : Type) (H1 : ι → Finset (Point N k)) (K A : ι → Point N k → Finset (ZMod N))
      (f : ι → Point N k → ZMod N → ZMod N) (D : ι → Finset (Point N (k + 1)))
      (phi rem : ι → Point N (k + 1) → ZMod N),
    (∀ c, ∀ x ∈ H1 c, ∀ r ∈ K c x, (x, r) ∈ Gamma) →
    (∀ c, ∀ x ∈ H1 c, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K c x) (zeta / v) → LinearOn (J.carrier ∩ A c x) (f c x)) →
    (∀ c, ∀ z ∈ D c, section16Init z ∈ H1 c ∧ section16Last z ∈ A c (section16Init z)) →
    (∀ c, ∀ z ∈ D c,
      phi c z = (-1 : ZMod N) ^ k * f c (section16Init z) (section16Last z) + rem c z) →
    (∀ c, ∀ z ∈ D c, (z, rem c z) ∈ Gr) →
    ∀ P : Box N (k + 1), P.HasIntegerRepresentatives → m ≤ P.width →
      ∃ qGamma : Nat,
        (qGamma : Real) ≤ Qr (sigma / 2) ∧
        IntegerSection16LineCoverFamily P D phi sigma
          (W m (Nat.floor (Qb (sigma / 2))) (Er (sigma / 2) * Eb (sigma / 2)) zeta) qGamma

/-- The abstract family Lemma 16.9 from the abstract family Lemma 16.6. -/
theorem integerAbstractFamilyLemma169At_of (k : Nat) {W : Nat → Nat → Real → Real → Real}
    (hW : Section16WidthTransfer W)
    (hlemma6 : IntegerAbstractFamilyLemma166At k W) : IntegerAbstractFamilyLemma169At k W := by
  unfold IntegerAbstractFamilyLemma169At
  intro N m _ hk zeta sigma hz hzHalf hs hs1 Qb Eb Qr Er hQ ha ha1 hEr
    Gamma hML Gr hrem ι H1 K A f D phi rem hfreq hlinear hdom hid hGr P hP hmP
  classical
  have hsHalf : 0 < sigma / 2 := by positivity
  have hsHalf1 : sigma / 2 ≤ 1 := by linarith
  obtain ⟨M, qGamma, F, R, mu, hFsub, hFmass, hRpart, hRproper, hqGamma,
      hRwidth, hmu, hremCover⟩ := hrem (sigma / 2) hsHalf hsHalf1 P hP
  have hlocal (j : Fin M) := hlemma6 N (R j).width hk zeta (sigma / 2) hz hzHalf
    hsHalf hsHalf1 Qb Eb hQ ha ha1 Gamma hML ι H1 K A f hfreq hlinear
    (R j) (boxInit (R j)) ((R j).axis (Fin.last k)) (hRproper j).toGenuine (boxInit_last_product (R j)) le_rfl
  choose G L S T J hGsub hGmass hSpart hSproper hSproduct hSwidth hSlin using hlocal
  let qDelta := Nat.floor (Qb (sigma / 2))
  have hwidth (j : Fin M) (a : Fin (L j)) :
      W m qDelta (Er (sigma / 2) * Eb (sigma / 2)) zeta ≤ (S j a).width := by
    have hcell : (m : Real) ^ (Er (sigma / 2)) ≤ (R j).width :=
      (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmP) hEr).trans (hRwidth j)
    exact (hW m (R j).width qDelta (Eb (sigma / 2)) (Er (sigma / 2)) zeta hz.le ha.le hEr
      hcell).trans (hSwidth j a)
  let U (j : Fin M) := lastProductSet (G j) ((R j).axis (Fin.last k)).carrier
  have hU (j : Fin M) : U j ⊆ (R j).carrier ∧
      (1 - sigma / 2) * ((R j).carrier.card : Real) ≤ (U j).card := by
    have h := lastProductSet_good_mass (boxInit (R j)).carrier (G j)
      ((R j).axis (Fin.last k)).carrier (sigma / 2) (hGsub j) (hGmass j)
    simpa only [U, (boxInit_last_product (R j)).1, lastProductSet] using h
  let V := Finset.univ.biUnion U
  have hV := IsPartition.good_union hRpart U (sigma / 2) (fun j => (hU j).1) (fun j => (hU j).2)
  let E := F ∩ V
  have hEsub : E ⊆ P.carrier := Finset.Subset.trans Finset.inter_subset_left hFsub
  have hEmass : (1 - sigma) * (P.carrier.card : Real) ≤ E.card := by
    have h := good_intersection_mass P.carrier F V (sigma / 2) (sigma / 2) hFsub hV.1 hFmass hV.2
    convert h using 1; ring
  have hext (c : ι) (j : Fin M) (a : Fin (L j)) (h : Point N k) :
      ∃ ell : ZMod N → ZMod N, LinearOn Finset.univ ell ∧
        (h ∈ G j ∧ h ∈ H1 c ∧ h ∈ (T j a).carrier →
          ∀ x ∈ (J j a).carrier ∩ A c h, f c h x = ell x) :=
    conditional_affine_extension _ _ _ (fun hh => hSlin j c a h hh.1 hh.2.1 hh.2.2)
  choose ell hell hellEq using hext
  let e := section5NatFlattenEquiv L
  let lines (c : ι) (j : Fin M) (a : Fin (L j)) (h : Point N k) (i : Fin qGamma) (x : ZMod N) :=
    (-1 : ZMod N) ^ k * ell c j a h x + mu j i (appendCoordinate h x)
  refine ⟨qGamma, hqGamma, E, ∑ j, L j, boxFlatten L S,
    (fun a => boxInit (boxFlatten L S a)),
    (fun a => (boxFlatten L S a).axis (Fin.last k)),
    (fun c a => lines c (e.symm a).1 (e.symm a).2), hEsub, hEmass,
    boxFlatten_partition P R L S hRpart hSpart, (fun a => hSproper _ _),
    (fun a => boxInit_isAscendingInteger _ (hSproper _ _)),
    (fun a => (hSproper _ _).axis_hasIntegerRepresentatives (Fin.last k)), ?_, ?_, ?_, ?_⟩
  · intro a
    exact boxInit_last_product _
  · intro a
    exact hwidth _ _
  · intro c a h i
    exact affine_plus_multilinear_fibres (mu (e.symm a).1) (hmu (e.symm a).1) h
      (ell c (e.symm a).1 (e.symm a).2 h) (hell _ _ _ _) ((-1 : ZMod N) ^ k) i
  · intro c a h x hhT hzD hzE hzS
    let j := (e.symm a).1
    let b := (e.symm a).2
    change appendCoordinate h x ∈ (S j b).carrier at hzS
    have hzR : appendCoordinate h x ∈ (R j).carrier := IsPartition.cell_subset (hSpart j) b hzS
    have hzF : appendCoordinate h x ∈ F := (Finset.mem_inter.mp hzE).1
    have hzV : appendCoordinate h x ∈ V := (Finset.mem_inter.mp hzE).2
    have hzU := (IsPartition.good_union_mem_iff hRpart U (fun j => (hU j).1) j hzR).mp hzV
    have hhG : h ∈ G j := by
      have h := (Finset.mem_filter.mp hzU).2.1
      simpa only [section16Init_appendCoordinate] using h
    have hdomain := hdom c _ hzD
    simp only [section16Init_appendCoordinate, section16Last_appendCoordinate] at hdomain
    have hxJ : x ∈ (J j b).carrier := by
      have h := ((hSproduct j b).mem_snoc h x).mp (by simpa only [appendCoordinate_eq_snoc] using hzS)
      exact h.2
    have hhTold : h ∈ (T j b).carrier :=
      (((hSproduct j b).mem_snoc h x).mp (by simpa only [appendCoordinate_eq_snoc] using hzS)).1
    have hphi := hellEq c j b h ⟨hhG, hdomain.1, hhTold⟩ x (Finset.mem_inter.mpr ⟨hxJ, hdomain.2⟩)
    obtain ⟨i, hi⟩ := hremCover j (appendCoordinate h x) hzR hzF _ (hGr c _ hzD)
    refine ⟨i, ?_⟩
    have hidz := hid c _ hzD
    simp only [section16Init_appendCoordinate, section16Last_appendCoordinate] at hidz
    change _ = lines c j b h i x
    dsimp only [lines]
    rw [hidz, hphi, hi]



theorem integerAbstractFamilyLemma169At_explicit (k : Nat) :
    IntegerAbstractFamilyLemma169At k
      (section16PowerWidth
        (familyWidthPrefactor (Nat.ceil (multiaffinePartitionK (k + 1) (2 ^ (k + 1)))))
        (familyWidthDivisor k ((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1))))) := by
  have hK := two_le_multiaffinePartitionK (k + 1) (2 ^ (k + 1))
  have hceil : 0 < Nat.ceil (multiaffinePartitionK (k + 1) (2 ^ (k + 1))) := by
    apply Nat.ceil_pos.mpr
    exact (by norm_num : (0 : Real) < 2).trans_le hK
  have hp : 0 < (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)) :=
    Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _)
  apply integerAbstractFamilyLemma169At_of k
    (section16PowerWidth_transfer (fun q => by unfold familyWidthPrefactor; positivity)
      (fun q => by unfold familyWidthDivisor; positivity))
  exact integerAbstractFamilyLemma166At_explicit k

end LeanProofs.GowersSzemeredi
