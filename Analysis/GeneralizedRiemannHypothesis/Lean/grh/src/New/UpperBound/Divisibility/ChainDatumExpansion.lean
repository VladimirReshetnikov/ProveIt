import New.UpperBound.Divisibility.ChainValuation

/-!
# Two invariant sums of translates attached to a chain datum

A chain datum `Ψ` has a plain tensor `φ♭` and a glued tensor `Glue φ♭`, and the latter is jointly
invariant. Expanding the gluing writes `Glue φ♭` as a double sum of translates of the vacuum
(`IsChainDatum.gluedTensor_eq_sum_translates`), and collecting its terms gives a weak chain datum
(`IsChainDatum.exists_isWeakChainDatum_compositeLift_eq`); this serves for sums of norms and for the
primes `p ≠ N`. The projection on vacua above `N` takes `Glue φ♭` to `φ♭`, so `φ♭` is jointly
invariant too (`IsChainDatum.isWeakChainDatum`); this serves for `p = N`.

Notions from other files:
* `D : Data P`: a CM field `E` with `f` infinite places, spaces `X_0, …, X_m` over it in a chain of
  `m` theta lifts, `X_j` of rank `n_j`, and a prime level `N = π π̄` with `π = D.piN`.
* `D.piNPlaces`: the places `w ∣ π`.
* `D.X j = D.InitIndex j ⊕ Unit`: the basis indices of `X_j`; the last one is the `Unit` summand.
* A tuple of translations `t`: a finite adelic matrix `t j` for each `j`, with rows indexed by
  `X_{j+1}` and columns by `X_j`. It is admissible for `q` if each `t j`, times the conjugate of
  `D.piM`, is integral at the places prime to `q`.
* `D.translateDatum t j`: the integral vacuum of `Hom(X_j, X_{j+1})` translated by the matrix `t j`.
* `D.gluedDoubleLiftDatum v i`: the gluing, the sum over `y` modulo `N` of the translates of
  `v (2 i) ⊗ v (2 i + 1)` by the last column `-y / N` and the last row `-ȳ / N`.
* `plainTensor Ψ`, `gluedTensor Ψ`: the tensors `φ♭ = ∑ x, Ψ x • ⊗ⱼ translateDatum x j` and
  `Glue φ♭`.
* `IsAdmissibleCombination v A q d p B z`: `z = ∑ x, r x • v x` with `r` supported in `A`, each
  `d * r x` integral away from `q` and, if `p` holds, all conjugates of `r` of `ℓ¹`-norm at most
  `B`.
* `IsChainDatum ϑ Ψ`, `IsWeakChainDatum ϑ Ψ`: admissible coefficients whose glued, respectively
  plain, tensor is jointly invariant under the levels `D.levelX j`; the conditions on support and
  sum of norms are weaker for a weak chain datum.

## Relation to the literature

See `New.UpperBound.Divisibility.LocalDivisibility` for related work.
-/

namespace New.Data

open TensorProduct Seesaw Space TensorChain

variable {P : Parameters} (D : Data P)

variable {D} in
/-- A place `w` above the level `N` does not divide `ϑ.normQ`, the product of the norms of the
places in the finite set `ϑ.Q` of the tame character `ϑ`. -/
lemma TameChar.normQ_notMem_of_N_mem (ϑ : D.TameChar) {w : FinPlace D.E}
    (hw : ↑D.N ∈ w.asIdeal) : ↑ϑ.normQ ∉ w.asIdeal :=
  w.isPrime.notMem_of_isCoprime_of_mem ϑ.coprime.coprime_mul_left.cast hw

/-- Let `ϑ` be a tame character and `ϑ.normQ = q` the product of the norms of the places in its
finite set `ϑ.Q`. Let the tuple of translations `t` be admissible for `q`: each matrix `t j`, times
the conjugate of `D.piM`, is integral at the places prime to `q`. Then the projection on the vacuum
at the places of `D.piNPlaces` and their conjugates fixes the translate `D.translateDatum t j` of
the integral vacuum by `t j`. -/
lemma vacuumProjFinPart_translateDatum (ϑ : D.TameChar) {t : D.Translations}
    (ht : t ∈ D.admissibleTranslations ϑ.normQ) (j : ℕ) :
    vacuumProjFinPart (D.homX j) D.piNPlaces (D.translateDatum t j) = D.translateDatum t j := by
  -- `t j` is integral above `N`: these places are not chosen and do not divide the modulus.
  refine Subtype.ext (D.projOn_translateDatum
    (D.mem_integralAfter_of_mem_admissibleTranslations ht fun w hw ↦ ?_))
  have hN : ↑D.N ∈ w.asIdeal := by simpa [D.isSplitLevel_piNPlaces.natCast_mem_iff] using hw
  exact ⟨ϑ.normQ_notMem_of_N_mem hN, .inr (D.not_isChosen_of_N_mem hN).right⟩

/-- Let `y` be a vector on `X_{j+1}` of classes modulo `N` at each `w ∣ π`, and suppose that the
adelic matrix `poleColumn`, with last column `-y / N` at these places and all other entries `0`, is
integral at these places and their conjugates. Then `y = 0`. -/
lemma eq_zero_of_poleColumn_mem_integralBox {j : ℕ} {y : D.X (j + 1) → D.piNPlaces → ZMod D.N}
    (hy : poleColumn (D.InitIndex j) y ∈
      integralBox (D.X (j + 1) × D.X j) (D.piNPlaces : Set (FinPlace D.E)).conjClosure) :
    y = 0 := by
  funext k
  rw [Pi.zero_apply, ← D.isSplitLevel_piNPlaces.reduction.map_zero, eq_comm,
    D.isSplitLevel_piNPlaces.reduction_eq_iff]
  intro w
  have h_entry : Valued.v (poleColumn (D.InitIndex j) y (k, Sum.inr ()) w) ≤ 1 :=
    idem_mul_mem_Ô.1 (mem_integralBox.1 hy (k, Sum.inr ())) w (.inl w.2)
  simpa [poleColumn] using h_entry

/-- Let `t` be a tuple of translations that is admissible for `ϑ.normQ`, the product of the norms of
the places in the set of the tame character `ϑ`. Gluing the `i`-th double lift means summing, over
the vectors `y` on `X_{2i+1}` of classes modulo `N` at each place `w ∣ π`, the translates of
`translateDatum t (2 i) ⊗ translateDatum t (2 i + 1)` by the last column `-y / N` and the last row
`-ȳ / N`. The projection on the vacuum at the places above `N`, applied to both factors of this sum
`D.gluedDoubleLiftDatum`, keeps only the term `y = 0`, so it undoes the gluing. -/
lemma vacuumProjFinPart_gluedDoubleLiftDatum (ϑ : D.TameChar) {t : D.Translations}
    (ht : t ∈ D.admissibleTranslations ϑ.normQ) (i : ℕ) :
    map (vacuumProjFinPart (D.homX (2 * i)) D.piNPlaces)
      (vacuumProjFinPart (D.homX (2 * i + 1)) D.piNPlaces)
        (D.gluedDoubleLiftDatum (D.translateDatum t) i) =
      D.translateDatum t (2 * i) ⊗ₜ D.translateDatum t (2 * i + 1) := by
  classical
  -- The projection keeps a further translate by `y` if `y` is integral above `N`, else kills it.
  have h_proj (j : ℕ) (y : D.X (j + 1) × D.X j → 𝔸f D.E) :
      vacuumProjFinPart (D.homX j) D.piNPlaces
        (heisenbergFinPart (D.homX j) y (D.translateDatum t j)) =
        boxIndicator (D.X (j + 1) × D.X j) (D.piNPlaces : Set (FinPlace D.E)).conjClosure y •
          heisenbergFinPart (D.homX j) y (D.translateDatum t j) :=
    Subtype.ext (projOn_finHeisenbergOp _
      (Subtype.ext_iff.1 (D.vacuumProjFinPart_translateDatum ϑ ht j)) y)
  simp only [gluedDoubleLiftDatum, doubleLiftGluing, LinearMap.sum_apply, map_sum, map_tmul, h_proj]
  rw [Fintype.sum_eq_single 0]
  · unfold poleColumn poleRow
    simp [← Pi.zero_def, residueOverN, heisenbergFinPart, LinearMap.restrict_apply,
      finHeisenbergOp, stdLattice.semichar]
  · exact fun y hy ↦ by simp [mt D.eq_zero_of_poleColumn_mem_integralBox hy]

/-- Let the tuple of translations `t` vanish at the places above `N` and let the matrix `z` vanish
at all other places, that is, outside `D.piNPlaces` and its conjugate. Then translating the integral
vacuum by `t j` and then by `z` is translating it by `z + t j`: as the supports are disjoint, there
is no phase. -/
lemma heisenbergFinPart_translateDatum_of_disjoint {t : D.Translations}
    (ht : ∀ (j : ℕ) (k : D.X (j + 1) × D.X j) (w : FinPlace D.E), ↑D.N ∈ w.asIdeal → t j k w = 0)
    (j : ℕ) (z : D.X (j + 1) × D.X j → 𝔸f D.E)
    (hz : ∀ (k : D.X (j + 1) × D.X j) (w : FinPlace D.E),
      w ∉ D.piNPlaces → star w ∉ D.piNPlaces → z k w = 0) :
    (D.homX j).heisenbergFinPart z (D.translateDatum t j) =
      (D.homX j).heisenbergFinPart (z + t j) (D.translateDatum 0 j) := by
  have h_orth (k : D.X (j + 1) × D.X j) : star (t j k) * z k = 0 := by
    ext w
    by_cases hw : ↑D.N ∈ w.asIdeal
    · simp [ht j k (star w) (by simpa using hw)]
    · rw [D.isSplitLevel_piNPlaces.natCast_mem_iff, not_or] at hw
      simp [hz k w hw.left hw.right]
  ext1
  simp [translateDatum, finHeisenbergOp_finHeisenbergOp, dotProduct, h_orth]

open scoped Classical in
/-- Let the translations `t` vanish at the places above `N`. Then `D.gluedDoubleLiftDatum` is a sum
over the vectors `y` on `X_{2i+1}` of classes modulo `N` at each place `w ∣ π` (`D.piNPlaces`). Its
term is the tensor of the translates of the integral vacuum by `t (2 i)` plus `poleColumn`, the
matrix with last column `-y / N` at the `w ∣ π`, and by `t (2 i + 1)` plus `poleRow`, the matrix
with last row `-ȳ / N` at their conjugates. -/
lemma gluedDoubleLiftDatum_translateDatum {t : D.Translations}
    (ht : ∀ (j : ℕ) (k : D.X (j + 1) × D.X j) (w : FinPlace D.E), ↑D.N ∈ w.asIdeal → t j k w = 0)
    (i : ℕ) :
    D.gluedDoubleLiftDatum (D.translateDatum t) i = ∑ y : D.X (2 * i + 1) → D.piNPlaces → ZMod D.N,
      (D.homX (2 * i)).heisenbergFinPart (poleColumn (D.InitIndex (2 * i)) y + t (2 * i))
          (D.translateDatum 0 (2 * i)) ⊗ₜ
        (D.homX (2 * i + 1)).heisenbergFinPart
          (poleRow (D.InitIndex (2 * i + 1 + 1)) y + t (2 * i + 1))
          (D.translateDatum 0 (2 * i + 1)) := by
  simp only [gluedDoubleLiftDatum, doubleLiftGluing, LinearMap.sum_apply, map_tmul,
    D.heisenbergFinPart_translateDatum_of_disjoint ht _ _
      fun k w hw _ ↦ poleColumn_apply_eq_zero _ k w hw,
    D.heisenbergFinPart_translateDatum_of_disjoint ht _ _
      fun k w _ hw_star ↦ poleRow_apply_eq_zero _ k w hw_star]

/-- The index set of the gluing: for each of the `ϱ + 1 = m / 2` double lifts, a vector on the
middle space `X_{2 i + 1}` modulo `N` at each place `w ∣ π`. -/
abbrev GluingClasses : Type :=
  ∀ i : Fin (D.ϱ + 1), D.X (2 * (i : ℕ) + 1) → D.piNPlaces → ZMod D.N

variable {D} in
/-- The tuple of translations `z` attached to the classes `y`: in the `i`-th double lift, `z (2 i)`
has last column `-y i / N` and the last row of `z (2 i + 1)` is its conjugate; all other entries
are `0`. -/
noncomputable def gluingTuple (y : D.GluingClasses) : D.Translations :=
  ∑ i : Fin (D.ϱ + 1), (Pi.single (2 * (i : ℕ)) (poleColumn (D.InitIndex (2 * i)) (y i)) +
    Pi.single (2 * (i : ℕ) + 1) (poleRow (D.InitIndex (2 * i + 1 + 1)) (y i)))

variable {D} in
lemma gluingTuple_two_mul (y : D.GluingClasses) (i : Fin (D.ϱ + 1)) :
    gluingTuple y (2 * i) = poleColumn (D.InitIndex (2 * i)) (y i) := by
  rw [gluingTuple, Finset.sum_apply, Fintype.sum_eq_single i]
  · simp
  · intro i' hi'
    simp [show (i : ℕ) ≠ i' by lia, show 2 * (i : ℕ) ≠ 2 * i' + 1 by lia]

variable {D} in
lemma gluingTuple_two_mul_add_one (y : D.GluingClasses) (i : Fin (D.ϱ + 1)) :
    gluingTuple y (2 * i + 1) = poleRow (D.InitIndex (2 * i + 1 + 1)) (y i) := by
  rw [gluingTuple, Finset.sum_apply, Fintype.sum_eq_single i]
  · simp
  · intro i' hi'
    simp [show (i : ℕ) ≠ i' by lia, show 2 * (i : ℕ) + 1 ≠ 2 * i' by lia]

variable {D} in
/-- For each class `y` in `D.GluingClasses`, the tuple of translations `gluingTuple y` lies in
`D.supportedTranslations D.N`: it vanishes at all places prime to `N`. -/
lemma gluingTuple_mem_supportedTranslations (y : D.GluingClasses) :
    gluingTuple y ∈ D.supportedTranslations D.N := by
  intro j k w hw
  obtain ⟨hw_notMem, hw_star⟩ : w ∉ D.piNPlaces ∧ star w ∉ D.piNPlaces := by
    simpa [D.isSplitLevel_piNPlaces.natCast_mem_iff] using hw
  have h_single (l : ℕ) (z : D.X (l + 1) × D.X l → 𝔸f D.E)
      (hz : ∀ k' : D.X (l + 1) × D.X l, z k' w = 0) :
      (Pi.single l z : D.Translations) j k w = 0 := by
    obtain rfl | h_ne := eq_or_ne j l <;> simp [*]
  refine Finset.sum_induction _ (fun z : D.Translations ↦ z j k w = 0)
    (by simp +contextual) (by simp) fun i _ ↦ ?_
  simp [h_single _ _ fun k' ↦ poleColumn_apply_eq_zero (y i) k' w hw_notMem,
    h_single _ _ fun k' ↦ poleRow_apply_eq_zero (y i) k' w hw_star]

open scoped Classical in
/-- A class of the gluing assigns a residue modulo `N` to each double lift `i`, basis index of
`X_{2i+1}` and place `w ∣ π`. There are at most `N ^ (f m n_m / 2)` of them. -/
lemma card_gluingClasses_le : Fintype.card D.GluingClasses ≤ D.N ^ (D.f * D.m * D.n D.m / 2) := by
  -- There are `m / 2 = ϱ + 1` double lifts, each with at most `N ^ (f n_m)` classes.
  have hm : D.m = 2 * D.ϱ + 2 := D.m_eq_two_mul_varrho_add_two
  have h_exponent : D.f * D.m * D.n D.m = D.f * D.n D.m * (D.ϱ + 1) * 2 := by
    linear_combination (D.f * D.n D.m) * hm
  have h_pair (i : Fin (D.ϱ + 1)) :
      Fintype.card (D.X (2 * (i : ℕ) + 1) → D.piNPlaces → ZMod D.N) ≤ D.N ^ (D.f * D.n D.m) :=
    calc _ = D.N ^ (D.f * D.n (2 * i + 1)) := by
          rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_coe, card_piNPlaces,
            card_X, pow_mul]
      _ ≤ D.N ^ (D.f * D.n D.m) :=
        Nat.pow_le_pow_right NeZero.one_le (Nat.mul_le_mul_left _ (D.n_mono (by lia)))
  calc Fintype.card D.GluingClasses
    _ = ∏ i : Fin (D.ϱ + 1), Fintype.card (D.X (2 * (i : ℕ) + 1) → D.piNPlaces → ZMod D.N) :=
      Fintype.card_pi
    _ ≤ (D.N ^ (D.f * D.n D.m)) ^ (D.ϱ + 1) := by
      simpa using Finset.prod_le_pow_card .univ _ _ fun i _ ↦ h_pair i
    _ = D.N ^ (D.f * D.m * D.n D.m / 2) := by
      rw [h_exponent, Nat.mul_div_cancel _ two_pos, ← pow_mul]

/-- The tensor `⊗ⱼ translateDatum t j` of the translates of the integral vacuum by `t`, grouped by
double lifts and not glued. -/
noncomputable def ungluedVacuum (t : D.Translations) : D.ChainTensor :=
  pure (fun i : ℕ ↦ D.translateDatum t (2 * i) ⊗ₜ D.translateDatum t (2 * i + 1)) (D.ϱ + 1)

variable {D} in
/-- The plain tensor of `Ψ` is `∑ x, Ψ x • D.ungluedVacuum x`. -/
lemma plainTensor_eq_sum_ungluedVacuum (Ψ : D.Translations →₀ ℂ) :
    plainTensor Ψ = Ψ.sum fun (x : D.Translations) (c : ℂ) ↦ c • D.ungluedVacuum x :=
  rfl

open scoped Classical in
/-- If the translations `t` vanish at the places above `N`, the glued tensor `D.gluedVacuum t` is
the sum, over the classes `y` of the gluing, of `D.ungluedVacuum (t + gluingTuple y)`: the tensors,
not glued, of the translates of the integral vacuum by `t + gluingTuple y`. -/
lemma gluedVacuum_eq_sum_translates {t : D.Translations}
    (ht : ∀ (j : ℕ) (k : D.X (j + 1) × D.X j) (w : FinPlace D.E), ↑D.N ∈ w.asIdeal → t j k w = 0) :
    D.gluedVacuum t = ∑ y : D.GluingClasses, D.ungluedVacuum (t + gluingTuple y) := by
  have h_datum (x : D.Translations) (j : ℕ) :
      D.translateDatum x j = (D.homX j).heisenbergFinPart (x j) (D.translateDatum 0 j) :=
    Subtype.ext (by simp [translateDatum, finHeisenbergOp_finHeisenbergOp])
  -- Expand each double lift, then the tensor product of the sums.
  unfold gluedVacuum ungluedVacuum
  rw [pure_congr fun i _ ↦ D.gluedDoubleLiftDatum_translateDatum ht i]
  refine pure_sum _ _ fun y i ↦ ?_
  rw [h_datum, h_datum _ (2 * i + 1), add_comm t, Pi.add_apply, Pi.add_apply, gluingTuple_two_mul,
    gluingTuple_two_mul_add_one]

variable {D} in
/-- Adding a tuple `z` that vanishes at the places not above `N` to a tuple that is admissible for
`q` gives a tuple that is admissible for `q N`. -/
lemma add_mem_admissibleTranslations_mul_N {q : ℕ} {t z : D.Translations}
    (ht : t ∈ D.admissibleTranslations q) (hz : z ∈ D.supportedTranslations D.N) :
    t + z ∈ D.admissibleTranslations (q * D.N) := by
  intro j k w hw
  rw [Nat.cast_mul, w.isPrime.mul_mem_iff_mem_or_mem, not_or] at hw
  simpa [hz j k w hw.right] using ht j k w hw.left

open scoped Classical in
variable {D} in
/-- A class `y` of the gluing gives a residue modulo `N` for each double lift, middle basis index
and place `w ∣ π`, and `gluingTuple y` puts `-y / N` in the corresponding last columns and its
conjugate in the last rows. `D.ungluedVacuum t` is the tensor product over `j` of the translates of
the integral vacuum by `t j`.

Let the tuple `t` be admissible for `q`: each `t j`, times the conjugate of `D.piM`, is integral at
the places prime to `q`. Then the sum of `D.ungluedVacuum (t + gluingTuple y)` over all classes `y`
equals `∑ x, r x • D.ungluedVacuum x` with `r` supported on tuples admissible for `q N`. The values
of `r` are integral away from `q` with denominator `1`, and all conjugates of `r` have `ℓ¹`-norm at
most `N ^ (f m n_m)`. The norm bound is only asked when `boundRequired` holds. -/
lemma isAdmissibleCombination_sum_ungluedVacuum {q : ℕ} {t : D.Translations}
    (ht : t ∈ D.admissibleTranslations q) (boundRequired : Prop) :
    IsAdmissibleCombination D.ungluedVacuum (D.admissibleTranslations (q * D.N)) q 1 boundRequired
      (D.N ^ (D.f * D.m * D.n D.m))
      (∑ y : D.GluingClasses, D.ungluedVacuum (t + gluingTuple y)) := by
  -- The coefficients are `1`, so the sum of norms is the number of classes.
  have h_card : (Fintype.card D.GluingClasses : ℝ) ≤ D.N ^ (D.f * D.m * D.n D.m) :=
    mod_cast D.card_gluingClasses_le.trans
      (Nat.pow_le_pow_right NeZero.one_le (Nat.div_le_self _ 2))
  have h_classes : IsAdmissibleCombination
      (fun y : D.GluingClasses ↦ D.ungluedVacuum (t + gluingTuple y))
      .univ q 1 boundRequired (D.N ^ (D.f * D.m * D.n D.m))
      (∑ y : D.GluingClasses, D.ungluedVacuum (t + gluingTuple y)) := by
    simpa using IsAdmissibleCombination.of_sum (c := 1) (d := 1)
      (v := fun y : D.GluingClasses ↦ D.ungluedVacuum (t + gluingTuple y)) (s := .univ)
      (by simp) fun _ _ ↦ by simpa using h_card
  exact h_classes.bind 1 1 (fun y _ ↦ .single (t + gluingTuple y)
    (add_mem_admissibleTranslations_mul_N ht (gluingTuple_mem_supportedTranslations y)))
    (by simp) (by simp)

variable {D}

/-- Suppose that the plain tensor `∑ x, Ψ x • ⊗ⱼ translateDatum x j`, with the factors grouped in
pairs `2 i, 2 i + 1` (the double lifts), is fixed by every tuple `b j ∈ D.levelX j` with `b m = 1`.
Then the same sum, with `m` single factors, is jointly invariant: for every tuple `b` with `b j = 1`
for all `j ≥ m` and every linear map from the `m`-fold tensor product to the functions on the Weyl
indices of `X_m`, the sum before and after the action of `b` has the same image. -/
lemma isJointlyInvariant_of_plainTensor {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}
    (h_plain : (plainTensor Ψ).IsInvariant ϑ) :
    IsJointlyInvariant (D.liftKernel ϑ) D.m Ψ.support
      (fun x : D.Translations ↦ Ψ x • LinearMap.id) D.translateDatum := by
  -- `T` regroups the `ϱ + 1` pairs into `m = 2 (ϱ + 1)` single factors.
  let S (j : ℕ) : Type := (D.homX j).finitePart
  let T : D.ChainTensor →ₗ[ℂ] TensorChain S (2 * (D.ϱ + 1)) :=
    TensorChain.lift (liftInPairs (M := fun j ↦ TensorChain S j) fun j ↦
      TensorProduct.mk ℂ (S j) (TensorChain S j)) (1 : ℂ) (D.ϱ + 1)
  have hT (f : ∀ j : ℕ, S j) :
      T (pure (fun i : ℕ ↦ f (2 * i) ⊗ₜ f (2 * i + 1)) (D.ϱ + 1)) = pure f (2 * (D.ϱ + 1)) :=
    (lift_pure ..).trans (compUpTo_liftInPairs_tmul ..)
  rw [show D.m = 2 * (D.ϱ + 1) from D.m_eq_two_mul_varrho_add_two]
  intro b hb β
  have h_inv : β (T (TensorChain.map (twoKernelAction (D.liftKernel ϑ) fun j ↦ b j) (D.ϱ + 1)
      (plainTensor Ψ))) = β (T (plainTensor Ψ)) := by
    rw [h_plain b (hb _ le_rfl)]
  simpa [plainTensor, twoKernelAction, ← hT, Finsupp.sum] using h_inv

/-- A place `w` above the level `N` divides neither the principal level `D.M` nor `ϑ.normQ`, the
product of the norms of the places in the finite set `ϑ.Q` of the tame character `ϑ`. -/
lemma TameChar.M_mul_normQ_notMem_of_N_mem (ϑ : D.TameChar) {w : FinPlace D.E}
    (hw : ↑D.N ∈ w.asIdeal) : ↑(D.M * ϑ.normQ) ∉ w.asIdeal := by
  have h_gProd : ↑D.M ∉ w.asIdeal := by
    simpa [← piM_mul_star, IsChosen, w.isPrime.mul_mem_iff_mem_or_mem]
      using D.not_isChosen_of_N_mem hw
  simpa [w.isPrime.mul_mem_iff_mem_or_mem, h_gProd] using ϑ.normQ_notMem_of_N_mem hw

open scoped Classical in
/-- **Expanding the gluing.** Fix admissible data `D`: a CM field `E` with `f` infinite places, a
chain of `m` theta lifts `X_0 → ⋯ → X_m` with `X_j` of rank `n_j`, and a prime level `N = π π̄`. A
twist `ϑ` is a character of `U(1)(𝔸)` of weight `0` with tame part non-trivial exactly at a finite
set of places of norm prime to `N`. A tuple of translations (`D.Translations`) is a finite adelic
matrix for each lift. A chain datum `Ψ` for `ϑ` is a finitely supported coefficient function on such
tuples, with bounded support and size, whose glued tensor `gluedTensor Ψ` (its tensor, glued in each
double lift) is invariant.

Then `gluedTensor Ψ` is the double sum, over `x` and over the classes `y` in `D.GluingClasses` (a
residue modulo `N` for each double lift, middle basis index and place above `π`), of `Ψ x` times
`D.ungluedVacuum (x + gluingTuple y)`, the tensor product over the lifts of the integral vacuum (a
fixed scalar multiple of the vacuum vector of `Hom(X_j, X_{j+1})`) translated by
`x + gluingTuple y`. There are at most `N ^ (f m n_m / 2)` classes `y`, and the tuples
`gluingTuple y` vanish at the places not above `N`. -/
lemma IsChainDatum.gluedTensor_eq_sum_translates {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}
    (hΨ : IsChainDatum ϑ Ψ) :
    (gluedTensor Ψ = Ψ.sum fun (x : D.Translations) (c : ℂ) ↦
      c • ∑ y : D.GluingClasses, D.ungluedVacuum (x + gluingTuple y)) ∧
    Fintype.card D.GluingClasses ≤ D.N ^ (D.f * D.m * D.n D.m / 2) ∧
    ∀ y : D.GluingClasses, gluingTuple y ∈ D.supportedTranslations D.N := by
  refine ⟨Finsupp.sum_congr fun x hx ↦ ?_, D.card_gluingClasses_le,
    gluingTuple_mem_supportedTranslations⟩
  -- `x` vanishes at the places prime to `D.M * ϑ.normQ`, hence above `N`.
  have hx_zero : x ∈ D.supportedTranslations (D.M * ϑ.normQ) :=
    Set.inter_subset_right (hΨ.support_subset x hx)
  rw [D.gluedVacuum_eq_sum_translates fun j k w hw ↦
    hx_zero j k w (ϑ.M_mul_normQ_notMem_of_N_mem hw)]

/-- Every chain datum `Ψ` has a weak chain datum `Ψ'`, obtained by expanding the gluing, such that
on every source form `φ` (a form on `X_0` of level `D.levelX 0`) the two composite lifts agree:
`compositeLift ϑ Ψ φ`, which lifts `φ` through the double lifts with the glued tensor of `Ψ` as data
and restricts the result from `X_m` to its subspace `Y_m`, equals `restrictedChain ϑ Ψ' φ`, the
combination `Ψ'` of chains of `m` single lifts, restricted in the same way. -/
lemma IsChainDatum.exists_isWeakChainDatum_compositeLift_eq {ϑ : D.Twist}
    {Ψ : D.Translations →₀ ℂ} (hΨ : IsChainDatum ϑ Ψ) :
    ∃ Ψ' : D.Translations →₀ ℂ, IsWeakChainDatum ϑ Ψ' ∧
      ∀ φ : D.SourceForm, compositeLift ϑ Ψ φ = restrictedChain ϑ Ψ' φ := by
  classical
  -- The glued tensor is a combination, with coefficients `Ψ`, of the sums over the classes `y`.
  have h_outer : IsAdmissibleCombination
      (fun x : D.Translations ↦ ∑ y : D.GluingClasses, D.ungluedVacuum (x + gluingTuple y))
      (D.admissibleTranslations ϑ.normQ ∩ D.supportedTranslations (D.M * ϑ.normQ))
      ϑ.normQ 1 (ϑ.Q = ∅) (D.M ^ (3 * D.f * D.m * D.n D.m ^ 2)) (gluedTensor Ψ) :=
    ⟨Ψ, hΨ.toIsAdmissibleCoeffs, hΨ.gluedTensor_eq_sum_translates.left⟩
  have h_size : (D.M ^ (3 * D.f * D.m * D.n D.m ^ 2) * D.N ^ (D.f * D.m * D.n D.m) : ℝ) ≤
      Real.exp (D.x ^ 60) := Real.le_exp_of_log_le D.le_of_hasLogBound
  obtain ⟨Ψ', h_adm, h_sum⟩ : IsAdmissibleCombination D.ungluedVacuum
      (D.admissibleTranslations (ϑ.normQ * D.N)) ϑ.normQ 1 (ϑ.Q = ∅)
      (Real.exp (D.x ^ 60)) (gluedTensor Ψ) :=
    h_outer.bind 1 (D.N ^ (D.f * D.m * D.n D.m))
      (fun x hx ↦ isAdmissibleCombination_sum_ungluedVacuum (Set.inter_subset_left hx) (ϑ.Q = ∅))
      (by simp) fun _ ↦ by simpa using h_size
  have h_eq : gluedTensor Ψ = plainTensor Ψ' := by rw [h_sum, plainTensor_eq_sum_ungluedVacuum]
  have h_inv : (plainTensor Ψ').IsInvariant ϑ := by simpa [← h_eq] using hΨ.isInvariant
  refine ⟨Ψ', ⟨h_adm, isJointlyInvariant_of_plainTensor h_inv⟩, fun φ ↦ ?_⟩
  have h_chain : chainOfTensor ϑ φ (plainTensor Ψ') =
      chainCombination ϑ Ψ' D.translateDatum (2 * (D.ϱ + 1)) φ := by
    simp [plainTensor, chain, Finsupp.sum, compUpTo_liftInPairs_tmul]
  rw [compositeLift, h_eq, h_chain]
  exact restrictToYOfEq_apply _ fun j ↦ chainCombination ϑ Ψ' D.translateDatum j φ

/-- Let `ϑ` be a twist and `Ψ` a chain datum for `ϑ`: coefficients on tuples `x` of translation
matrices whose glued tensor is invariant. Then the plain tensor
`φ♭ = ∑ x, Ψ x • ⊗ⱼ translateDatum x j` of the translated integral vacua is invariant too: under the
Weil actions of the theta kernels `D.liftKernel ϑ`, every tuple `b j ∈ D.levelX j` with `b m = 1`
fixes it. -/
lemma IsChainDatum.isInvariant_plainTensor {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}
    (hΨ : IsChainDatum ϑ Ψ) : (plainTensor Ψ).IsInvariant ϑ := by
  let pr : D.ChainTensor →ₗ[ℂ] D.ChainTensor := TensorChain.map
    (fun i ↦ map (vacuumProjFinPart (D.homX (2 * i)) D.piNPlaces)
      (vacuumProjFinPart (D.homX (2 * i + 1)) D.piNPlaces)) (D.ϱ + 1)
  have h_pr : pr (gluedTensor Ψ) = plainTensor Ψ := by
    simp +contextual [pr, gluedTensor, plainTensor, gluedVacuum, Finsupp.sum,
      hΨ.mem_admissibleTranslations, D.vacuumProjFinPart_gluedDoubleLiftDatum ϑ]
  -- The levels are integral, so they commute with the projection.
  have h_comm (j : ℕ) (a : D.levelX j) (b : D.levelX (j + 1)) :
      (D.liftKernel ϑ j).ω (a, b) ∘ₗ vacuumProjFinPart (D.homX j) D.piNPlaces =
        vacuumProjFinPart (D.homX j) D.piNPlaces ∘ₗ (D.liftKernel ϑ j).ω (a, b) := by
    ext v : 2
    simp [liftKernel_ω, pairWeil_apply, omega_projOn,
      mem_stdLevel_iff.1 (D.isLevel_levelX.le a.property),
      mem_stdLevel_iff.1 (D.isLevel_levelX.le b.property)]
  intro b hb
  calc TensorChain.map (twoKernelAction (D.liftKernel ϑ) fun j ↦ b j) (D.ϱ + 1) (plainTensor Ψ)
    _ = pr (TensorChain.map (twoKernelAction (D.liftKernel ϑ) fun j ↦ b j) (D.ϱ + 1)
          (gluedTensor Ψ)) := by
      simp only [← h_pr, pr, gluedTensor, gluedVacuum, Finsupp.sum, map_sum, map_smul,
        TensorChain.map_pure, twoKernelAction, TensorProduct.map_map, h_comm]
    _ = plainTensor Ψ := by rw [hΨ.isInvariant b hb, h_pr]

/-- Here `D` is admissible data with scale `x = D.x` and prime level `N`. `ϑ` is a twist: a
weight-`0` character whose tame part is non-trivial exactly at the places of the finite set `ϑ.Q`.
Also `q = ϑ.normQ`, the product of their norms. A chain datum `Ψ` for `ϑ` is a weak chain datum.
That is: the tuples of translations in its support are admissible for `q N`, its values are integral
away from `q`, their conjugates have `ℓ¹`-norm at most `exp (x ^ 60)` if `ϑ.Q` is empty, and its
plain tensor `∑ x, Ψ x • ⊗ⱼ translateDatum x j`, with no gluing, is invariant under all the levels
`D.levelX j` at once. -/
lemma IsChainDatum.isWeakChainDatum {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}
    (hΨ : IsChainDatum ϑ Ψ) :
    IsWeakChainDatum ϑ Ψ where
  support_subset x hx j k w hw :=
    -- A place prime to `q N` is prime to `q`.
    hΨ.mem_admissibleTranslations hx j k w fun h_mem ↦
      hw (by simpa using w.asIdeal.mul_mem_right _ h_mem)
  integral := hΨ.integral
  sum_norm_le hQ σ := by
    have h_log : Real.log (D.M ^ (3 * D.f * D.m * D.n D.m ^ 2)) ≤ D.x ^ 60 := by
      simpa using D.le_of_hasLogBound
    exact (hΨ.sum_norm_le hQ σ).trans (Real.le_exp_of_log_le h_log)
  isJointlyInvariant := isJointlyInvariant_of_plainTensor hΨ.isInvariant_plainTensor

end New.Data
