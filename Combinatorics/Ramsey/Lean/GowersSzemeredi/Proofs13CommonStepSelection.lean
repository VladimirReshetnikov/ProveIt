import GowersSzemeredi.Proofs13CoefficientPartition
import GowersSzemeredi.Proofs10ProgressionLinearity

/-! The common-step partition and weighted selection in Lemma 13.6.
The selected progression retains both its lower and upper length bounds.

`lemma_13_6_of_bohr_models`, `lemma_13_6_of_bohr_models_with_length`,
`lemma_13_6_of_short_difference_rules` and `stage136_common_step_mem_bohr` are
in `Proofs13CommonStepSelectionSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A prime cyclic group admits a proper progression partition of prescribed
nonzero step, with lengths `m` or `m+1`, whenever `m^2 <= N`. -/
theorem cyclic_common_step_partition {N : Nat} [Fact N.Prime]
    (d : ZMod N) (hd : d != 0) (m : Nat) (hm : 0 < m) (hsize : m * m ≤ N) :
    ∃ M : Nat, ∃ P : Fin M → ModAP N,
      IsPartition (fun j ↦ (P j).carrier) Finset.univ ∧
      ∀ j, (P j).step = d ∧ (P j).IsProper ∧
        ((P j).length = m ∨ (P j).length = m + 1) := by
  let R : ModAP N := { start := 0, step := d, length := N }
  have hRuniv : R.carrier = Finset.univ := Finset.eq_univ_of_forall fun x =>
    Finset.mem_image.mpr ⟨⟨(x / d).val, (x / d).val_lt⟩, Finset.mem_univ _, by
      change 0 + (((x / d).val : Nat) : ZMod N) * d = x
      rw [zero_add, ZMod.natCast_zmod_val, div_mul_cancel₀ x (bne_iff_ne.mp hd)]⟩
  let B := R.asBox
  have hB : B.IsProper := fun _ ↦ by
    change R.carrier.card = N
    rw [hRuniv, Finset.card_univ, ZMod.card]
  have hsize' : m * m ≤ B.width := by rwa [BaseCase.boxOne_width B]
  let P : Fin (B.width / m) → ModAP N := fun j ↦ (BaseCase.coarseChildBox B m j).axis 0
  refine ⟨B.width / m, P, hRuniv ▸ box_one_partition_axes B (BaseCase.coarseChildBox B m)
    (BaseCase.coarseChildBox_partition B hB m hm hsize'),
    fun j ↦ ⟨rfl, BaseCase.coarseChildBox_proper B hB m hm hsize' j 0, ?_⟩⟩
  dsimp only [P, BaseCase.coarseChildBox, BaseCase.coarseChunkLength]
  split_ifs <;> simp

/-- Two points of a progression of length at most `m+1` differ by one of
its first `m` positive or negative step multiples. -/
theorem modAP_difference_mem_symmetric {N : Nat} (P : ModAP N) {m : Nat}
    (hlen : P.length ≤ m + 1) {x y : ZMod N} (hx : x ∈ P.carrier) (hy : y ∈ P.carrier) :
    x - y ∈ section10SymmetricMultiples P.step m := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
  apply Finset.mem_image.mpr
  refine ⟨(i : Nat) - (j : Int), Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
  · have := i.isLt
    have := j.isLt
    omega
  · have := i.isLt
    have := j.isLt
    omega
  · push_cast
    ring

/-- A scalar difference rule on short step multiples gives an affine
formula on any progression cell, even for a domain with repeated indices. -/
theorem linearOnDomain_of_short_difference_rule {N : Nat} {X : Type*}
    (Y : Finset X) (r : X → ZMod N) (phi : X → ZMod N) (P : ModAP N)
    (m : Nat) (hlen : P.length ≤ m + 1)
    (hrule : ∃ c : ZMod N, ∀ v ∈ Y, ∀ w ∈ Y,
      r v - r w ∈ section10SymmetricMultiples P.step m →
        phi v - phi w = c * (r v - r w)) :
    LinearOnDomain (Y.filter fun v ↦ r v ∈ P.carrier) r phi := by
  obtain ⟨c, hc⟩ := hrule
  by_cases hne : (Y.filter fun v ↦ r v ∈ P.carrier).Nonempty
  · obtain ⟨w, hw⟩ := hne
    obtain ⟨hwY, hwP⟩ := Finset.mem_filter.mp hw
    refine ⟨c, phi w - c * r w, ?_⟩
    intro v hv
    obtain ⟨hvY, hvP⟩ := Finset.mem_filter.mp hv
    have h := hc v hvY w hwY (modAP_difference_mem_symmetric P hlen hvP hwP)
    linear_combination h
  · refine ⟨0, 0, ?_⟩
    intro v hv
    exact (hne ⟨v, hv⟩).elim

/-- Choose one common-step progression preserving the aggregate row mass.
The upper length bound is retained for the geometry of Lemma 13.9. -/
theorem common_step_row_selection {N : Nat} [Fact N.Prime]
    (I : Finset (ZMod N)) (Y : ZMod N → Finset (Pair N))
    (phi : ZMod N → Pair N → ZMod N) (d : ZMod N) (m : Nat) (delta : Real)
    (hd : d != 0) (hm : 0 < m) (hsize : m * m ≤ N)
    (hmass : ∀ h ∈ I, delta * (N : Real) ^ 2 ≤ (Y h).card)
    (hrule : ∀ h ∈ I, ∃ c : ZMod N, ∀ v ∈ Y h, ∀ w ∈ Y h,
      v.1 - w.1 ∈ section10SymmetricMultiples d m →
        phi h v - phi h w = c * (v.1 - w.1)) :
    ∃ R : ModAP N, R.step = d ∧ R.IsProper ∧ (R.length = m ∨ R.length = m + 1) ∧
      (∀ h ∈ I, LinearOnDomain ((Y h).filter fun z ↦ z.1 ∈ R.carrier)
        (fun z : Pair N ↦ z.1) (phi h)) ∧
      delta * R.length * N * I.card ≤
        ∑ h ∈ I, ((Y h).filter fun z ↦ z.1 ∈ R.carrier).card := by
  obtain ⟨M, P, hP, hcell⟩ := cyclic_common_step_partition d hd m hm hsize
  -- the rows over `I` carry total mass at least `delta N ^ 2 |I|`
  have hmass' : (delta * N * I.card) * (Finset.univ : Finset (ZMod N)).card ≤
      (I.sigma Y).card := by
    have h := Finset.sum_le_sum hmass
    rw [Finset.sum_const, nsmul_eq_mul] at h
    rw [Finset.card_univ, ZMod.card, Finset.card_sigma, Nat.cast_sum]
    linarith
  obtain ⟨j, hj⟩ := exists_coordinate_filter_cell (I.sigma Y) Finset.univ
    (fun z : Sigma (fun _ : ZMod N ↦ Pair N) ↦ z.2.1)
    (fun j ↦ (P j).carrier) Finset.univ_nonempty hP (fun _ _ ↦ Finset.mem_univ _) hmass'
  obtain ⟨hstep, hproper, hlen⟩ := hcell j
  refine ⟨P j, hstep, hproper, hlen, fun h hh ↦ linearOnDomain_of_short_difference_rule (Y h)
    _ (phi h) (P j) m (by omega) (by simpa only [hstep] using hrule h hh), ?_⟩
  simp only [show (P j).carrier.card = (P j).length from hproper, Finset.filter_sigma,
    Finset.card_sigma] at hj
  nlinarith only [hj]

/-- Assemble Stage 13.6 from its row models and explicit integer partition
budgets, retaining the upper length bound needed by Lemma 13.9. -/
theorem lemma_13_6_of_short_difference_rules_with_length {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h135 : IsStage135Data S D E) (m : Nat) (Y : ZMod N → Finset (Pair N))
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hY : ∀ h ∈ criticalHeights S D E,
      Y h ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ (Y h).card)
    (hrule : ∀ h ∈ criticalHeights S D E, ∃ c : ZMod N, ∀ v ∈ Y h, ∀ w ∈ Y h,
      v.1 - w.1 ∈ section10SymmetricMultiples E.Q.step m →
        verticalPhiDifference S.phi h v - verticalPhiDifference S.phi h w =
          c * (v.1 - w.1)) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  let delta : Real := (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224
  obtain ⟨R, hs, hp, hl, hlinear, hmass⟩ := common_step_row_selection
    (criticalHeights S D E) Y (verticalPhiDifference S.phi) E.Q.step m delta
    h135.1 hm hsize (fun h hh ↦ (hY h hh).2) hrule
  have hmR : m ≤ R.length := by omega
  refine ⟨⟨R, Y⟩, ⟨hs, hs ▸ h135.1, hp, hlower.trans (by exact_mod_cast hmR),
    fun h hh ↦ ⟨(hY h hh).1, (hY h hh).2, hlinear h hh⟩, hmass, ?_⟩, hmR,
    show R.length ≤ E.Q.length by omega⟩
  -- `|crit| ≥ α ^ 32 |Q| / 20 ≥ α ^ 32 |Q| / 32`, and `2 ^ -43 / 32 = 2 ^ -48`
  calc (2 : Real) ^ (-(48 : Int)) * S.alpha ^ 256 * E.Q.length * R.length * N
      = delta * R.length * N * (S.alpha ^ 32 * E.Q.length / 32) := by
        rw [show (256 : Nat) = 224 + 32 by omega, pow_add]
        norm_num [delta, zpow_neg]
        ring
    _ ≤ delta * R.length * N * (criticalHeights S D E).card :=
        mul_le_mul_of_nonneg_left (by linarith [h135.2.2.2.2.2]) (by dsimp [delta]; positivity)
    _ ≤ _ := hmass

/-- The coordinate map for Section 13 edge differences, represented on
lower-endpoint pairs. Only the selected subset enters the Bohr model. -/
def section13EdgeIndexDomain (N : Nat) : MultifunctionDomain N (Pair N) where
  index := Prod.fst

/-- The common step lies in every required Bohr set, at any precision `ε`
of the Stage 13.5 phases with `ε ≤ ζ/m`. -/
theorem stage136_common_step_mem_bohr_at {N : Nat} [NeZero N]
    (S : Section13Context N) (theta zeta eps : Real) (D : Stage134Data N)
    (E : Stage135Data N) (m : Nat) (K : ZMod N → Finset (ZMod N))
    (h134 : IsStage134Data S theta D)
    (hprec : ∀ i, ∀ h, h ∈ E.Q.carrier →
      (centeredAbs ((D.a i * h + D.b i) * E.Q.step) : Real) ≤ eps * N)
    (hK : ∀ h ∈ criticalHeights S D E, ∀ r ∈ K h,
      theta * (N : Real) ^ 2 ≤ ‖fourier (verticalEdgeFiberFunction S.A h) r‖)
    (hbudget : eps ≤ zeta / m) :
    ∀ h ∈ criticalHeights S D E, E.Q.step ∈ bohr (K h) (zeta / m) := by
  classical
  intro h hh
  have hmem := Finset.mem_inter.mp (Finset.mem_filter.mp hh).1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  obtain ⟨i, hi⟩ := h134.2.2.2.2.2.2.2.2 h hmem.2 r (hK h hh r hr)
  rw [hi]
  exact (hprec i h hmem.1).trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _))

/-- The common-step extraction from Bohr models at a general precision. -/
theorem lemma_13_6_of_bohr_models_at {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (theta zeta eps : Real) (D : Stage134Data N)
    (E : Stage135Data N) (m : Nat) (Y : ZMod N → Finset (Pair N))
    (K : ZMod N → Finset (ZMod N)) (psi : ZMod N → ZMod N → ZMod N)
    (h134 : IsStage134Data S theta D) (h135 : IsStage135Data S D E)
    (hprec : ∀ i, ∀ h, h ∈ E.Q.carrier →
      (centeredAbs ((D.a i * h + D.b i) * E.Q.step) : Real) ≤ eps * N)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hY : ∀ h ∈ criticalHeights S D E,
      Y h ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ (Y h).card)
    (hK : ∀ h ∈ criticalHeights S D E, ∀ r ∈ K h,
      theta * (N : Real) ^ 2 ≤ ‖fourier (verticalEdgeFiberFunction S.A h) r‖)
    (hbudget : eps ≤ zeta / m)
    (hmodel : ∀ h ∈ criticalHeights S D E,
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        (K h) zeta (Y h) (psi h)) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  apply lemma_13_6_of_short_difference_rules_with_length S D E h135 m Y hm hsize hupper hlower hY
  intro h hh
  exact corollary_10_14_holds N (Pair N) (section13EdgeIndexDomain N)
    (verticalPhiDifference S.phi h) (K h) zeta (Y h) (psi h) (Fact.out : N.Prime)
    (hmodel h hh) m hm E.Q.step
    (stage136_common_step_mem_bohr_at S theta zeta eps D E m K h134 hprec hK hbudget h hh)

end LeanProofs.GowersSzemeredi
