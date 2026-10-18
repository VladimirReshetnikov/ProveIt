import GowersSzemeredi.Proofs16ProductTiling

/-! # Bounded chunks without a square-scale assumption

For any positive target r no larger than the interval, cut off consecutive
chunks of length r and absorb the remainder in the last chunk. Every length
lies in [r, 2*r), so a preliminary localization costs only a constant factor
in width rather than a square root.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

private def boundedChunk (L r : Nat) (j : Fin (L / r)) : NatAP where
  start := (j : Nat) * r
  step := 1
  length := if (j : Nat) + 1 = L / r then L - (j : Nat) * r else r

private theorem boundedChunk_start_le {L r : Nat} (j : Fin (L / r)) :
    (j : Nat) * r ≤ L :=
  (Nat.mul_le_mul_right r (Nat.le_of_lt j.isLt)).trans (Nat.div_mul_le_self L r)

private theorem boundedChunk_bounds {L r : Nat} (hr : 0 < r) (j : Fin (L / r)) :
    r ≤ (boundedChunk L r j).length ∧ (boundedChunk L r j).length < 2 * r := by
  have hdiv := Nat.div_add_mod L r
  have hmod := Nat.mod_lt L hr
  have hstart := boundedChunk_start_le j
  dsimp [boundedChunk]
  split_ifs with h
  · have heq := congrArg (fun t : Nat => t * r) h
    have htotal : L = (j : Nat) * r + r + L % r := by nlinarith
    omega
  · omega

private theorem boundedChunk_end_le {L r : Nat} (j : Fin (L / r)) :
    (j : Nat) * r + (boundedChunk L r j).length ≤ L := by
  have hs := boundedChunk_start_le j
  dsimp [boundedChunk]
  split_ifs
  · omega
  · have h := (Nat.mul_le_mul_right r (show (j : Nat) + 1 ≤ L / r by omega)).trans
      (Nat.div_mul_le_self L r)
    nlinarith

private theorem boundedChunk_mem {L r : Nat} (j : Fin (L / r)) (x : Nat) :
    x ∈ (boundedChunk L r j).carrier ↔
      (j : Nat) * r ≤ x ∧ x < (j : Nat) * r + (boundedChunk L r j).length := by
  simp only [NatAP.carrier, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    change (j : Nat) * r ≤ (j : Nat) * r + (i : Nat) * 1 ∧ _
    have hi := i.isLt
    dsimp only [boundedChunk] at hi ⊢
    omega
  · intro hx
    refine ⟨⟨x - (j : Nat) * r, by omega⟩, ?_⟩
    change (j : Nat) * r + (x - (j : Nat) * r) * 1 = x
    omega

private theorem boundedChunk_proper {L r : Nat} (j : Fin (L / r)) :
    (boundedChunk L r j).IsProper := by
  refine ⟨by simp [boundedChunk], ?_⟩
  unfold NatAP.carrier
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    apply Fin.ext
    simpa [boundedChunk] using hab

private theorem boundedChunk_partition (L r : Nat) (hr : 0 < r) (hL : r ≤ L) :
    IsNatAPPartition (boundedChunk L r) (Finset.range L) := by
  have hM : 0 < L / r := Nat.div_pos hL hr
  have hsep (a b : Fin (L / r)) (hab : (a : Nat) < b) :
      (a : Nat) * r + (boundedChunk L r a).length ≤ (b : Nat) * r := by
    simp only [boundedChunk, if_neg (show (a : Nat) + 1 ≠ L / r by omega)]
    nlinarith [Nat.mul_le_mul_right r (show (a : Nat) + 1 ≤ b by omega)]
  refine ⟨fun x => ⟨fun hx => ?_, fun ⟨j, hj⟩ => Finset.mem_range.2
    (((boundedChunk_mem j x).mp hj).2.trans_le (boundedChunk_end_le j))⟩, fun i j hij => ?_⟩
  · rw [Finset.mem_range] at hx
    have hxr := Nat.div_add_mod' x r
    have hxm := Nat.mod_lt x hr
    by_cases hq : x / r + 1 < L / r
    · refine ⟨⟨x / r, by omega⟩, (boundedChunk_mem _ x).mpr ⟨Nat.div_mul_le_self x r, ?_⟩⟩
      simp only [boundedChunk, if_neg (show x / r + 1 ≠ L / r by omega)]
      omega
    · have h1 := Nat.mul_le_mul_right r (show L / r - 1 ≤ x / r by omega)
      have h2 := Nat.mul_le_mul_right r (show L / r - 1 ≤ L / r by omega)
      refine ⟨⟨L / r - 1, by omega⟩,
        (boundedChunk_mem _ x).mpr ⟨h1.trans (Nat.div_mul_le_self x r), ?_⟩⟩
      simp only [boundedChunk, if_pos (show L / r - 1 + 1 = L / r by omega)]
      have := Nat.div_mul_le_self L r
      omega
  · refine Finset.disjoint_left.mpr fun x hxi hxj => ?_
    have hi := (boundedChunk_mem i x).mp hxi
    have hj := (boundedChunk_mem j x).mp hxj
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne (bne_iff_ne.mp hij)) with h | h
    · have := hsep i j h; omega
    · have := hsep j i h; omega

/-- Localize a natural interval to lengths in [r,2*r), requiring only r<=L. -/
theorem bounded_interval_partition (L r : Nat) (hr : 0 < r) (hL : r ≤ L) :
    ∃ M : Nat, ∃ Q : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition Q (Finset.range L) ∧
      (∀ j, (Q j).IsProper ∧ r ≤ (Q j).length ∧ (Q j).length < 2 * r) ∧
      ∀ j, (Q j).step = 1 := by
  exact ⟨L / r, boundedChunk L r, Nat.div_pos hL hr,
    boundedChunk_partition L r hr hL,
    fun j => ⟨boundedChunk_proper j, boundedChunk_bounds hr j⟩, fun _ => rfl⟩

/-- Localize a proper modular progression while preserving its original step. -/
theorem ModAP.bounded_partition {N : Nat} [NeZero N] (P : ModAP N)
    (hP : P.IsProper) (r : Nat) (hr : 0 < r) (hsize : r ≤ P.length) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      0 < M ∧ IsPartition (fun j => (Q j).carrier) P.carrier ∧
      (∀ j, (Q j).IsProper ∧ r ≤ (Q j).length ∧ (Q j).length < 2 * r) ∧
      ∀ j, (Q j).step = P.step := by
  obtain ⟨M, R, hM, hpart, hprop, hstep⟩ := bounded_interval_partition P.length r hr hsize
  refine ⟨M, fun j => section5Transport P (R j), hM,
    section5Transport_partition P R hP hpart, ?_, ?_⟩
  · intro j
    exact ⟨section5Transport_isProper P (R j) hP (hprop j).1
      (IsPartition.cell_subset hpart j), (hprop j).2⟩
  · intro j
    change ((R j).step : ZMod N) * P.step = P.step
    rw [hstep j]
    simp

/-- Every proper positive-dimensional box can be localized to bounded axes
at only a constant-factor width cost, without changing the common difference. -/
theorem Box.bounded_partition {N k : Nat} [NeZero N] (P : Box N k)
    (hP : P.IsProper) (hk : 0 < k) (r : Nat) (hr : 0 < r) (hsize : r ≤ P.width) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper ∧ r ≤ (Q j).width) ∧
      (∀ j i, r ≤ ((Q j).axis i).length ∧ ((Q j).axis i).length < 2 * r) ∧
      ∀ j, (Q j).commonDiff = P.commonDiff := by
  choose m R _ hpart hprop hstep using fun i =>
    (P.axis i).bounded_partition (hP i) r hr (hsize.trans (P.width_le_axis_length i))
  have hstep' (i : Fin k) (j : Fin (m i)) : (R i j).step = P.commonDiff := by
    rw [hstep, P.axis_step]
  let Q := fun j : Fin (Fintype.card (∀ i, Fin (m i))) =>
    boxProductCell m R P.commonDiff hstep' ((Fintype.equivFin _).symm j)
  refine ⟨_, Q, boxProductCell_partition P m R _ hstep' hpart, ?_, ?_, ?_⟩
  · intro j
    exact ⟨fun i => (hprop i _).1,
      Box.le_width_of_le_axis _ hk (fun i => (hprop i _).2.1)⟩
  · intro j i
    exact (hprop i _).2
  · intro j
    rfl

end LeanProofs.GowersSzemeredi
