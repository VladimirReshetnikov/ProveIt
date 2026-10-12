import GowersSzemeredi.Proofs13RectanglePartitionMass

/-! A dense subset of a modular square has a dense genuine integer
rectangle with a shared positive step and explicit square-root side bounds. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem dense_common_step_integer_rectangle {N : Nat} [NeZero N]
    (P R : ModAP N) (hP : P.IsProper) (hR : R.IsProper)
    (hlen : P.length = R.length) (hstep : P.step = R.step) (hm : 4 ≤ P.length)
    (B : Finset (Pair N)) (delta : Real) (hd : 0 < delta)
    (hB : B ⊆ P.carrier.product R.carrier)
    (hmass : delta * P.length * R.length ≤ B.card) :
    ∃ Q T : NatAP, ∃ E : Finset (Pair N),
      Q.IsProper ∧ T.IsProper ∧ Q.step = T.step ∧
      Q.carrier ⊆ Finset.range N ∧ T.carrier ⊆ Finset.range N ∧
      delta * Real.sqrt P.length / 16 ≤ Q.length ∧
      delta * Real.sqrt P.length / 16 ≤ T.length ∧
      E ⊆ B ∧ E ⊆ (Q.toModAP N).carrier.product (T.toModAP N).carrier ∧
      delta / 4 * Q.length * T.length ≤ E.card := by
  classical
  obtain ⟨d, M, L, Q, T, hdstep, hQpart, hTpart, hQprops, hTprops, hM, hL⟩ :=
    common_integer_refinement_pair P R hP hR hlen hstep hm
  have hQproper (i : Fin M) : ((Q i).toModAP N).IsProper :=
    ((Q i).toModAP_hasIntegerRepresentatives (hQprops i).1 (hQprops i).2.2).isProper
  have hTproper (j : Fin L) : ((T j).toModAP N).IsProper :=
    ((T j).toModAP_hasIntegerRepresentatives (hTprops j).1 (hTprops j).2.2).isProper
  have hsumQ : ∑ i, ((Q i).length : Real) = P.length := by
    have h : ∑ i, (Q i).length = P.length := by
      calc
        _ = ∑ i, ((Q i).toModAP N).carrier.card :=
          Finset.sum_congr rfl (fun i _ => (hQproper i).symm)
        _ = P.carrier.card := hQpart.sum_card
        _ = P.length := hP
    exact_mod_cast h
  have hsumT : ∑ j, ((T j).length : Real) = P.length := by
    have h : ∑ j, (T j).length = P.length := by
      calc
        _ = ∑ j, ((T j).toModAP N).carrier.card :=
          Finset.sum_congr rfl (fun j _ => (hTproper j).symm)
        _ = R.carrier.card := hTpart.sum_card
        _ = R.length := hR
        _ = P.length := hlen.symm
    exact_mod_cast h
  let A (i : Fin M) (j : Fin L) := ((Q i).toModAP N).carrier.product ((T j).toModAP N).carrier ∩ B
  have hsumA : (∑ i, ∑ j, ((A i j).card : Real)) = B.card := by
    exact_mod_cast product_partition_inter_sum_card
      (fun i => ((Q i).toModAP N).carrier) (fun j => ((T j).toModAP N).carrier)
      P.carrier R.carrier hQpart hTpart B hB
  have hcap (i : Fin M) (j : Fin L) : (A i j).card ≤ (Q i).length * (T j).length := by
    have h : (A i j).card ≤
        (((Q i).toModAP N).carrier.product ((T j).toModAP N).carrier).card :=
      Finset.card_le_card Finset.inter_subset_left
    calc
      (A i j).card ≤ _ := h
      _ = ((Q i).toModAP N).carrier.card * ((T j).toModAP N).carrier.card :=
        Finset.card_product _ _
      _ = (Q i).length * (T j).length := congrArg₂ Nat.mul (hQproper i) (hTproper j)
  have hsqrt : (Nat.sqrt P.length : Real) ≤ Real.sqrt P.length :=
    Real.le_sqrt_of_sq_le (by rw [pow_two]; exact_mod_cast Nat.sqrt_le P.length)
  have hMreal : (M : Real) ≤ 4 * Real.sqrt P.length :=
    (by exact_mod_cast hM : (M : Real) ≤ 4 * (Nat.sqrt P.length : Real)).trans
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
  have hLreal : (L : Real) ≤ 4 * Real.sqrt P.length :=
    (by exact_mod_cast hL : (L : Real) ≤ 4 * (Nat.sqrt P.length : Real)).trans
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
  have hmpos : (0 : Real) < P.length := by exact_mod_cast (show 0 < P.length by omega)
  obtain ⟨i, j, hQi, hTj, hcell⟩ := exists_dense_large_rectangle_cell
    (fun i => ((Q i).length : Real)) (fun j => ((T j).length : Real))
    (fun i j => ((A i j).card : Real)) P.length P.length delta (delta * Real.sqrt P.length / 16)
    hmpos hmpos hd (by positivity) (fun _ => by positivity) (fun _ => by positivity)
    hsumQ hsumT (fun i j => by exact_mod_cast hcap i j)
    (by rw [hsumA]; simpa only [← hlen] using hmass)
    (square_root_rectangle_capacity (Nat.cast_nonneg _) hd.le hMreal hLreal)
  refine ⟨Q i, T j, A i j, (hQprops i).1, (hTprops j).1,
    (hQprops i).2.1.trans (hTprops j).2.1.symm, (hQprops i).2.2, (hTprops j).2.2,
    hQi, hTj, Finset.inter_subset_right, Finset.inter_subset_left, hcell⟩

end LeanProofs.GowersSzemeredi
