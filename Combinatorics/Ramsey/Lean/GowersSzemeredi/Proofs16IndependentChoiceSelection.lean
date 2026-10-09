import GowersSzemeredi.Proofs16PinnedChoiceCounts

/-! Finite independent-choice selection for distinct four-coordinate
queries. The expected error depends on only the four queried fibre sizes,
not on the number of progression points being assigned representatives. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def queriedBadChoices {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (q : Fin 4 → I) (B : Finset (Fin 4 → V)) : Finset (I → V) :=
  (Fintype.piFinset F).filter fun f => (fun j => f (q j)) ∈ B

/-- Exact four-coordinate error count before division or averaging. -/
theorem four_choice_bad_count_product {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (q : Fin 4 → I) (hq : Function.Injective q) (B : Finset (Fin 4 → V))
    (hB : ∀ b ∈ B, ∀ j, b j ∈ F (q j)) :
    (∏ j : Fin 4, (F (q j)).card)*(queriedBadChoices F q B).card =
      (Fintype.piFinset F).card*B.card := by
  have hsum : (queriedBadChoices F q B).card =
      ∑ b ∈ B, ((queriedBadChoices F q B).filter fun f => (fun j => f (q j)) = b).card :=
    Finset.card_eq_sum_card_fiberwise (fun f hf => (Finset.mem_filter.mp hf).2)
  have hfibre : ∀ b ∈ B,
      (queriedBadChoices F q B).filter (fun f => (fun j => f (q j)) = b) =
        (Fintype.piFinset F).filter (fun f => ∀ j, f (q j) = b j) := by
    intro b hb
    ext f
    simp only [queriedBadChoices, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hf, hbad⟩, heq⟩
      exact ⟨hf, fun j => congrFun heq j⟩
    · rintro ⟨hf, hvals⟩
      have heq : (fun j => f (q j)) = b := funext hvals
      exact ⟨⟨hf, heq.symm ▸ hb⟩, heq⟩
  rw [hsum, Finset.mul_sum]
  calc
    ∑ b ∈ B, (∏ j : Fin 4, (F (q j)).card)*
        ((queriedBadChoices F q B).filter fun f => (fun j => f (q j)) = b).card
      = ∑ _b ∈ B, (Fintype.piFinset F).card := Finset.sum_congr rfl fun b hb => by
        rw [hfibre b hb]
        exact four_choice_fibre_count_product F q hq b (hB b hb)
    _ = _ := by simp [Nat.mul_comm]

/-- There is one valid global representative assignment with the averaged
four-coordinate error bound. The remaining coordinate products cancel. -/
theorem exists_independent_choice_few_bad_queries {I V : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (hF : ∀ i, (F i).Nonempty)
    (Q : Finset (Fin 4 → I)) (B : (Fin 4 → I) → Finset (Fin 4 → V))
    (hq : ∀ q ∈ Q, Function.Injective q)
    (hB : ∀ q ∈ Q, ∀ b ∈ B q, ∀ j, b j ∈ F (q j))
    {D E : Real} (hD : 0 < D)
    (hprod : ∀ q ∈ Q, D ≤ ((∏ j : Fin 4, (F (q j)).card) : Real))
    (htotal : ∑ q ∈ Q, ((B q).card : Real) ≤ E) :
    ∃ f ∈ Fintype.piFinset F,
      (((Q.filter fun q => (fun j => f (q j)) ∈ B q).card) : Real) ≤ E/D := by
  let A := Fintype.piFinset F
  have hA : A.Nonempty := ⟨(fun i => (hF i).choose),
    Fintype.mem_piFinset.mpr (fun i => (hF i).choose_spec)⟩
  have hsum : ∑ f ∈ A, (Q.filter fun q => (fun j => f (q j)) ∈ B q).card =
      ∑ q ∈ Q, (queriedBadChoices F q (B q)).card := by
    simp only [queriedBadChoices, Finset.card_filter]
    exact Finset.sum_comm
  have hsumR : ∑ f ∈ A, ((Q.filter fun q => (fun j => f (q j)) ∈ B q).card : Real) =
      ∑ q ∈ Q, ((queriedBadChoices F q (B q)).card : Real) := by exact_mod_cast hsum
  have hscaled : D*(∑ q ∈ Q, ((queriedBadChoices F q (B q)).card : Real)) ≤ (A.card : Real)*E := by
    calc
      _ = ∑ q ∈ Q, D*(queriedBadChoices F q (B q)).card := Finset.mul_sum _ _ _
      _ ≤ ∑ q ∈ Q, (A.card : Real)*(B q).card := Finset.sum_le_sum fun q hqQ => by
        have h := four_choice_bad_count_product F q (hq q hqQ) (B q) (hB q hqQ)
        have hR : ((∏ j : Fin 4, (F (q j)).card) : Real)*(queriedBadChoices F q (B q)).card =
            (A.card : Real)*(B q).card := by exact_mod_cast h
        rw [←hR]
        exact mul_le_mul_of_nonneg_right (hprod q hqQ) (Nat.cast_nonneg _)
      _ = (A.card : Real)*(∑ q ∈ Q, ((B q).card : Real)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left htotal (Nat.cast_nonneg _)
  have havg : ∑ f ∈ A, ((Q.filter fun q => (fun j => f (q j)) ∈ B q).card : Real) ≤
      ∑ _f ∈ A, E/D := by
    rw [hsumR, Finset.sum_const, nsmul_eq_mul]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hD).mpr
    simpa only [mul_comm] using hscaled
  obtain ⟨f, hf, hbad⟩ := Finset.exists_le_of_sum_le hA havg
  exact ⟨f, hf, hbad⟩

end LeanProofs.GowersSzemeredi
