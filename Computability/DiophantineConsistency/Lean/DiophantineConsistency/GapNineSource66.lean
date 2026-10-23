import DiophantineConsistency.GapSourceExistence66
import DiophantineConsistency.SplitNineSource59

/-!
# Literal H2082 source and the unbounded nine-coordinate equation

The four coefficient ports have explicit size bounds. The half-height
parameter is 432007 for the coherent compact54-sharp instance. Native
compiler interpretation and internal ZFC provability are separate.
-/

namespace DiophantineConsistency.GapNineSource66

open GapSourceWords66 GapSourceContract66

noncomputable abbrev parameters (ports : Fin 4 → ℤ) : Parameters := literalParameters ports

theorem coefficients_zero_iff_source (ports : Fin 4 → ℤ) (z : Fin 31 → ℕ) :
    (∀ j, (sourcePolynomial (parameters ports) z).coeff (GapCertificate66.targets j) = 0) ↔
      ∀ j, GapSource66.rows ports (fun i => (z i : ℤ)+1) j = 0 :=
  GapKernels66.sourcePolynomial_zero_iff ports (fun i => (z i : ℤ)+1)

noncomputable def naturalValue (ports : Fin 4 → ℤ) (a : ℕ) (x : Fin 9 → ℕ) : ℤ :=
  GapSourceExistence66.naturalValue (parameters ports) a x

/-- The full unbounded existence equivalence with the authoritative old-z
source. The source itself rules out the all-one positive tuple. -/
theorem exists_natural_zero_iff_source (ports : Fin 4 → ℤ) (a : ℕ)
    (hd : Valid (parameters ports) a) :
    (∃ x : Fin 9 → ℕ, naturalValue ports a x = 0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j,
        GapSource66.rows ports (fun i => (z i : ℤ) + 1) j = 0 := by
  change (∃ x : Fin 9 → ℕ, GapSourceExistence66.naturalValue (parameters ports) a x = 0) ↔ _
  rw [GapSourceExistence66.exists_natural_zero_iff_source hd]
  constructor
  · rintro ⟨z, _, hz⟩
    exact ⟨z, (coefficients_zero_iff_source ports z).mp hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, GapKernels66.source_zero_has_nonzero_digit ports z hz,
      (coefficients_zero_iff_source ports z).mpr hz⟩

theorem exists_natural_zero_iff_source_portBounds (ports : Fin 4 → ℤ) (p q a : ℕ)
    (hp : 1 ≤ p) (hpq : p+4 ≤ q) (ha : p+q+1=2*a)
    (hb : 0 ≤ ports 0 ∧ ports 0 < 2^p)
    (hk : 0 ≤ ports 1 ∧ ports 1 < 2^q)
    (hm : 0 ≤ ports 2 ∧ ports 2 < 2^p)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*2^p) :
    (∃ x : Fin 9 → ℕ, naturalValue ports a x=0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j, GapSource66.rows ports (fun i => (z i : ℤ)+1) j=0 :=
  exists_natural_zero_iff_source ports a
    (literal_valid_pow ports p q a hp hpq ha hb hk hm hf)

theorem exists_natural_zero_iff_source_compact54 (ports : Fin 4 → ℤ)
    (hb : 0 ≤ ports 0 ∧ ports 0 < 2^429959)
    (hk : 0 ≤ ports 1 ∧ ports 1 < 2^434054)
    (hm : 0 ≤ ports 2 ∧ ports 2 < 2^429959)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*2^429959) :
    (∃ x : Fin 9 → ℕ, naturalValue ports 432007 x=0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j, GapSource66.rows ports (fun i => (z i : ℤ)+1) j=0 :=
  exists_natural_zero_iff_source_portBounds ports 429959 434054 432007
    (by decide) (by decide) (by decide) hb hk hm hf

private theorem exists_successor_iff_positive {m : ℕ} (P : (Fin m → ℤ) → Prop) :
    (∃ z : Fin m → ℕ, P (fun i => (z i : ℤ)+1)) ↔
      ∃ x : Fin m → ℕ, (∀ i,0<x i) ∧ P (fun i => (x i : ℤ)) := by
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨fun i => z i+1,fun _ => Nat.succ_pos _,?_⟩
    simpa only [Nat.cast_add,Nat.cast_one] using hz
  · rintro ⟨x,hpos,hx⟩
    have he : (fun i => ((x i-1 : ℕ) : ℤ)+1)=(fun i => (x i : ℤ)) := by
      funext i
      exact_mod_cast Nat.sub_add_cancel (show 1 ≤ x i by have h:=hpos i; omega)
    refine ⟨fun i => x i-1,?_⟩
    rw [he]
    exact hx

/-- The affine source bridge preserves all unbounded successor-coordinate zeros. -/
theorem source_successor_zero_iff_old (ports : Fin 4 → ℤ) (hβ : 0<ports 0) :
    (∃ z : Fin 31 → ℕ, ∀ j, GapSource66.rows ports (fun i => (z i : ℤ)+1) j=0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j,
        SplitCertificate59.sourceRows ports (fun i => (z i : ℤ)+1) j=0 :=
  (exists_successor_iff_positive (fun x : Fin 31 → ℤ => ∀ j,GapSource66.rows ports x j=0)).trans
    ((GapSource66.exists_positive_nat_zero_iff ports hβ).trans
      (exists_successor_iff_positive
        (fun x : Fin 31 → ℤ => ∀ j,SplitCertificate59.sourceRows ports x j=0)).symm)

/-- Both numerical recipes have the same unbounded natural zero existence.
This is a source-equation comparison, not a native consistency calibration. -/
theorem compact54_zero_iff_split59 (ports : Fin 4 → ℤ) (hβ : 0<ports 0)
    (hb : 0 ≤ ports 0 ∧ ports 0 < 2^429959)
    (hk : 0 ≤ ports 1 ∧ ports 1 < 2^434054)
    (hm : 0 ≤ ports 2 ∧ ports 2 < 2^429959)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*2^429959) :
    (∃ x : Fin 9 → ℕ, naturalValue ports 432007 x=0) ↔
      ∃ x : Fin 9 → ℕ, SplitNineSource59.naturalValue ports 864014 x=0 :=
  (exists_natural_zero_iff_source_compact54 ports hb hk hm hf).trans
    ((source_successor_zero_iff_old ports hβ).trans
      (SplitNineSource59.exists_natural_zero_iff_source_compact54 ports hb hk hm hf).symm)

theorem no_natural_zero_iff_source (ports : Fin 4 → ℤ) (a : ℕ)
    (hd : Valid (parameters ports) a) :
    (∀ x : Fin 9 → ℕ, naturalValue ports a x≠0) ↔
      ¬∃ z : Fin 31 → ℕ, ∀ j, GapSource66.rows ports (fun i => (z i : ℤ)+1) j=0 := by
  simpa only [not_exists] using not_congr (exists_natural_zero_iff_source ports a hd)

end DiophantineConsistency.GapNineSource66
