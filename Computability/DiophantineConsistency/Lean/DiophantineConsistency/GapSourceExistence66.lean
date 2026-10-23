import DiophantineConsistency.GapSourceContract66
import DiophantineConsistency.SplitSourceExistence

/-!
# Unbounded nine-coordinate existence for H2082

The cofinal digit-sum construction is reused unchanged. Only the new
H2082 word, rank and threshold contracts determine the arithmetic equation.
-/

namespace DiophantineConsistency.GapSourceExistence66

open Polynomial Finset Jones1982
open GapSourceWords66 GapSourceContract66
open SplitSourceExistence (cofinalCap digits_lt_cofinalCap code_lt_cofinalCap
  code_pos exists_positive_digit_of_code_pos)
open scoped BigOperators

noncomputable def value (d : Parameters) (a b g : ℕ) (v : FreeCarrierRatio.FreeVars) (n : ℕ) : ℤ :=
  GapNineRatio66.value a b g (word d a b g) (mask d a b) v n

/-- Nine positive unknowns, with the positive CRT input represented as j+1.
The internal absorbed index itself remains an unrestricted natural number. -/
def HasZero (d : Parameters) (a : ℕ) : Prop :=
  ∃ b g : ℕ,0<b ∧ 0<g ∧ ∃ v : FreeCarrierRatio.FreeVars,
    0<v.h ∧ 0<v.s ∧ 0<v.w ∧ 0<v.C ∧ 0<v.i ∧
      ∃ n : ℕ,0<n ∧ value d a b g v n=0

/-- A nonzero source coefficient witness yields an actual equation zero using
the explicit cofinal cap, so no boundedness premise survives this theorem. -/
theorem hasZero_iff_source {d : Parameters} {a : ℕ} (hd : Valid d a) :
    HasZero d a ↔ ∃ z : Fin 31 → ℕ,(∃ i,0<z i) ∧
      ∀ j,(sourcePolynomial d z).coeff (d.q j)=0 := by
  constructor
  · rintro ⟨b,g,hb,hg,v,hh,hs,hw,hC,hi,n,hn,hzero⟩
    obtain ⟨k,hpow,z,hz,hcode,hcoeff⟩ := source_of_zero hd v hb hh hs hw hC hi ⟨n,hn,hzero⟩
    refine ⟨z,?_,hcoeff⟩
    apply exists_positive_digit_of_code_pos d.w z
    rw [← hcode]
    exact hg
  · rintro ⟨z,hzpos,hcoeff⟩
    let b := cofinalCap z
    have hb : 0<b := by dsimp [b,cofinalCap]; positivity
    have hB : 0<GapNineRatio66.base a b := by have h := (GapNineRatio66.base_bounds a hb).1; omega
    let g := LowMaskCoding.indexedCode (GapNineRatio66.base a b) d.w z
    have hg : 0<g := code_pos hB d.w z hzpos
    have hcap : g<b*(GapNineRatio66.base a b)^116 := code_lt_cofinalCap hB d.w hd.weights_le z
    obtain ⟨v,hh,hs,hw,hC,hi,n,hn,hzero⟩ := zero_of_source hd (b:=b)
      (k:=(∑ i,z i)+1) rfl z (digits_lt_cofinalCap z) hcoeff hcap
    exact ⟨b,g,hb,hg,v,hh,hs,hw,hC,hi,n,hn,hzero⟩

/-- The literal positive coordinate order is b,g,h,s,w,C,i,j_plus,n. -/
def positiveVars (x : Fin 9 → ℕ) : FreeCarrierRatio.FreeVars :=
  ⟨x 2,x 3,x 4,x 5,x 6,x 7-1⟩

noncomputable def positiveValue (d : Parameters) (a : ℕ) (x : Fin 9 → ℕ) : ℤ :=
  value d a (x 0) (x 1) (positiveVars x) (x 8)

/-- The positive tuple contains exactly nine coordinates, including j_plus. -/
theorem exists_positive_zero_iff_hasZero (d : Parameters) (a : ℕ) :
    (∃ x : Fin 9 → ℕ,(∀ i,0<x i) ∧ positiveValue d a x=0) ↔ HasZero d a := by
  constructor
  · rintro ⟨x,hpos,hzero⟩
    exact ⟨x 0,x 1,hpos 0,hpos 1,positiveVars x,hpos 2,hpos 3,hpos 4,hpos 5,hpos 6,
      x 8,hpos 8,hzero⟩
  · rintro ⟨b,g,hb,hg,v,hh,hs,hw,hC,hi,n,hn,hzero⟩
    let x : Fin 9 → ℕ := ![b,g,v.h,v.s,v.w,v.C,v.i,v.j+1,n]
    have hp : ∀ i,0<x i := by
      intro i
      fin_cases i
      · exact hb
      · exact hg
      · exact hh
      · exact hs
      · exact hw
      · exact hC
      · exact hi
      · exact Nat.succ_pos _
      · exact hn
    have hv : positiveVars x=v := by
      cases v
      rfl
    refine ⟨x,hp,?_⟩
    change value d a b g (positiveVars x) n=0
    rw [hv]
    exact hzero

/-- All positive coordinates are shifted by one; the internal CRT index is x7. -/
def naturalVars (x : Fin 9 → ℕ) : FreeCarrierRatio.FreeVars :=
  ⟨x 2+1,x 3+1,x 4+1,x 5+1,x 6+1,x 7⟩

noncomputable def naturalValue (d : Parameters) (a : ℕ) (x : Fin 9 → ℕ) : ℤ :=
  value d a (x 0+1) (x 1+1) (naturalVars x) (x 8+1)

theorem positiveValue_successors (d : Parameters) (a : ℕ) (x : Fin 9 → ℕ) :
    positiveValue d a (fun i => x i+1)=naturalValue d a x := rfl

/-- The exact bijective nine-natural-coordinate translation. -/
theorem exists_natural_zero_iff_hasZero (d : Parameters) (a : ℕ) :
    (∃ x : Fin 9 → ℕ,naturalValue d a x=0) ↔ HasZero d a := by
  rw [← exists_positive_zero_iff_hasZero d a]
  constructor
  · rintro ⟨x,hzero⟩
    exact ⟨fun i => x i+1,fun i => Nat.succ_pos _,by rw [positiveValue_successors]; exact hzero⟩
  · rintro ⟨x,hpos,hzero⟩
    let y : Fin 9 → ℕ := fun i => x i-1
    have he : (fun i => y i+1)=x := by
      funext i
      exact Nat.sub_add_cancel (by have h:=hpos i; omega)
    refine ⟨y,?_⟩
    rw [← positiveValue_successors,he]
    exact hzero

theorem exists_natural_zero_iff_source {d : Parameters} {a : ℕ} (hd : Valid d a) :
    (∃ x : Fin 9 → ℕ,naturalValue d a x=0) ↔
      ∃ z : Fin 31 → ℕ,(∃ i,0<z i) ∧ ∀ j,(sourcePolynomial d z).coeff (d.q j)=0 :=
  (exists_natural_zero_iff_hasZero d a).trans (hasZero_iff_source hd)

/-- Negating the proved existence equivalence introduces no consistency claim. -/
theorem no_natural_zero_iff {d : Parameters} {a : ℕ} (hd : Valid d a) :
    (∀ x : Fin 9 → ℕ,naturalValue d a x≠0) ↔
      ¬∃ z : Fin 31 → ℕ,(∃ i,0<z i) ∧ ∀ j,(sourcePolynomial d z).coeff (d.q j)=0 := by
  simpa only [not_exists] using not_congr (exists_natural_zero_iff_source hd)

end DiophantineConsistency.GapSourceExistence66
