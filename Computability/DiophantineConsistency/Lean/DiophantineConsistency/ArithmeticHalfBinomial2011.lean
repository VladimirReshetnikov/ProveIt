import DiophantineConsistency.ArithmeticHalfBinomial
import DiophantineConsistency.ArithmeticCarrierRadix2011

/-! Spec A6 at the actual maintained current zero: the population lower bound
`3*(width*L)+2 ≤ σ(rank v)` for the same block count `L` as the radix.
Only positivity and the literal split zero are premises; the half-binomial
identity, the binomial coefficient and the 2-adic valuation are all derived
internally (ArithmeticHalfBinomial, ArithmeticBinomLegendre). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticHalfBinomial2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticBinaryPopulation ArithmeticHalfBinomial
  ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ObjectCurrentEquation2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem one_le_of_pos {x : V} (h : 0<x) : 1≤x := by
  simpa using lt_iff_succ_le.mp h

/-- The rank dominates `q^2-1`, hence `3h+1` when `q = 2^h ≥ 16`. -/
theorem three_h_lt_rank (v : Fin 14 → V) (hv : ∀j,0<v j) (h : V)
    (hq : q v=Exp.exp h) : 3*h+1≤rank v := by
  obtain ⟨hb,_,_⟩ := current_bounds (V:=V)
  have hq16 : (16:V)≤q v := by
    unfold q
    calc
      (16:V)=15*1+1 := by ring
      _≤(CurrentMasks2011.beta:V)*v 0+1 :=
        add_le_add (mul_le_mul hb (one_le_of_pos (hv 0)) (by simp) (by simp)) le_rfl
  have hR : (q v)^2-1≤rank v := by
    unfold rank
    have h1 : 1≤(q v-1)*(q v-v 1)+v 2 :=
      le_trans (one_le_of_pos (hv 2)) (le_add_of_nonneg_left (by simp))
    calc
      (q v)^2-1=1*((q v)^2-1) := (one_mul _).symm
      _≤((q v-1)*(q v-v 1)+v 2)*((q v)^2-1) := mul_le_mul_of_nonneg_right h1 (by simp)
      _≤_ := le_add_of_nonneg_right (by simp)
  have hhq : h+1≤q v := by rw [hq]; exact lt_iff_succ_le.mp (lt_exp h)
  have hsq : 3*h+1+1≤(q v)^2 := calc
    3*h+1+1≤3*(h+1)+(16:V) := by
      have : 3*h+1+1+(3+14:V)=3*(h+1)+16 := by ring
      rw [←this]; exact le_add_of_nonneg_right (by simp)
    _≤3*q v+q v := add_le_add (mul_le_mul_of_nonneg_left hhq (by simp)) hq16
    _=4*q v := by ring
    _≤16*q v := mul_le_mul_of_nonneg_right (by
      exact_mod_cast (show (4:ℕ)≤16 by decide)) (by simp)
    _≤q v*q v := mul_le_mul_of_nonneg_right hq16 (by simp)
    _=(q v)^2 := by ring
  exact le_trans (le_tsub_of_add_le_right hsq) hR

/-- The core: actual equations, the recovered power and the radix exponent
`q = 2^h` give `3h+2 ≤ σ(rank v)`. -/
theorem population_of_equations (v : Fin 14 → V) (hv : ∀j,0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hp : X v=Exp.exp (rank v)) (h : V) (hq : q v=Exp.exp h) :
    3*h+2≤population (rank v) := by
  obtain ⟨hb,hl,hh⟩ := current_bounds (V:=V)
  have hb0 : (0:V)<(CurrentMasks2011.beta:V) := lt_of_lt_of_le (by simp) hb
  obtain ⟨ht,hn,hm,hf,hu⟩ := he
  obtain ⟨n,_,hn5,_,hnR,_,hk,_,hc,_,_,_,_⟩ :=
    ArithmeticPellFirstIndex.maintained_first_indices
    (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
    ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    (v 10) (v 11) (v 12) (v 13) hb0 hl hh
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7) (hv 8) (hv 9)
    (hv 10) (hv 11) (hv 12) (hv 13) ht hn hm hf hu
  change v 10+v 11=2*ycoord n (2*(X v*Y v*Y v-1)+1) at hk
  change (v 10+v 11)*Y v+v 10=ycoord (rank v) (X v*Y v+Y v) at hc
  change 2*n=rank v+1 at hnR
  -- the half index
  have hn1 : 1≤n := le_trans (by simp) hn5
  obtain ⟨r,hrn⟩ : ∃ r, r+1=n := ⟨n-1,tsub_add_cancel_of_le hn1⟩
  have hr4 : 4≤r := by
    have : (4:V)+1≤r+1 := by rw [hrn]; simpa only [show (4:V)+1=5 by ring] using hn5
    exact (add_le_add_iff_right 1).mp this
  have hR : rank v=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    rw [←hnR,←hrn]; ring
  have hXe : X v=Exp.exp (2*r+1) := by rw [hp,hR]
  have hY : 1≤Y v := by
    unfold Y
    have hq1 : 1≤q v := by unfold q; exact le_add_of_nonneg_left (by simp)
    exact one_le_mul (one_le_of_pos (hv 7)) (by
      simpa only [show (q v)^3=q v*q v*q v by ring] using one_le_mul (one_le_mul hq1 hq1) hq1)
  have hck : ycoord (2*r+1) (Y v*(X v+1))=2*ycoord (r+1) (2*(X v*Y v*Y v-1)+1)*Y v+v 10 := by
    rw [show Y v*(X v+1)=X v*Y v+Y v by ring,←hR,←hc,hrn,←hk]
  obtain ⟨w,hw⟩ := half_binomial (X v) (Y v) r (v 10) (v 11) hr4 hXe hY hck
    (by rw [hrn,←hk]) (hv 10) (hv 11)
  have hYq : Exp.exp (3*h)∣Y v := by
    refine ⟨v 7,?_⟩
    unfold Y
    rw [hq,show 3*h=h+h+h by ring,exp_add,exp_add]
    ring
  have h3 := three_h_lt_rank v hv h hq
  rw [hR] at h3 ⊢
  exact population_lower (X v) (Y v) r w h hXe hw hYq h3

/-- **Spec A6 at the actual current zero.** Only positivity and the literal
split zero are premises. The radix conjunction is stated in full at the same `L`. -/
theorem current_population_lower (v : Fin 14 → V) (hv : ∀j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    ∃ L : V, 0<L ∧ q v=Exp.exp ((CurrentMasks2011.width:V)*L) ∧
      (CurrentMasks2011.width:V)*L≤rank v ∧
      v 8=Exp.exp (rank v-(CurrentMasks2011.width:V)*L) ∧
      Exponential ((CurrentMasks2011.width:V)*L) (q v) ∧
      Exponential (rank v-(CurrentMasks2011.width:V)*L) (v 8) ∧
      3*((CurrentMasks2011.width:V)*L)+2≤population (rank v) := by
  obtain ⟨⟨hp,_,_⟩,L,hL,hq,hle,h8,he1,he2⟩ := current_radix v hv hz
  exact ⟨L,hL,hq,hle,h8,he1,he2,
    population_of_equations v hv (current_equations v hv hz) hp _ hq⟩

/-- The natural-domain client, with the accepted single shift `u = v+1`. -/
theorem current_natural_population_lower (v : Fin 14 → V)
    (hz : naturalExpression.splitNatural.1.evalSemiring v=
      naturalExpression.splitNatural.2.evalSemiring v) :
    let u:=fun j => v j+1
    ∃ L : V, 0<L ∧ q u=Exp.exp ((CurrentMasks2011.width:V)*L) ∧
      (CurrentMasks2011.width:V)*L≤rank u ∧
      u 8=Exp.exp (rank u-(CurrentMasks2011.width:V)*L) ∧
      Exponential ((CurrentMasks2011.width:V)*L) (q u) ∧
      Exponential (rank u-(CurrentMasks2011.width:V)*L) (u 8) ∧
      3*((CurrentMasks2011.width:V)*L)+2≤population (rank u) := by
  intro u
  have hu : ∀j,0<u j := fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _)
  obtain ⟨⟨hp,_,_⟩,L,hL,hq,hle,h8,he1,he2⟩ := current_natural_radix v hz
  exact ⟨L,hL,hq,hle,h8,he1,he2,
    population_of_equations u hu (current_natural_equations v hz) hp _ hq⟩

end DiophantineConsistency.ArithmeticHalfBinomial2011
