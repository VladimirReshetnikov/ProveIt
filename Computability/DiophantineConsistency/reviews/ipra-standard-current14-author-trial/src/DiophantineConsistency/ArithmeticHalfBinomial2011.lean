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

/-- The rank dominates `q^2-1`, hence `3h+1` when `q = 2^h ≥ 16`. -/
theorem three_h_lt_rank (v : Fin 14 → V) (hv : ∀j,0<v j) (h : V)
    (hq : q v=Exp.exp h) : 3*h+1≤rank v := by
  obtain ⟨hb,_,_⟩ := current_bounds (V:=V)
  have hq16 : (16:V)≤q v := by
    unfold q
    calc
      (16:V)=15*1+1 := by ring
      _≤(CurrentMasks2011.beta:V)*v 0+1 :=
        add_le_add (mul_le_mul hb (pos_iff_one_le.mp (hv 0)) (by simp) (by simp)) le_rfl
  simpa only [rank] using
    ArithmeticHalfBinomial.rank_lower_of_radix (q v) (v 1) (v 2) (v 0)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
      h hq16 (hv 2) hq

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
  obtain ⟨r,hrn,hr4,hR⟩ := half_index_of_ge_five n (rank v) hn5 hnR
  have hXe : X v=Exp.exp (2*r+1) := by rw [hp,hR]
  have hY : 1≤Y v := by
    unfold Y
    have hq1 : 1≤q v := by unfold q; exact le_add_of_nonneg_left (by simp)
    exact one_le_mul (pos_iff_one_le.mp (hv 7)) (by
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
  exact current_population_lower (fun j => v j+1)
    (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)

end DiophantineConsistency.ArithmeticHalfBinomial2011
