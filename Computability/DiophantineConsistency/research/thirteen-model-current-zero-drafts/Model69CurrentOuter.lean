import DiophantineConsistency.ArithmeticHalfBinomial2011
import Model69Outer

/-! Draft caller from the actual maintained positive 2011 carrier zero.
The rank phase, exact 69-coordinate binding and fixed-port end theorem are
not yet proved here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69CurrentOuter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011
open ObjectCurrentEquation2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Draft: actual positive 2011 parent zero gives a positive gap and a
positive, beta*J-divisible retained transport. -/
theorem current_outer (v : Fin 14 → V) (hv : ∀ j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    let q:=q v
    let R:=rank v
    let C:=q-v 1-v 2
    ∃ L G : V, 0<L ∧ 0<R ∧ 0<C ∧ 0<G ∧ (CurrentMasks2011.beta:V)*v 0∣G ∧
      ((CurrentKernel2011.K:V)+v 8)*C=v 1+G ∧
      (v 10+v 11)*Y v+v 10 =
        ArithmeticPellRecurrence.ycoord R (X v*Y v+Y v) := by
  dsimp only
  obtain ⟨hb,hl,hh⟩ := current_bounds (V:=V)
  have hb0 : (0:V)<(CurrentMasks2011.beta:V) := lt_of_lt_of_le (by simp) hb
  have he := current_equations v hv hz
  obtain ⟨ht,hn,hm,hf,hu⟩ := he
  obtain ⟨L,hL,hq,hLE,hw8,hexq,hexw,hpop⟩ :=
    ArithmeticHalfBinomial2011.current_population_lower v hv hz
  have hX := (current_power v hv hz).1
  have hcount : ArithmeticBinaryPopulation.population (rank v) ≤ rank v :=
    (ArithmeticBinaryPopulation.population_le (rank v)).1.trans
      (ArithmeticBinaryPopulation.population_le (rank v)).2
  obtain ⟨G,hC,hG,hdiv,htrans⟩ :=
    Model69Outer.outer_of_scalar_data
      (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
      (v 0) (v 1) (v 2) (v 3) (v 8) (v 7) (CurrentMasks2011.width*L)
      (ArithmeticBinaryPopulation.population (rank v)) hb0 (hv 0) (hv 1) (hv 2)
      (hv 3) (hv 8) (hv 7) hl hh ht hq hX hcount hpop
  obtain ⟨n,_,hn5,hnlt,hnR,_,hk,_,hc,_,_,_,_⟩ :=
    ArithmeticPellFirstIndex.maintained_first_indices
      (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
      ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
      (v 10) (v 11) (v 12) (v 13) hb0 hl hh
      (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7) (hv 8) (hv 9)
      (hv 10) (hv 11) (hv 12) (hv 13) ht hn hm hf hu
  have hR : 0<rank v := by
    change n<rank v at hnlt
    exact lt_trans (lt_of_lt_of_le (by norm_num : (0:V)<5) hn5) hnlt
  refine ⟨L,G,hL,hR,?_,hG,?_,?_,?_⟩
  · simpa only [q] using hC
  · simpa only using hdiv
  · simpa only [q] using htrans
  · change (v 10+v 11)*Y v+v 10=ArithmeticPellRecurrence.ycoord (rank v) (X v*Y v+Y v) at hc
    exact hc
end Model69CurrentOuter
#print axioms Model69CurrentOuter.current_outer
