import Model69ViewMap

/-! Experimental transfer of the two retained natural norms into the
model difference ring. The actual-zero caller is not yet provided. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69RetainedNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ModelDifferenceRing
open Model69ViewMap
open DiophantineConsistency
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ObjectCurrentEquation2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_norm (E N k Y R : V) (hR : R≤E*N+k)
    (hn : (E*N+k-R)*(E*N+k-R)=1+(E*Y)*(E*Y+1)*k*k) :
    ((ι E * ι N + ι k - ι R : DiffRing V)^2 -
      (ι E * ι k * ι Y) * (ι E * ι k * ι Y + ι k)) = 1 := by
  have h := congrArg (ι : V → DiffRing V) hn
  simp only [map_add, map_mul, map_one, map_sub_of_le _ _ hR] at h
  linear_combination h

theorem main_norm (a c d : V)
    (hn : d*d=1+(a+1)*(a+3)*c*c) :
    (ι d : DiffRing V)^2 - ((ι a)^2+(4*ι a+3))*(ι c)^2 = 1 := by
  have h := congrArg (ι : V → DiffRing V) hn
  simp only [map_add, map_mul, map_one, map_ofNat] at h
  linear_combination h

/-- Attempted caller extracting actual 2011 bounds before matching the graph. -/
theorem current_bounds_for_map (v : Fin 14 → V) (hv : ∀j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    v 1≤q v ∧ v 2≤q v-v 1 ∧ 1≤(q v)^2 ∧
      rank v≤X v*Y v*v 9+(v 10+v 11) := by
  obtain ⟨hb,hl,hh⟩ := current_bounds (V:=V)
  have hb0 : (0:V)<(CurrentMasks2011.beta:V) := lt_of_lt_of_le (by simp) hb
  have ht := (current_equations v hv hz).1
  obtain ⟨hgap,hRlo,hRhi⟩ := ArithmeticPellFirstIndex.scalar_window
    (q v) (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
    (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
    (v 0) (v 1) (v 2) (v 3) (v 8) (v 7) hb0
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 8) (hv 7) hl hh rfl ht
  have hF : v 1≤q v := by
    have hsub : 0<q v-v 1 := lt_of_lt_of_le hgap tsub_le_self
    exact le_of_lt (tsub_pos_iff_lt.mp hsub)
  have ha : v 2≤q v-v 1 := le_of_lt (tsub_pos_iff_lt.mp hgap)
  have hq1 : (1:V)≤q v := by dsimp [q]; simp
  have hq2 : (1:V)≤(q v)^2 := by
    simpa only [pow_two] using one_le_mul hq1 hq1
  have hRE : rank v+2<X v*Y v := by
    convert hRhi using 1
    dsimp [rank,X,Y]
    ring
  have hR : rank v≤X v*Y v*v 9+(v 10+v 11) := le_of_lt (calc
    rank v<rank v+2 := lt_add_of_pos_right _ (by simp)
    _<X v*Y v := hRE
    _≤X v*Y v*v 9 := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 9))
    _≤X v*Y v*v 9+(v 10+v 11) := by simp)
  exact ⟨hF,ha,hq2,hR⟩

end Model69RetainedNorm
#print axioms Model69RetainedNorm.first_norm
#print axioms Model69RetainedNorm.main_norm
#print axioms Model69RetainedNorm.current_bounds_for_map
