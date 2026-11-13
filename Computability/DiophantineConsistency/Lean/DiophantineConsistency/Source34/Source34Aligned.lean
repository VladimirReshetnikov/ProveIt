import DiophantineConsistency.Source34.Source34Increment
import DiophantineConsistency.Compact44.Facts.FreeJGraphCongruenceExplore
import DiophantineConsistency.Compact44.Facts.FreeJSaturationClient

/-! # Alignment, first-pair congruence and native cells at the source34 ports

`Mixed121Aligned` at the source34 tuple; every declaration mentions the ports,
so all are re-declared with `Source34Ports`, `Source34Masks` and
`Source34Increment` in place of their Mixed121 counterparts. The proof bodies
are unchanged.

Let a positive valuation satisfy `CompactLeafFacts.LeafFacts Source34Ports.ports v`.
With `d = 121·8801`, there are `N > 0` and `w` with `q = 2^(dN)`,
`J = rep(d, N)`, `X = q·w`, `w = 2^(R − dN)`, the first-pair congruence
`((K + w)·C) mod (Jβ) = F`, and a native word `C = q − F − α` with
`dig₁₂₁ C 0 = 1` whose `8801·N` cells are at most `3`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Aligned
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem port_three :
    ((Source34Ports.ports 3 : ℕ) : V) = (Source34Ports.highNat : V) + (Source34Ports.ports 0 : V) := by
  unfold Source34Ports.ports
  rw [Source34Ports.ports_three, Source34Ports.ports_zero, Nat.cast_add, add_comm]

theorem port_two : ((Source34Ports.ports 2 : ℕ) : V) = (Source34Ports.lowNat : V) := by
  unfold Source34Ports.ports
  rw [Source34Ports.ports_two]

theorem symbolic_aligned (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧
      dig 121 C 0=1 ∧ ∀ k<8801*N, dig 121 C k≤3 := by
  let p := Source34Ports.ports
  let d : V := 121*8801
  obtain ⟨hb, hl, hh, hbeta⟩ := Source34Ports.leaf_bounds (V:=V)
  have hport : (p 0:V) = Exp.exp d - 1 := Source34Ports.port_beta
  obtain ⟨N,w,hN,hq,hle,hw,hv5,hpos,hbound,hcongr⟩ :=
    FreeJGraphCongruenceExplore.graph_aligned_congruence_facts p v d hb hl hh hv hz hbeta
      (by dsimp [d]; norm_num) hport
  have hJ : v 0=rep d N := by
    apply ArithmeticRepunit.eq_rep_of_identity (by dsimp [d]; norm_num)
    calc (Exp.exp d-1)*v 0+1 = 1+v 0*(p 0:V) := by rw [←hport]; ring
      _ = Exp.exp (d*N) := hq
  obtain ⟨hnc, _⟩ := FreeJSaturationClient.graph_saturation_facts p v d N
    (Source34Ports.highNat : V) hb hl hh hv hz hbeta (by dsimp [d]; norm_num) hN hq hJ
    port_three (by rw [port_two]; exact Source34Masks.model_low_lt)
    Source34Masks.model_high_lt (by rw [port_two]; exact Source34Masks.model_low_even)
    Source34Masks.model_high_mod_eight
    (by rw [port_two]; exact Source34Masks.model_population_sum)
    (Source34Ports.high_mul_pos (v 0) (hv 0))
  have hC : 1 ≤ 1+v 0*(p 0:V)-v 1-v 2 := by
    apply pos_iff_one_le.mp
    simpa only [tsub_tsub] using (hz.transport hb)
  have hnc' : NoCarry ((1+v 0*(p 0:V)-v 1-v 2)-1)
      (((Source34Ports.lowNat : ℕ) : V) * rep (121*8801) N + 1) := by
    have h := hnc
    have e2 : (p 2:V)*v 0+1 = ((Source34Ports.lowNat : ℕ) : V) * rep (121*8801) N + 1 := by
      rw [port_two, hJ]
    rw [e2] at h
    exact h
  have hdigits := Source34Increment.recipe_digits N _ hN hC hnc'
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,hdigits⟩
end Source34Aligned
#print axioms Source34Aligned.port_three
#print axioms Source34Aligned.port_two
#print axioms Source34Aligned.symbolic_aligned
