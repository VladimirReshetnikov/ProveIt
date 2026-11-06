import DiophantineConsistency.Mixed121.Mixed121Increment
import DiophantineConsistency.Compact44.Facts.FreeJGraphCongruenceExplore
import DiophantineConsistency.Compact44.Facts.FreeJSaturationClient

/-! # Alignment, first-pair congruence and native cells at the 121x8801 ports

This is the 121x8801 counterpart of Compact44's
`FreeJGraphCongruenceExplore.symbolic_aligned_facts`, the first tuple-level
link of the `LeafFacts` halting chain. Let a positive valuation satisfy
`CompactLeafFacts.LeafFacts Mixed121Ports.ports v`. With `d = 121·8801`, there
are `N > 0` and `w` such that:

* `q = 2^(dN)` and `J = rep(d, N)`, and `X = q·w` with `w = 2^(R − dN)`;
* the first-pair congruence `((K + w)·C) mod (Jβ) = F` holds;
* the native word `C = q − F − α` has `dig₁₂₁ C 0 = 1`, and each of its
  `8801·N` cells is at most `3`.

Everything is composed from port-generic `Facts/` lemmas of Compact44
(`graph_aligned_congruence_facts`, `graph_saturation_facts`) and the new
121x8801 modules (`Mixed121Ports`, `Mixed121Masks`, `Mixed121Increment`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Aligned
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem port_three :
    ((Mixed121Ports.ports 3 : ℕ) : V) = (Mixed121Ports.highNat : V) + (Mixed121Ports.ports 0 : V) := by
  unfold Mixed121Ports.ports
  rw [Mixed121Ports.ports_three, Mixed121Ports.ports_zero, Nat.cast_add, add_comm]

theorem port_two : ((Mixed121Ports.ports 2 : ℕ) : V) = (Mixed121Ports.lowNat : V) := by
  unfold Mixed121Ports.ports
  rw [Mixed121Ports.ports_two]

theorem symbolic_aligned (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧
      dig 121 C 0=1 ∧ ∀ k<8801*N, dig 121 C k≤3 := by
  let p := Mixed121Ports.ports
  let d : V := 121*8801
  obtain ⟨hb, hl, hh, hbeta⟩ := Mixed121Ports.leaf_bounds (V:=V)
  have hport : (p 0:V) = Exp.exp d - 1 := Mixed121Ports.port_beta
  obtain ⟨N,w,hN,hq,hle,hw,hv5,hpos,hbound,hcongr⟩ :=
    FreeJGraphCongruenceExplore.graph_aligned_congruence_facts p v d hb hl hh hv hz hbeta
      (by dsimp [d]; norm_num) hport
  have hJ : v 0=rep d N := by
    apply ArithmeticRepunit.eq_rep_of_identity (by dsimp [d]; norm_num)
    calc (Exp.exp d-1)*v 0+1 = 1+v 0*(p 0:V) := by rw [←hport]; ring
      _ = Exp.exp (d*N) := hq
  obtain ⟨hnc, _⟩ := FreeJSaturationClient.graph_saturation_facts p v d N
    (Mixed121Ports.highNat : V) hb hl hh hv hz hbeta (by dsimp [d]; norm_num) hN hq hJ
    port_three (by rw [port_two]; exact Mixed121Masks.model_low_lt)
    Mixed121Masks.model_high_lt (by rw [port_two]; exact Mixed121Masks.model_low_even)
    Mixed121Masks.model_high_mod_eight
    (by rw [port_two]; exact Mixed121Masks.model_population_sum)
    (Mixed121Ports.high_mul_pos (v 0) (hv 0))
  have hC : 1 ≤ 1+v 0*(p 0:V)-v 1-v 2 := by
    apply pos_iff_one_le.mp
    simpa only [tsub_tsub] using (hz.transport hb)
  have hnc' : NoCarry ((1+v 0*(p 0:V)-v 1-v 2)-1)
      (((Mixed121Ports.lowNat : ℕ) : V) * rep (121*8801) N + 1) := by
    have h := hnc
    have e2 : (p 2:V)*v 0+1 = ((Mixed121Ports.lowNat : ℕ) : V) * rep (121*8801) N + 1 := by
      rw [port_two, hJ]
    rw [e2] at h
    exact h
  have hdigits := Mixed121Increment.recipe_digits N _ hN hC hnc'
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,hdigits⟩
end Mixed121Aligned
#print axioms Mixed121Aligned.port_three
#print axioms Mixed121Aligned.symbolic_aligned
