import Trace74RankCRTChart

/-! CRT chart consequences for the actual carrier-register shape. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74RankCarrierCRT
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing Trace74RankCRTChart

section Ring
variable {R : Type*} [CommRing R]

/-- The carrier numerator has the required factor without a coprimality
assumption on `H` and `h*D`. -/
theorem carrier_divisibility (h D H B e K V v7 : R)
    (hB : h ∣ B) (he : D ∣ e) (hK : H ∣ K) :
    h*D*H ∣ h*D*(H*(v7-V^2*B)+K)-H*(D*B+h*e) := by
  obtain ⟨b,hb⟩ := hB
  obtain ⟨d,hd⟩ := he
  obtain ⟨k,hk⟩ := hK
  refine ⟨v7-V^2*B+k-b-d, ?_⟩
  rw [hb,hd,hk]
  ring
end Ring

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The same negative-rank witnesses supplied by CRT satisfy the carrier
divisibility, provided the graph's remaining `H ∣ K` input holds. -/
theorem negative_rank_carrier_chart (q h D c U W RJ k r bound : V)
    (H K T v7 : DiffRing V)
    (hh : 0<h) (hD : 0<D) (hc : 0<c)
    (hq : h+1=q) (hU : 1≤U) (hW : 1≤W)
    (hDc : IsCoprime (ι D : DiffRing V) (ι c))
    (hDh : IsCoprime (ι D : DiffRing V) (ι h))
    (hch : IsCoprime (ι c : DiffRing V) (ι h))
    (hUD : IsCoprime (ι U : DiffRing V) (ι D))
    (hUc : IsCoprime (ι U : DiffRing V) (ι c))
    (hWh : IsCoprime (ι W : DiffRing V) (ι h))
    (hK : H ∣ K) :
    ∃ N B : V, bound<N ∧ 1≤B ∧
      let C := q*h+N
      let R : DiffRing V := ι RJ-ι U*ι N
      let e : DiffRing V := ι k-R-1
      R<0 ∧ q≤1+C ∧
      (ι D : DiffRing V) ∣ e ∧
      (ι c : DiffRing V) ∣ R+ι r ∧
      (ι h : DiffRing V) ∣ ι B ∧
      (ι B : DiffRing V)=ι W*ι C-1 ∧
      (ι h : DiffRing V)*ι D*H ∣
        ι h*ι D*(H*(v7-T^2*ι B)+K)-H*(ι D*ι B+ι h*e) := by
  obtain ⟨N,B,hN,hB1,hR,hguard,he,hr,hB,hBdef⟩ :=
    negative_rank_chart q h D c U W RJ k r bound hh hD hc hq hU hW
      hDc hDh hch hUD hUc hWh
  refine ⟨N,B,hN,hB1,hR,hguard,he,hr,hB,hBdef,?_⟩
  exact carrier_divisibility (ι h) (ι D) H (ι B) (ι k-(ι RJ-ι U*ι N)-1)
    K T v7 hB he hK
end Model

#print axioms Trace74RankCarrierCRT.carrier_divisibility
#print axioms Trace74RankCarrierCRT.negative_rank_carrier_chart
end Trace74RankCarrierCRT
