import Trace74NegativeRankTuple
import Trace74RankCRTChart

/-! Construct an actual updated chart tuple from explicit CRT certificates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CRTNaturalTuple
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing Trace74ChartAssembly
open Trace74NegativeRankTuple Trace74RankCRTChart
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Explicit parameter bindings and Bézout certificates yield an internal
natural magnitude whose updated, casted chart has divisible carrier. -/
theorem exists_updated_carrier (p : Fin 4 → V) (v : Fin 10 → V)
    (q h D c U W RJ k r bound : V)
    (hh : 0<h) (hD : 0<D) (hc : 0<c)
    (hq : h+1=q) (hU : 1≤U) (hW : 1≤W)
    (hh0 : h=p 0*v 0)
    (hDshape : D=(v 5*q)*((q*q*q)*v 6))
    (hWshape : W=p 1+v 5)
    (hRJshape : RJ=(p 2+q*p 3)*v 0)
    (hkshape : k=v 8+v 9)
    (hUcast : (ι U : DiffRing V)=ι q*ι q-1)
    (hDc : IsCoprime (ι D : DiffRing V) (ι c))
    (hDh : IsCoprime (ι D : DiffRing V) (ι h))
    (hch : IsCoprime (ι c : DiffRing V) (ι h))
    (hUD : IsCoprime (ι U : DiffRing V) (ι D))
    (hUc : IsCoprime (ι U : DiffRing V) (ι c))
    (hWh : IsCoprime (ι W : DiffRing V) (ι h))
    (hK : let P := fun i => (ι (p i) : DiffRing V);
      let V₀ := fun i => (ι (v i) : DiffRing V);
      let Q := P 0*V₀ 0+1; let X := V₀ 5*Q; let Y := (Q*Q*Q)*V₀ 6;
      let C := (V₀ 8+V₀ 9)*Y+V₀ 8; let H := 4*(X*Y+Y)-1;
      H ∣ X*(3*C-2*X)+2) :
    ∃ N : V, bound<N ∧
      let P := fun i => (ι (p i) : DiffRing V)
      let w := Function.update (Function.update v 1 1) 2 (q*h+N)
      (chart P (fun i => ι (w i))).M ∣ (chart P (fun i => ι (w i))).Z := by
  obtain ⟨N,B,hN,hB1,hR,hguard,he,hr,hB,hBdef⟩ :=
    negative_rank_chart q h D c U W RJ k r bound hh hD hc hq hU hW
      hDc hDh hch hUD hUc hWh
  let P := fun i => (ι (p i) : DiffRing V)
  let V₀ := fun i => (ι (v i) : DiffRing V)
  have hp0 : P 0*V₀ 0=ι h := by dsimp [P,V₀]; rw [hh0,map_mul]
  have hq0 : P 0*V₀ 0+1=ι q := by
    rw [hp0]
    simpa only [map_add,map_one] using congrArg ι hq
  have hw0 : P 1+V₀ 5=ι W := by dsimp [P,V₀]; rw [hWshape,map_add]
  have hd0 : (V₀ 5*ι q)*((ι q*ι q*ι q)*V₀ 6)=ι D := by
    dsimp [V₀]; rw [hDshape]; simp only [map_mul]
  have hr0 : (P 2+ι q*P 3)*V₀ 0=ι RJ := by
    dsimp [P,V₀]; rw [hRJshape]; simp only [map_mul,map_add]
  have hk0 : V₀ 8+V₀ 9=ι k := by dsimp [V₀]; rw [hkshape,map_add]
  have hb' : (ι h : DiffRing V) ∣ ι W*(ι q*ι h+ι N)-1 := by
    have hs : (ι B : DiffRing V)=ι W*(ι q*ι h+ι N)-1 := by
      simpa only [map_add,map_mul] using hBdef
    rw [←hs]
    exact hB
  have hrings : let Q := P 0*V₀ 0+1
      let w := Function.update (Function.update V₀ 1 1) 2 (Q*(P 0*V₀ 0)+ι N)
      (chart P w).M ∣ (chart P w).Z := by
    apply updated_carrier P V₀ (ι N)
    · dsimp only
      rw [hq0,hp0,hw0]
      exact hb'
    · dsimp only
      rw [hq0,hd0,hr0,hk0,←hUcast]
      exact he
    · exact hK
  have hc0 : (ι (q*h+N) : DiffRing V)=
      (P 0*V₀ 0+1)*(P 0*V₀ 0)+ι N := by
    rw [hq0,hp0]
    simp only [map_add,map_mul]
  have hw : (fun i => (ι ((Function.update (Function.update v 1 1) 2 (q*h+N)) i) : DiffRing V)) =
      Function.update (Function.update V₀ 1 1) 2 ((P 0*V₀ 0+1)*(P 0*V₀ 0)+ι N) := by
    funext i
    by_cases hi2 : i=2
    · subst i; simp [hc0]
    · by_cases hi1 : i=1
      · subst i; simp
      · simp [hi2,hi1,V₀]
  refine ⟨N,hN,?_⟩
  change (chart P (fun i => ι ((Function.update (Function.update v 1 1) 2 (q*h+N)) i))).M ∣
    (chart P (fun i => ι ((Function.update (Function.update v 1 1) 2 (q*h+N)) i))).Z
  rw [hw]
  exact hrings

#print axioms Trace74CRTNaturalTuple.exists_updated_carrier
end Trace74CRTNaturalTuple
