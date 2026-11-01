import DiophantineConsistency.AdaptiveGap85CubicCancel
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FourthRootCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85CubicCancel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def fourthC (a : V) : V := 4*(a+2)*(2*((a+1)*(a+3))+1)
def fourthS (a : V) : V := 8*a*a*a*a+64*a*a*a+184*a*a+224*a+97

/-- Either signed fourth-root orientation imposes its corresponding cubic
modulus condition. This theorem assumes the displayed root equation. -/
theorem fourth_root_congruences (X Y q A B : V) (hY : 1≤Y) (hq : q∣Y)
    (hroot :
      (Y*q*q)*fourthS (Y*(X+1))+(4*(Y*(X+1))+3)*B =
        (Y*q*q)*(X+(Y*(X+1))*fourthC (Y*(X+1)))+(4*(Y*(X+1))+3)*A ∨
      (Y*q*q)*fourthS (Y*(X+1))+(Y*q*q)*(X+(Y*(X+1))*fourthC (Y*(X+1)))+
        (4*(Y*(X+1))+3)*A=(4*(Y*(X+1))+3)*B) :
    (27*X)%(4*(Y*(X+1))+3)=(27*16)%(4*(Y*(X+1))+3) ∨
    (27*(16*X+1))%(4*(Y*(X+1))+3)=0 := by
  let a := Y*(X+1)
  let U := Y*q*q
  let H := 4*a+3
  have hH : 0<H := by dsimp [H]; simp
  have hpospoly : fourthS a = a*fourthC a+H*(4*a*a+20*a+27)+16 := by
    dsimp [fourthS,fourthC,H]; ring
  have hnegpoly : 16*(fourthS a+(X+a*fourthC a)) =
      H*(64*a*a*a+400*a*a+804*a+517)+(16*X+1) := by
    dsimp [fourthS,fourthC,H]; ring
  rcases hroot with hpos | hneg
  · left
    change U*fourthS a+H*B=U*(X+a*fourthC a)+H*A at hpos
    have he : U*X+H*A=U*16+H*(U*(4*a*a+20*a+27)+B) := by
      have hh : U*(a*fourthC a)+(U*X+H*A)=
          U*(a*fourthC a)+(U*16+H*(U*(4*a*a+20*a+27)+B)) := by
        calc
          _ = U*(X+a*fourthC a)+H*A := by ring
          _ = U*fourthS a+H*B := hpos.symm
          _ = _ := by rw [hpospoly]; ring
      exact add_left_cancel hh
    have hm : (U*X)%H=(U*16)%H := by
      have hh := congrArg (fun z : V => z%H) he
      simpa only [mod_add_mul' _ _ hH] using hh
    exact cubic_cancel X Y q X 16 hY hq hm
  · right
    change U*fourthS a+U*(X+a*fourthC a)+H*A=H*B at hneg
    have he : U*(16*X+1)+H*(U*(64*a*a*a+400*a*a+804*a+517)+16*A)=H*(16*B) := by
      calc
        _ = U*(H*(64*a*a*a+400*a*a+804*a+517)+(16*X+1))+H*(16*A) := by ring
        _ = U*(16*(fourthS a+(X+a*fourthC a)))+H*(16*A) := by rw [hnegpoly]
        _ = 16*(U*fourthS a+U*(X+a*fourthC a)+H*A) := by ring
        _ = H*(16*B) := by rw [hneg]; ring
    have hz : (H*(16*B))%H=0 := mod_eq_zero_iff_dvd.mpr ⟨16*B,rfl⟩
    have hm : (U*(16*X+1))%H=(U*0)%H := by
      have hh := congrArg (fun z : V => z%H) he
      rw [mod_add_mul' _ _ hH,hz] at hh
      simpa only [mul_zero,zero_mod] using hh
    have hc := cubic_cancel X Y q (16*X+1) 0 hY hq hm
    simpa only [mul_zero,zero_mod] using hc
end DiophantineConsistency.AdaptiveGap85FourthRootCongruence
