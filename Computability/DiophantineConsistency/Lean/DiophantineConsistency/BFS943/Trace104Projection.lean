import DiophantineConsistency.BFS943.Trace104Transport
import DiophantineConsistency.BFS943.Trace104NormRank
import DiophantineConsistency.BFS943.Trace104NormOffset
import DiophantineConsistency.BFS943.Trace75Projection
import DiophantineConsistency.BFS943.Direct80ProjectionProduct

/-! # Whole-product projection for the 104/174 core

At a positive core zero (with `H ∣ K`, the unit factor `N = 0` of the
literal), the whole-product projection needs no carrier argument: `H ∣ K`
gives `H ∣ (6 h X) K` directly (the multiplier `6 h X` is kept so that
`Trace104GraphPower` is the 87 proof verbatim), and `graph_entire_product` is
the whole-product projection. This is package 184's step "the exact unit
equation `N = 0` gives `H ∣ K`"; no coprimality of `q` and `H` is used.
Also `zero_norm_data` (norm value, mask, first-index residue) and
`zero_alignment` (`2 n = R + 1`, `Trace104NormOffset`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace104Projection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace104
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery
open Trace104Factors Trace104NormRank

theorem cancel_pow {R : Type*} [CommRing R] (m t x : R) :
    ∀ n : ℕ, m*t-1∣m^n*x → m*t-1∣x
  | 0, h => by simpa using h
  | n+1, h => by
    apply cancel_pow m t x n
    apply Trace75Projection.cancel_base m t (m^n*x)
    have he : m^(n+1)*x=m*(m^n*x) := by ring
    rwa [he] at h

/-- The norm-layer hypotheses at a positive zero: the norm value at the
actual carrier, the mask and the first-index residue `2 n ≡ R + 1 (mod q⁴)`. -/
theorem zero_norm_data (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : valueC (ports p) (fun j => ι (v j)) = 0)
    (hHK : (regs (ports p) (fun j => ι (v j))).H∣(regs (ports p) (fun j => ι (v j))).K) :
    TenPositiveTrace76.normValue (regs (ports p) (fun j => ι (v j)))
        (regs (ports p) (fun j => ι (v j))).Z = 0 ∧
      v 1+v 2<q p v ∧
      ∃ n : V, 0<n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
        (ι (q p v):DiffRing V)^4 ∣ ι (2*n)-ι (rankNat p v+1) := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨_z,_tau,_f,_y,_,_,_,_,_,_,_,hm,n,hn,hny,_,_,hres⟩ :=
    Trace104Transport.graph_zero_data p v hb hv hz hHK
  exact ⟨hz,hm,n,hn,hny,hres⟩

/-- The first-index alignment at a positive zero (`Trace104NormOffset`). -/
theorem zero_alignment (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : valueC (ports p) (fun j => ι (v j)) = 0)
    (hHK : (regs (ports p) (fun j => ι (v j))).H∣(regs (ports p) (fun j => ι (v j))).K) :
    ∃ n : V, 0<n ∧ n<rankNat p v ∧ 2*n=rankNat p v+1 ∧
      2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      c p v=ycoord (rankNat p v) (A p v-1) := by
  obtain ⟨hzn,hm,n,hn,hny,hres⟩ := zero_norm_data p v hb31 hv hz hHK
  obtain ⟨hnR,heq,hc⟩ := Trace104NormOffset.graph_first_main_alignment p v _ n hb31 hl hh hv hzn hm hny hres
  exact ⟨n,hn,hnR,heq,hny,hc⟩

theorem graph_projection_divisibility (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : valueC (ports p) (fun j => ι (v j)) = 0)
    (hHK : (regs (ports p) (fun j => ι (v j))).H∣(regs (ports p) (fun j => ι (v j))).K) :
    let rr := regs (ports p) (fun j => ι (v j))
    rr.H∣(6*rr.h*rr.X)*rr.K := by
  exact dvd_mul_of_dvd_right hHK _

theorem graph_entire_product (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : valueC (ports p) (fun j => ι (v j)) = 0)
    (hHK : (regs (ports p) (fun j => ι (v j))).H∣(regs (ports p) (fun j => ι (v j))).K) :
    let rr := regs (ports p) (fun j => ι (v j))
    rr.H∣(6*rr.h*rr.X)*(rr.X-ι (Exp.exp (rankNat p v)))*
      (ι (Exp.exp (rankNat p v))*rr.X+1) := by
  obtain ⟨hzn,hm,_⟩ := Trace104Projection.zero_norm_data p v hb31 hv hz hHK
  let rr := regs (ports p) (fun j => ι (v j))
  let a : V := A p v-1
  let R : V := rankNat p v
  let C : V := c p v
  let d : V := xcoord R a
  let T : V := Exp.exp R
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (by norm_num) (hv 6)
  have hx : 0<X p v := mul_pos hq (hv 5)
  have hA : 0<A p v := add_pos (mul_pos hx hy) hy
  have ha1 : a+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hAeval : rr.Am1=ι (A p v) := by
    dsimp [rr,A,X,Y,q,b,ports]
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,map_mul,map_add,map_one,map_natCast,map_ofNat] <;> ring
  have hCeval : rr.c=ι C := by
    dsimp [rr,C,c,k,X,Y,q,b,ports]
    simp only [c_def,k_def,q_def,h_def,ports,map_mul,map_add,map_one,map_natCast]
  have ha : (ι a:DiffRing V)+1=rr.Am1 := by
    rw [hAeval,←map_one (ι : V →+* DiffRing V),←map_add,ha1]
  have hH : rr.H=4*(ι a:DiffRing V)+3 := by
    rw [show rr.H=4*rr.Am1-1 by dsimp [rr]; rw [H_def]]
    rw [←ha]
    ring
  obtain ⟨_heval,_hlo,_hodd,hc,_hwindow⟩ := graph_rank_exact p v _ hb31 hl hh hv hzn hm
  change C=ycoord R a at hc
  obtain ⟨z,hd⟩ := projection_quotient a R
  change d=T+a*ycoord R a+(4*a+3)*z at hd
  rw [←hc] at hd
  have hn : d*d=1+ArithmeticPellRecurrence.delta a*C*C := by
    dsimp [d]
    rw [hc]
    exact norm R a
  have hdR := congrArg (fun x : V => (ι x:DiffRing V)) hd
  have hnR := congrArg (fun x : V => (ι x:DiffRing V)) hn
  simp only [map_add,map_mul,map_one,map_ofNat] at hdR hnR
  have hnorm : (ι d:DiffRing V)*ι d=1+
      ((ι a:DiffRing V)*ι a+(4*ι a+3))*ι C*ι C := by
    have hdelta : (ι (ArithmeticPellRecurrence.delta a):DiffRing V)=
        (ι a:DiffRing V)*ι a+(4*ι a+3) := by
      simp only [ArithmeticPellRecurrence.delta,map_mul,map_add,map_one,map_ofNat]
      ring
    rw [hdelta] at hnR
    exact hnR
  have hK : rr.K=(4*(ι a:DiffRing V)+3)*rr.X*ι C-
      2*(rr.X*rr.X+2*ι a*rr.X*ι C-1) := by
    rw [show rr.K=rr.X*(3*rr.c-2*rr.X)+2 by dsimp [rr]; rw [K_def],hCeval]
    ring
  have hdiv := graph_projection_divisibility p v hb hv hz hHK
  change rr.H∣(6*rr.h*rr.X)*rr.K at hdiv
  rw [hH,hK] at hdiv
  have hdR' : (ι d:DiffRing V)=ι T+ι a*ι C+(4*ι a+3)*ι z := by
    exact hdR
  have hproduct := Direct80ProjectionProduct.entire_product (ι a:DiffRing V) (ι C) (ι d)
    (ι T) rr.X (6*rr.h*rr.X) (ι z) hdR' hnorm hdiv
  change rr.H∣(6*rr.h*rr.X)*(rr.X-ι T)*(ι T*rr.X+1)
  rwa [hH]

#print axioms Trace104Projection.graph_projection_divisibility
#print axioms Trace104Projection.graph_entire_product
end Trace104Projection
