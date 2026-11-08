import DiophantineConsistency.BFS943.Trace104NormFold
import DiophantineConsistency.BFS943.Direct80IndexOne

/-! # First index at least two, radix size and positive `K` at an arbitrary carrier (104/174)

`Trace75Index`, `Trace75Size` and `Trace75Kpos` restated for a positive zero
of `normValue (regs …) Z` at an arbitrary carrier value `Z`; the proofs are
those of the 75 modules, routed through `Trace104NormFold`. Here `q⁴ ≤ v`
fails (`v = q³ w s²`), so `graph_rank_size` keeps only `8 v + 4 ≤ k`; the
bound `2 q⁴ < c` moves to `Trace104NormRank.two_q4_lt_c` (main index `≥ 3`).

Constant-dilation copy of `TraceNormKpos` (from the chart-q1 copy `Trace80NormKpos`) for the 104/174
registers `TenPositiveTrace104.regs` (`X = q w`, register `Y = 210 s`, strip
`c = k s + η`); names `Trace75*`/`TraceNorm*` below refer to the q3 originals.
Beyond `X = q w` and `Y = 210 s` (positivity lines only), only the strip lines differ
from `Trace80NormKpos`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace104NormKpos
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace104 TenPositiveTrace76
open ArithmeticPellRecurrence
open Trace104Factors Trace104Residue Trace104NormFold
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_index_ge_two (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V) (n : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0)
    (hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v) : 2≤n := by
  have hkpos : 0<k v := add_pos (hv 8) (hv 9)
  have hn : 0<n := pos_iff_ne_zero.mpr (by
    intro hn0
    apply ne_of_gt hkpos
    simpa [hn0] using hcoord.symm)
  obtain ⟨m,j,I,_,_,_,_,_,hc,_,_,_⟩ := graph_odd_ordinate p v Z hb hv hz
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (by norm_num) (hv 6)
  have hY : 1≤Y p v := pos_iff_one_le.mp hy
  have hne : n≠1 := by
    intro h1
    have hy1 : ycoord 1 (2*(firstParam p v-1)+1)=1 := by simpa using y_succ (0:V) _
    have hk : v 8+v 9=2 := by
      rw [h1,hy1] at hcoord
      simpa [k] using hcoord.symm
    have hsY : v 6≤Y p v := le_mul_of_one_le_left (by simp) (by norm_num)
    apply Direct80IndexOne.impossible (v 6) (Y p v) (X p v) (v 8) (v 9) m
      (pos_iff_one_le.mp (hv 6)) hsY (hv 8) (hv 9) hk
    have hA : A p v = Y p v*(X p v+1) := by dsimp [A]; ring
    rw [hA] at hc
    simpa only [c,k] using hc
  have hgt : 1<n := lt_of_le_of_ne (pos_iff_one_le.mp hn) (Ne.symm hne)
  simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp hgt

theorem graph_rank_size (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) :
    8*firstParam p v+4≤k v := by
  obtain ⟨tau,f,n,I,_,_,_,_,_,_,_,hny,_⟩ := first_and_doubled p v Z hb hv hz
  have hn2 := first_index_ge_two p v Z n hb hv hz hny
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (by norm_num) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hy
  have hx : 0<X p v := mul_pos hq (hv 5)
  have hP : 0<P := mul_pos hx (mul_pos hy hy)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hB : B+2=2*P+1 := by
    calc
      B+2=2*(P-1+1)+1 := by dsimp [B]; ring
      _=2*P+1 := by rw [hP1]
  have hy1 : ycoord 1 B=1 := by simpa using y_succ (0:V) B
  have hx1 : xcoord 1 B=B+2 := by simpa using x_succ (0:V) B
  have hy2 : ycoord 2 B=2*(B+2) := by
    calc
      ycoord 2 B=xcoord 1 B+(B+2)*ycoord 1 B := by
        simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) B
      _=2*(B+2) := by rw [hx1,hy1]; ring
  have hklower : 8*P+4≤k v := calc
    8*P+4=2*ycoord 2 B := by rw [hy2,hB]; ring
    _≤2*ycoord n B := mul_le_mul_of_nonneg_left ((ordinate_strictMono B).monotone hn2) (by simp)
    _=k v := hny
  exact hklower

theorem graph_c_above_x (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) : X p v<c p v := by
  have hklower := graph_rank_size p v Z hb hv hz
  let P : V := firstParam p v
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (by norm_num) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hy
  have hXP : X p v≤P := by
    change X p v≤X p v*(Y p v*Y p v)
    exact le_mul_of_one_le_right (by simp) (one_le_mul hY1 hY1)
  have hPk : P<k v := calc
    P≤8*P := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1:V)≤8 by norm_num) (show (0:V)≤P by simp)
    _<8*P+4 := lt_add_of_pos_right _ (by norm_num)
    _≤k v := hklower
  have hkc : k v≤c p v := by
    change k v≤k v*v 6+v 8
    exact le_trans (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 6))) (by simp)
  exact lt_of_lt_of_le (lt_of_le_of_lt hXP hPk) hkc

theorem graph_K_positive (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) :
    0<(regs (ports p) (fun j => ι (v j))).K := by
  have hc := graph_c_above_x p v Z hb hv hz
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hx : 0<X p v := mul_pos hq (hv 5)
  have hxr : (0:DiffRing V)<ι (X p v) := by
    simpa only [map_zero] using (ι_lt_ι.mpr hx)
  have hcr : (ι (X p v):DiffRing V)<ι (c p v) := ι_lt_ι.mpr hc
  have hgap : (0:DiffRing V)<3*ι (c p v)-2*ι (X p v) := by linarith
  have hxeval : (regs (ports p) (fun j => ι (v j))).X=ι (X p v) := by
    simp only [X_def,q_def,h_def,ports,X,q,b,map_mul,map_add,map_one,map_natCast]
  rw [K_def,hxeval,c_eval]
  have hprod := mul_pos hxr hgap
  linarith

#print axioms Trace104NormKpos.graph_K_positive
end Trace104NormKpos
