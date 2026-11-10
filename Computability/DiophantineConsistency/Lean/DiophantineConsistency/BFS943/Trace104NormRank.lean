import DiophantineConsistency.BFS943.Trace104NormKpos
import DiophantineConsistency.BFS943.Trace75Rank
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
import DiophantineConsistency.BFS943.Trace75SignedRank
import DiophantineConsistency.BFS943.PellRankReduction
import DiophantineConsistency.ArithmeticPellFirstIndex

/-! # Rank window and exact main index at an arbitrary carrier

`Trace75JoinedSquare`, `Trace75Rank.graph_rank_window`, `Trace75RankIndex`,
`Trace75MainIndex` and `Trace75RankExact` restated for a positive zero of
`normValue (regs …) Z` at an arbitrary carrier value `Z`, with the one
carrier-dependent input of the 75 chain, the mask `F + α < q` (which the 75
chain takes from `Trace75Transport.graph_transport_and_mask`), made an explicit
hypothesis. The proofs are those of the 75 modules, routed through
`Trace104NormRoots`, `Trace104NormFold` and `Trace104NormKpos`. Every q3-chart circuit
whose output is `normValue (regs p v) Z` for some `Z` can use them once it
has proved its own mask.

Constant-dilation copy of `TraceNormRank` (from the chart-q1 copy `Trace80NormRank`) for the 104/174
registers `TenPositiveTrace104.regs` (`X = q w`, register `Y = 210 s`, strip
`c = k s + η`); names `Trace75*`/`TraceNorm*` below refer to the q3 originals.
Beyond `X = q w` and `Y = 210 s` (positivity lines only), only the strip lines differ
from `Trace80NormRank`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace104NormRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace104 TenPositiveTrace76
open ArithmeticPellRecurrence ArithmeticPellFirstNorm ArithmeticPellClassification
open ArithmeticPellResidueClasses ArithmeticPellHalfIndex TenPositivePellRecovery
open ArithmeticAdaptiveRankWindow2011 TenPositivePellRankReduction
open Trace104Factors Trace104Residue Trace104NormRoots Trace104NormKpos
open Trace75SignedRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `Trace75Rank.rankNat` for the 104 core registers. -/
def rankNat (p : Fin 4 → ℕ) (v : Fin 10 → V) : V :=
  (b p v*(q p v-v 1)+v 2)*(q p v*q p v-1)+((p 2:V)+q p v*(p 3:V))*v 0

theorem rank_eval_of_mask (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hq : 0<q p v) (hmask : v 1+v 2<q p v) :
    (regs (ports p) (fun j => ι (v j))).rank=ι (rankNat p v) := by
  have hqF : v 1≤q p v := le_trans (by simp) (le_of_lt hmask)
  have hqq : 1≤q p v*q p v := pos_iff_one_le.mp (mul_pos hq hq)
  have hd1 : (ι (q p v-v 1):DiffRing V)=ι (q p v)-ι (v 1) := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,tsub_add_cancel_of_le hqF]
  have hd2 : (ι (q p v*q p v-1):DiffRing V)=ι (q p v)*ι (q p v)-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one (ι : V →+* DiffRing V),←map_add,tsub_add_cancel_of_le hqq,map_mul]
  simp only [rankNat,map_add,map_mul,hd1,hd2,map_natCast]
  simp only [rank_def,q_def,h_def,ports,b,q,map_mul,map_add,map_one,map_natCast]


/-- `Trace104NormFold.strong_and_auxiliary_indices_with_graph_residue`, also
exporting the square representative `V² = V0²` (as `Trace75JoinedSquare`). -/
theorem strong_auxiliary_square (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (Z : DiffRing V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) :
    let D := delta p v
    let U0 := U p v
    let E0 := E p v
    let A0 := A p v
    let a := D*U0*U0*E0
    let F := 1+2*a
    ∃ tau f V0 y I j h : V,
      0<tau ∧ 0<f ∧ 0<V0 ∧ 0<y ∧ 0<I ∧ 0<j ∧
      E0=tau*tau ∧ 1+a=f*f ∧ I=2*U0*tau*f ∧ c p v*c p v∣I ∧
      xcoord j (A0-1)=F ∧ ycoord j (A0-1)=I ∧
      xcoord (2*h+1) (D*I-2)=(D*I)*V0 ∧
      ycoord (2*h+1) (D*I-2)=y ∧
      (regs (ports p) (fun j => ι (v j))).V*(regs (ports p) (fun j => ι (v j))).V=ι (V0*V0) ∧
      SignMod F V0 (c p v) ∧
      SignMod F V0 (ycoord (2*h+1) (A0-1)) := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let A0 : V := A p v
  let a : V := D*U0*U0*E0
  let F : V := 1+2*a
  let Q : V := D*(4*a*(1+a))
  obtain ⟨hD,hU,hE,hM⟩ := factors_positive p v hb hv
  have hA : 0<A0 := pos_of_mul_pos_left (by change 0<A0*(A0+2) at hD; exact hD) (by simp)
  have hA1 : A0-1+1=A0 := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hdelta : ArithmeticPellRecurrence.delta (A0-1)=D := by
    unfold ArithmeticPellRecurrence.delta
    have h3 : A0-1+3=(A0-1+1)+2 := by ring
    rw [h3,hA1]
    rfl
  obtain ⟨tau,f,V0,Z0,y,htau,hf,hVp,hy,ht,hf2,hV,hZ,hZeq,haux⟩ := graph_adjacent p v Z hb hv hz
  change E0=tau*tau at ht
  change 1+a=f*f at hf2
  change Q*(V0*V0)=1+(Q-1)*(y*y) at haux
  let I : V := 2*U0*tau*f
  let J : V := D*I
  have hI : 0<I := mul_pos (mul_pos (mul_pos (by simp) hU) htau) hf
  have hD1 : 1≤D := pos_iff_one_le.mp hD
  have hI2 : 2≤I := by
    have hpos : 1≤U0*tau*f := pos_iff_one_le.mp (mul_pos (mul_pos hU htau) hf)
    simpa only [I,mul_assoc,mul_one] using mul_le_mul_of_nonneg_left hpos (by simp : (0:V)≤2)
  have hJ2 : 2≤J := le_trans hI2 (le_mul_of_one_le_left (by simp) hD1)
  have hJ : 0<J := lt_of_lt_of_le (by simp : (0:V)<2) hJ2
  have hF : 0<F := by dsimp [F]; simp
  have hG : E0*(1+a)=(tau*tau)*(f*f) := by rw [ht,hf2]
  have hstrong : F*F=1+D*I*I := by
    calc
      F*F=1+4*a*(1+a) := by dsimp [F]; ring
      _=1+D*(2*U0)*(2*U0)*(E0*(1+a)) := by dsimp [a]; ring
      _=1+D*(2*U0)*(2*U0)*((tau*tau)*(f*f)) := by rw [hG]
      _=1+D*I*I := by dsimp [I]; ring
  have hQ : Q=J*J := by
    calc
      Q=(D*(2*U0))*(D*(2*U0))*(E0*(1+a)) := by dsimp [Q,a]; ring
      _=(D*(2*U0))*(D*(2*U0))*((tau*tau)*(f*f)) := by rw [hG]
      _=J*J := by dsimp [J,I]; ring
  have hc : c p v*c p v∣I := ⟨2*v 3*tau*f,by dsimp [I,U0,U]; ring⟩
  have hstrong' : F*F=1+ArithmeticPellRecurrence.delta (A0-1)*I*I := by rwa [hdelta]
  obtain ⟨j,_,hjx,hjy⟩ := ArithmeticPellClassification.solution_index (A0-1) F I hstrong'
  have hj : 0<j := pos_iff_ne_zero.mpr (by intro hj0; apply (ne_of_gt hI); simpa [hj0] using hjy.symm)
  have hJsub : J-2+2=J := tsub_add_cancel_of_le hJ2
  have hdJ : ArithmeticPellRecurrence.delta (J-2)+1=J*J := by
    calc
      ArithmeticPellRecurrence.delta (J-2)+1=(J-2+2)*(J-2+2) := by unfold ArithmeticPellRecurrence.delta; ring
      _=J*J := by rw [hJsub]
  have hQsub : Q-1=ArithmeticPellRecurrence.delta (J-2) := by rw [hQ,←hdJ]; simp
  have hn : (J*V0)*(J*V0)=1+ArithmeticPellRecurrence.delta (J-2)*y*y := by
    calc
      (J*V0)*(J*V0)=Q*(V0*V0) := by rw [hQ]; ring
      _=1+(Q-1)*(y*y) := haux
      _=1+ArithmeticPellRecurrence.delta (J-2)*y*y := by rw [hQsub]; ring
  obtain ⟨s,_,hsx,hsy⟩ := ArithmeticPellClassification.solution_index (J-2) (J*V0) y hn
  obtain ⟨h,hs⟩ := odd_index_witness (J-2) s (by rw [hJsub,hsx]; exact ⟨V0,rfl⟩)
  have hV0 : V0=oddQuotient h (J-2) := by
    apply mul_left_cancel₀ (ne_of_gt hJ)
    calc
      J*V0=xcoord (2*h+1) (J-2) := by rw [←hs,hsx]
      _=J*oddQuotient h (J-2) := by rw [odd_exact,hJsub]
  have hstrongnorm : J*J+ArithmeticPellRecurrence.delta (A0-1)=
      ArithmeticPellRecurrence.delta (A0-1)*F*F := by
    rw [hdelta]
    calc
      J*J+D=D*(1+D*I*I) := by dsimp [J]; ring
      _=D*(F*F) := by rw [hstrong]
      _=D*F*F := by ring
  have htransfer : SignMod F V0 (ycoord (2*h+1) (A0-1)) := by
    rw [hV0]
    exact quotient_mod_norm (A0-1) J F h hJ2 hF hstrongnorm
  refine ⟨tau,f,V0,y,I,j,h,htau,hf,hVp,hy,hI,hj,ht,hf2,rfl,hc,hjx,hjy,?_,?_,hV,?_,htransfer⟩
  · simpa only [←hs] using hsx
  · simpa only [←hs] using hsy
  · exact graph_signed_residue p v V0 hV

/-- `Trace75MainIndex.graph_main_index` at an arbitrary carrier. -/
theorem graph_main_index (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) :
    ∃ r j I : V, 3≤r ∧ r<j ∧ r%2=1 ∧ 0<j ∧ 0<I ∧
      c p v=ycoord r (A p v-1) ∧ 2*r<c p v ∧
      xcoord j (A p v-1)=1+2*(delta p v*U p v*U p v*E p v) ∧
      ycoord j (A p v-1)=I ∧ c p v*c p v∣I := by
  obtain ⟨r,j,I,hr,hrj,hodd,hj,hI,hc,hjx,hjy,hdiv⟩ := Trace104NormFold.graph_odd_ordinate p v Z hb hv hz
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (by norm_num) (hv 6)
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hCgt : 1<c p v := lt_of_le_of_lt (pos_iff_one_le.mp (mul_pos hk (hv 6)))
    (show k v*v 6<k v*v 6+v 8 from lt_add_of_pos_right _ (hv 8))
  have hr1 : 1<r := by
    by_contra hn
    have hrle : r≤1 := le_of_not_gt hn
    have hrone : r=1 := le_antisymm hrle (pos_iff_one_le.mp hr)
    have hy1 : ycoord 1 (A p v-1)=1 := by simpa using y_succ (0:V) (A p v-1)
    rw [hrone,hy1] at hc
    exact (ne_of_gt hCgt) hc
  have hr2 : 2≤r := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hr1
  have hr2lt : 2<r := by
    rcases lt_or_eq_of_le hr2 with h|h
    · exact h
    · rw [←h] at hodd
      simp at hodd
  have hr3 : 3≤r := by simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp hr2lt
  have hrsize : 2*r<c p v := by rw [hc]; exact twice_index_lt_y (A p v-1) r hr3
  exact ⟨r,j,I,hr3,hrj,hodd,hj,hI,hc,hrsize,hjx,hjy,hdiv⟩


/-- Package 184's size bound (5), `2 q⁴ < c`, from the main index `r ≥ 3` and
the first index `m ≥ 2` alone (the constant dilation gives no `A ≥ q²`). With
`β = A + 1` (the Pell base; `A ≥ 2 q`): if `r ≥ 5`, `c = ψ_β(r) ≥ ψ_β(5) ≥ β⁴`;
if `r = 3`, `c + 1 = 4 β²`, and `m ≥ 3` would give `k = 2 ψ(m) ≥ 2 ψ_β(3) = 2 c`
against `k < c`, so `m = 2` and `k = 8 v + 4` (`v = 44100 X s²`). Then
`4 β² ≤ c + 1 ≤ k (s + 1)` forces `X ≤ 2 s`, and
`c ≥ 4 (210 s X)² ≥ 44100 X⁴ > 2 q⁴`. -/
theorem two_q4_lt_c (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) :
    2*(q p v)^4<c p v := by
  obtain ⟨r,_j,_I,hr3,_,hodd,_,_,hc,_⟩ := graph_main_index p v Z hb hv hz
  obtain ⟨_tau,_f,m,_I',_,_,_,_,_,_,_,hmy,_⟩ := Trace104NormFold.first_and_doubled p v Z hb hv hz
  have hm2 := first_index_ge_two p v Z m hb hv hz hmy
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hX : 0<X p v := mul_pos hq (hv 5)
  have hYp : 0<Y p v := mul_pos (by norm_num) (hv 6)
  have hA : 0<A p v := add_pos (mul_pos hX hYp) hYp
  have ha1 : (A p v-1)+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hβ : (A p v-1)+2=A p v+1 := by rw [show (A p v-1)+2=((A p v-1)+1)+1 by ring,ha1]
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hkc : k v<c p v := lt_of_le_of_lt (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6)) (by simp : (0:V)≤k v))
    (show k v*v 6<k v*v 6+v 8 from lt_add_of_pos_right _ (hv 8))
  -- the first Pell values at the main base `a = A - 1`
  have hy1 : ycoord 1 (A p v-1)=1 := by simpa using y_succ (0:V) (A p v-1)
  have hx1 : xcoord 1 (A p v-1)=(A p v-1)+2 := by simpa using x_succ (0:V) (A p v-1)
  have hy2 : ycoord 2 (A p v-1)=2*((A p v-1)+2) := by
    calc
      ycoord 2 (A p v-1)=xcoord 1 (A p v-1)+((A p v-1)+2)*ycoord 1 (A p v-1) := by
        simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) (A p v-1)
      _=2*((A p v-1)+2) := by rw [hx1,hy1]; ring
  have hx2 : xcoord 2 (A p v-1)+1=2*(((A p v-1)+2)*((A p v-1)+2)) := by
    have h := x_succ (1:V) (A p v-1)
    rw [show (1:V)+1=2 by ring,hx1,hy1] at h
    rw [h]
    unfold ArithmeticPellRecurrence.delta
    ring
  have hy3 : ycoord 3 (A p v-1)+1=4*(((A p v-1)+2)*((A p v-1)+2)) := by
    have h := y_succ (2:V) (A p v-1)
    rw [show (2:V)+1=3 by ring,hy2] at h
    rw [h]
    calc xcoord 2 (A p v-1)+((A p v-1)+2)*(2*((A p v-1)+2))+1
        =(xcoord 2 (A p v-1)+1)+2*(((A p v-1)+2)*((A p v-1)+2)) := by ring
      _=4*(((A p v-1)+2)*((A p v-1)+2)) := by rw [hx2]; ring
  -- `A ≥ 2 q`
  have hqX : q p v≤X p v := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 5))
  have h2q : 2*q p v≤A p v+1 := by
    have h1 : 2*q p v≤X p v*Y p v := by
      calc 2*q p v≤X p v*2 := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hqX (by simp)
        _≤X p v*Y p v := mul_le_mul_of_nonneg_left
            (le_trans (by norm_num : (2:V)≤210*1)
              (mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6)) (by simp))) (by simp)
    have hXYA : X p v*Y p v≤A p v := by
      change X p v*Y p v≤X p v*Y p v+Y p v
      exact le_self_add
    exact le_trans h1 (le_trans hXYA le_self_add)
  rcases lt_or_ge r 5 with hr5|hr5
  · -- `r = 3`
    have hr4 : r≤4 := by
      have h := lt_iff_succ_le.mp hr5
      exact (add_le_add_iff_right (1:V)).mp (by simpa only [show (4:V)+1=5 by ring] using h)
    have hr : r=3 := by
      by_contra hne
      have h3 : 3<r := lt_of_le_of_ne hr3 (Ne.symm hne)
      have h4 : 4≤r := by simpa only [show (3:V)+1=4 by ring] using lt_iff_succ_le.mp h3
      have heq : r=4 := le_antisymm hr4 h4
      rw [heq,show (4:V)=2*2 by norm_num,mod_mul_self_left] at hodd
      exact absurd hodd (by simp)
    rw [hr] at hc
    -- the first index is `2`
    let P : V := firstParam p v
    let B : V := 2*(P-1)+1
    change 2*ycoord m B=k v at hmy
    have hP : 0<P := mul_pos hX (mul_pos hYp hYp)
    have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
    have hXP : X p v+1≤2*X p v := by
      calc
        X p v+1≤X p v+X p v := by
          simpa only [add_comm] using _root_.add_le_add_left (pos_iff_one_le.mp hX) (X p v)
        _=2*X p v := by ring
    have hYY : Y p v≤Y p v*Y p v := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hYp)
    have hA2P : A p v≤2*P := calc
      A p v=Y p v*(X p v+1) := by dsimp [A]; ring
      _≤Y p v*(2*X p v) := mul_le_mul_of_nonneg_left hXP (by simp)
      _≤(Y p v*Y p v)*(2*X p v) := mul_le_mul_of_nonneg_right hYY (by simp)
      _=2*P := by dsimp [P,firstParam]; ring
    have hbase : A p v-1≤B := by
      apply (add_le_add_iff_right (2:V)).mp
      calc
        A p v-1+2=A p v+1 := hβ
        _≤2*P+1 := by simpa only [add_comm] using _root_.add_le_add_right hA2P (1:V)
        _=B+2 := by dsimp [B]; rw [show 2*(P-1)+1+2=2*(P-1+1)+1 by ring,hP1]
    have hm : m=2 := by
      by_contra hne
      have h2 : 2<m := lt_of_le_of_ne hm2 (Ne.symm hne)
      have h3 : 3≤m := by simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp h2
      have hle : c p v≤k v := calc
        c p v=ycoord 3 (A p v-1) := hc
        _≤ycoord 3 B := (ArithmeticPellFirstIndex.base_mono (A p v-1) B hbase 3).2
        _≤ycoord m B := (ordinate_strictMono B).monotone h3
        _≤2*ycoord m B := le_mul_of_one_le_left (by simp) (by simp)
        _=k v := hmy
      exact (not_le_of_gt hkc) hle
    rw [hm] at hmy
    have hyB1 : ycoord 1 B=1 := by simpa using y_succ (0:V) B
    have hxB1 : xcoord 1 B=B+2 := by simpa using x_succ (0:V) B
    have hyB2 : ycoord 2 B=2*(B+2) := by
      calc
        ycoord 2 B=xcoord 1 B+(B+2)*ycoord 1 B := by
          simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) B
        _=2*(B+2) := by rw [hxB1,hyB1]; ring
    have hB2 : B+2=2*P+1 := by dsimp [B]; rw [show 2*(P-1)+1+2=2*(P-1+1)+1 by ring,hP1]
    have hkP : k v=8*P+4 := by rw [←hmy,hyB2,hB2]; ring
    -- `c + 1 ≤ k (s + 1)`
    have hcs : c p v+1≤k v*(v 6+1) := by
      have hlt : c p v<k v*(v 6+1) := by
        change k v*v 6+v 8<k v*(v 6+1)
        have he : v 8<k v := lt_add_of_pos_right _ (hv 9)
        have hs := add_lt_add_of_le_of_lt (le_refl (k v*v 6)) he
        simpa only [mul_add,mul_one] using hs
      exact lt_iff_succ_le.mp hlt
    -- move to the difference ring
    have hsR : (1:DiffRing V)≤ι (v 6) := by
      rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact pos_iff_one_le.mp (hv 6)
    have hXR : (ι (q p v):DiffRing V)≤ι (X p v) := ι_le_ι.mpr hqX
    have hqR : (0:DiffRing V)<ι (q p v) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hq
    have hAeq : (ι (A p v):DiffRing V)=210*ι (v 6)*(ι (X p v)+1) := by
      simp only [A,Y,map_add,map_mul,map_ofNat]; ring
    have hPeq : (ι P:DiffRing V)=44100*ι (X p v)*(ι (v 6)*ι (v 6)) := by
      simp only [P,firstParam,Y,map_mul,map_ofNat]; ring
    have hc4 : (ι (c p v):DiffRing V)+1=4*((ι (A p v)+1)*(ι (A p v)+1)) := by
      have h := congrArg (ι : V →+* DiffRing V) hy3
      rw [hβ,←hc] at h
      simpa only [map_add,map_mul,map_one,map_ofNat] using h
    have hcsR : (ι (c p v):DiffRing V)+1≤(8*ι P+4)*(ι (v 6)+1) := by
      have h := ι_le_ι.mpr hcs
      rw [hkP] at h
      simpa only [map_add,map_mul,map_one,map_ofNat] using h
    set S : DiffRing V := ι (v 6) with hS
    set Xr : DiffRing V := ι (X p v) with hXr
    have hXpos : (0:DiffRing V)≤Xr := ι_nonneg _
    have hX2s : Xr≤2*S := by
      by_contra hn
      have hgt : 2*S+1≤Xr := by
        have h := lt_of_not_ge hn
        have hd : ∀ x : DiffRing V, 0<x → 1≤x := fun x hx =>
          one_le_of_pos (fun z hz => pos_iff_one_le.mp hz) hx
        have := hd (Xr-2*S) (by linarith)
        linarith
      have h1 : 0≤S*S*Xr*(Xr-2*S-1) := mul_nonneg (mul_nonneg (mul_self_nonneg S) hXpos) (by linarith)
      have h2 : S≤S*S := le_mul_of_one_le_left (le_trans zero_le_one hsR) hsR
      have h3 : 0≤S*S*Xr := mul_nonneg (mul_self_nonneg S) hXpos
      have hbig : (352800*Xr*(S*S)+4)*(S+1)<176400*(S*S)*((Xr+1)*(Xr+1)) := by nlinarith
      have hAR : 210*S*(Xr+1)<ι (A p v)+1 := by rw [hAeq]; linarith
      have hA0 : (0:DiffRing V)≤210*S*(Xr+1) :=
        mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one hsR)) (by linarith)
      have hsq : (210*S*(Xr+1))*(210*S*(Xr+1))<(ι (A p v)+1)*(ι (A p v)+1) :=
        mul_self_lt_mul_self hA0 hAR
      rw [hPeq] at hcsR
      nlinarith
    have hS0 : (0:DiffRing V)≤S := le_trans zero_le_one hsR
    have hAR : 210*S*Xr+1≤ι (A p v)+1 := by rw [hAeq]; linarith
    have hA0 : (0:DiffRing V)≤210*S*Xr+1 := by
      have := mul_nonneg (mul_nonneg (show (0:DiffRing V)≤210 by norm_num) hS0) hXpos
      linarith
    have hsq := mul_self_le_mul_self hA0 hAR
    have hXX : Xr*Xr≤(2*S)*(2*S) := mul_self_le_mul_self hXpos hX2s
    have hq4 : (ι (q p v):DiffRing V)^4≤Xr*Xr*(Xr*Xr) := by
      have h1 := mul_self_le_mul_self (le_of_lt hqR) hXR
      have h2 := mul_self_le_mul_self (mul_nonneg (le_of_lt hqR) (le_of_lt hqR)) h1
      rw [show (ι (q p v):DiffRing V)^4=ι (q p v)*ι (q p v)*(ι (q p v)*ι (q p v)) by ring]
      exact h2
    have hX4 : (0:DiffRing V)<Xr*Xr*(Xr*Xr) := by
      have h0 : (0:DiffRing V)<Xr := lt_of_lt_of_le hqR hXR
      exact mul_pos (mul_pos h0 h0) (mul_pos h0 h0)
    have hfin : 2*(ι (q p v):DiffRing V)^4<ι (c p v) := by
      have hXXS : Xr*Xr*(Xr*Xr)≤Xr*Xr*((2*S)*(2*S)) := mul_le_mul_of_nonneg_left hXX (mul_self_nonneg Xr)
      have hSX : (0:DiffRing V)≤S*Xr := mul_nonneg hS0 hXpos
      have hq40 : (0:DiffRing V)≤(ι (q p v))^4 := pow_nonneg (le_of_lt hqR) 4
      nlinarith
    have h := hfin
    rw [←map_pow,←map_ofNat (ι : V →+* DiffRing V) 2,←map_mul] at h
    exact ι_lt_ι.mp h
  · -- `r ≥ 5`
    have hstep : ∀ n : V, ((A p v-1)+2)*ycoord n (A p v-1)≤ycoord (n+1) (A p v-1) := by
      intro n
      rw [y_succ]
      exact le_add_self
    have hy5 : ((A p v-1)+2)*(((A p v-1)+2)*(((A p v-1)+2)*((A p v-1)+2)))≤ycoord 5 (A p v-1) := by
      have h2 := hstep 1
      have h3 := hstep 2
      have h4 := hstep 3
      have h5 := hstep 4
      rw [hy1,mul_one,show (1:V)+1=2 by ring] at h2
      rw [show (2:V)+1=3 by ring] at h3
      rw [show (3:V)+1=4 by ring] at h4
      rw [show (4:V)+1=5 by ring] at h5
      calc ((A p v-1)+2)*(((A p v-1)+2)*(((A p v-1)+2)*((A p v-1)+2)))
          ≤((A p v-1)+2)*(((A p v-1)+2)*(((A p v-1)+2)*ycoord 2 (A p v-1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h2 (by simp)) (by simp)) (by simp)
        _≤((A p v-1)+2)*(((A p v-1)+2)*ycoord 3 (A p v-1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by simp)) (by simp)
        _≤((A p v-1)+2)*ycoord 4 (A p v-1) := mul_le_mul_of_nonneg_left h4 (by simp)
        _≤ycoord 5 (A p v-1) := h5
    have hc5 : ycoord 5 (A p v-1)≤c p v := by
      rw [hc]; exact (ordinate_strictMono (A p v-1)).monotone hr5
    rw [hβ] at hy5
    have hq2 : (2*q p v)*((2*q p v)*((2*q p v)*(2*q p v)))≤
        (A p v+1)*((A p v+1)*((A p v+1)*(A p v+1))) :=
      mul_le_mul h2q (mul_le_mul h2q (mul_le_mul h2q h2q (by simp) (by simp)) (by simp) (by simp))
        (by simp) (by simp)
    have hlt : 2*(q p v)^4<(2*q p v)*((2*q p v)*((2*q p v)*(2*q p v))) := by
      have hq4 : 0<(q p v)^4 := pow_pos hq 4
      calc 2*(q p v)^4<16*(q p v)^4 := mul_lt_mul_of_pos_right (by norm_num) hq4
        _=(2*q p v)*((2*q p v)*((2*q p v)*(2*q p v))) := by ring
    exact lt_of_lt_of_le hlt (le_trans hq2 (le_trans hy5 hc5))

/-- `Trace75Rank.graph_rank_window` with the mask as a hypothesis. -/
theorem graph_rank_window (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0)
    (hm : v 1+v 2<q p v) :
    (regs (ports p) (fun j => ι (v j))).rank=ι (rankNat p v) ∧
      v 1+v 2<q p v ∧ 3*q p v<rankNat p v ∧
      rankNat p v+q p v^3+q p v+1≤q p v^4 ∧ 2*rankNat p v<c p v := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have he := rank_eval_of_mask p v hq hm
  have hwin := scalar_rank_window (q p v) (p 0:V) (p 2:V) (p 3:V) (v 0) (v 1) (v 2)
    hb (hv 0) (hv 1) (hv 2) hl hh rfl hm
  have hbq : q p v-1=b p v := by dsimp [q]; simp
  have hR : ((q p v-1)*(q p v-v 1)+v 2)*(q p v^2-1)+
      ((p 2:V)+q p v*(p 3:V))*v 0=rankNat p v := by
    rw [hbq]
    dsimp [rankNat]
    ring_nf
  rw [hR] at hwin
  have hJ1 : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hb31' : (31:V)≤b p v := le_trans hb31 (by
    change (p 0:V)≤(p 0:V)*v 0
    exact le_mul_of_one_le_right (by simp) hJ1)
  have hq32 : (32:V)≤q p v := by
    simpa only [q,show (32:V)=31+1 by ring,add_comm] using _root_.add_le_add_right hb31' (1:V)
  have hq4 : (4:V)≤q p v := le_trans (by norm_num) hq32
  have hq2 : (2:V)≤q p v := le_trans (by norm_num) hq32
  have hq1 : (1:V)≤q p v := le_trans (by norm_num) hq32
  have hG : 1≤b p v*(q p v-v 1)+v 2 := pos_iff_one_le.mp
    (add_pos_of_nonneg_of_pos (by simp) (hv 2))
  have hRlower : q p v*q p v-1≤rankNat p v := calc
    q p v*q p v-1≤(b p v*(q p v-v 1)+v 2)*(q p v*q p v-1) :=
      le_mul_of_one_le_left (by simp) hG
    _≤rankNat p v := by dsimp [rankNat]; simp
  have hsq : 4*q p v≤q p v*q p v := mul_le_mul_of_nonneg_right hq4 (by simp)
  have hsq1 : 1≤q p v*q p v := one_le_mul hq1 hq1
  have hsmall : 3*q p v+2≤q p v*q p v := calc
    3*q p v+2≤3*q p v+q p v := _root_.add_le_add_right hq2 _
    _=4*q p v := by ring
    _≤q p v*q p v := hsq
  have hsmall' : 3*q p v+1≤q p v*q p v-1 :=
    (le_tsub_iff_right hsq1).mpr (calc
      3*q p v+1+1=3*q p v+2 := by ring
      _≤q p v*q p v := hsmall)
  have hrlo : 3*q p v<rankNat p v := lt_of_lt_of_le (lt_add_one (3*q p v)) (le_trans hsmall' hRlower)
  have hwin' : rankNat p v+(q p v^3+q p v+1)≤q p v^4 := by
    simpa only [add_assoc] using hwin.2
  have hrhi : rankNat p v<q p v^4 := lt_of_lt_of_le (lt_add_of_pos_right _
    (show 0<q p v^3+q p v+1 by simp)) hwin'
  have hc := two_q4_lt_c p v Z hb hv hz
  have hrC : 2*rankNat p v<c p v := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (le_of_lt hrhi) (by simp)) hc
  exact ⟨he,hm,hrlo,hwin.2,hrC⟩

/-- `Trace75RankIndex.graph_rank_auxiliary` with the mask as a hypothesis. -/
theorem graph_rank_auxiliary (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0)
    (hm : v 1+v 2<q p v) :
    let D := delta p v
    let U0 := U p v
    let E0 := E p v
    let A0 := A p v
    let F := 1+2*(D*U0*U0*E0)
    ∃ I j h : V, 0<I ∧ 0<j ∧ c p v*c p v∣I ∧
      xcoord j (A0-1)=F ∧ ycoord j (A0-1)=I ∧
      SignMod F (c p v) (ycoord (2*h+1) (A0-1)) ∧
      SignMod (c p v) (rankNat p v) (2*h+1) := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let a : V := D*U0*U0*E0
  let F : V := 1+2*a
  let C : V := c p v
  let R : V := rankNat p v
  let x : DiffRing V := (regs (ports p) (fun j => ι (v j))).V
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨tau,f,V0,y,I,j,h,htau,hf,hV,hy,hI,hj,ht,hf2,hIeq,hdiv,hjx,hjy,hauxx,hauxy,hVsq,hgc,htransfer⟩ :=
    strong_auxiliary_square p v Z hb hv hz
  have hwindow := graph_rank_window p v Z hb31 hl hh hv hz hm
  have hrank : (regs (ports p) (fun j => ι (v j))).rank=ι R := hwindow.1
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (by norm_num) (hv 6)
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hcpos : 0<C := add_pos (mul_pos hk (hv 6)) (hv 8)
  have hFpos : 0<F := by dsimp [F]; simp
  have hcdiv : C∣2*a := ⟨2*D*(v 3)*(v 3)*C*C*C*E0,by dsimp [a,U0,U,C]; ring⟩
  have hfmod : F%C=(1:V)%C := by
    dsimp [F]
    exact mod_add_remove_right_of_dvd hcdiv hcpos
  have hx : x=ι F*(ι (v 4*C)+ι (0:V)-ι R)-ι C := by
    dsimp [x]
    rw [V_def,b_def,f_eq,a_eq,delta_eval,U_eval,E_eval,Trace104Residue.c_eval,hrank]
    dsimp [F,a,D,U0,E0,C]
    simp only [pow_two,map_mul,map_add,map_one,map_zero,map_ofNat]
    ring
  have hRank : SignMod C V0 R := by
    have hs := rank_residue_of_square C F (v 4) R 0 V0 x hcpos hfmod hx hVsq
    simpa only [absdiff,tsub_zero,zero_tsub,add_zero] using hs
  have hcI : C∣I := dvd_trans (dvd_mul_right C C) hdiv
  have hD : 0<D := (factors_positive p v hb hv).1
  have hU : 0<U0 := (factors_positive p v hb hv).2.1
  have hI2 : 2≤I := by
    have hpos : 1≤U0*tau*f := pos_iff_one_le.mp (mul_pos (mul_pos hU htau) hf)
    rw [hIeq]
    simpa only [mul_assoc,mul_one] using mul_le_mul_of_nonneg_left hpos (by simp : (0:V)≤2)
  have hJ2 : 2≤D*I := le_trans hI2 (le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hD))
  have hJpos : 0<D*I := lt_of_lt_of_le (by simp : (0:V)<2) hJ2
  have hsub : D*I-2+2=D*I := tsub_add_cancel_of_le hJ2
  have hu : V0=oddQuotient h (D*I-2) := by
    apply mul_left_cancel₀ (ne_of_gt hJpos)
    calc
      (D*I)*V0=xcoord (2*h+1) (D*I-2) := hauxx.symm
      _=(D*I)*oddQuotient h (D*I-2) := by rw [odd_exact,hsub]
  have hdJ : C∣D*I := dvd_mul_of_dvd_right hcI D
  have hindex : SignMod C V0 (2*h+1) := by
    rw [hu]
    exact quotient_mod_divisor (D*I) C h hJ2 hcpos hdJ
  have htarget : SignMod F C (ycoord (2*h+1) (A p v-1)) := by
    exact sign_trans hFpos (sign_symm hgc) htransfer
  exact ⟨I,j,h,hI,hj,hdiv,hjx,hjy,htarget,sign_trans hcpos (sign_symm hRank) hindex⟩


/-- `Trace75RankExact.graph_rank_exact` with the mask as a hypothesis. -/
theorem graph_rank_exact (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0)
    (hm : v 1+v 2<q p v) :
    (regs (ports p) (fun j => ι (v j))).rank=ι (rankNat p v) ∧
    3*q p v<rankNat p v ∧ rankNat p v%2=1 ∧
    c p v=ycoord (rankNat p v) (A p v-1) ∧
    rankNat p v+q p v^3+q p v+1≤q p v^4 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨hrank,hmask,hrlo,hrhi,hrC⟩ := graph_rank_window p v Z hb31 hl hh hv hz hm
  obtain ⟨r,j0,I0,hr3,hrj,hodd,hj0,hI0,hc,hrsize,hj0x,hj0y,hdiv0⟩ := graph_main_index p v Z hb hv hz
  obtain ⟨I,j,h,hI,hj,hdiv,hjx,hjy,htarget,hRmod⟩ := graph_rank_auxiliary p v Z hb31 hl hh hv hz hm
  have hdiv' : c p v*c p v∣ycoord j (A p v-1) := by rwa [hjy]
  have htarget' : SignMod (xcoord j (A p v-1)) (c p v) (ycoord (2*h+1) (A p v-1)) := by
    rwa [hjx]
  have hres := rank_to_main_index j (2*h+1) (A p v-1) (c p v) r (rankNat p v)
    hj hr3 hc hdiv' htarget' hRmod
  have hrpos : 0<r := lt_of_lt_of_le (by simp : (0:V)<3) hr3
  have hRpos : 0<rankNat p v := lt_of_le_of_lt (by simp) hrlo
  have heq : rankNat p v=r := sign_eq_of_half hRpos hrpos hrC hrsize hres
  refine ⟨hrank,hrlo,?_,?_,hrhi⟩
  · rwa [heq]
  · rwa [heq]


#print axioms Trace104NormRank.graph_rank_exact
end Trace104NormRank
