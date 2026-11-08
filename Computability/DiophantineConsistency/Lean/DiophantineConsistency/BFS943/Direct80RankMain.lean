import DiophantineConsistency.BFS943.PellRankReduction
import DiophantineConsistency.BFS943.Direct80MainNorm
import DiophantineConsistency.BFS943.SignedRankIndex
import DiophantineConsistency.BFS943.Direct80ResidueBinding
import DiophantineConsistency.BFS943.Direct80Adjacent
import DiophantineConsistency.ArithmeticPellHalfIndex

/-! Graph-specific strong and odd auxiliary Pell indices; no all-index fold. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80RankMain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPellRecurrence ArithmeticPellClassification ArithmeticPellResidueClasses ArithmeticPellHalfIndex
open TenPositive80Graph TenPositive80Factors TenPositive80Adjacent TenPositive80ResidueBinding TenPositiveSignedRankIndex
open TenPositive80MainNorm TenPositivePellRankReduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Strong index and odd auxiliary index, including the signed modular
transfer. This does not yet establish c as a Pell ordinate. -/
theorem graph_rank_index (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
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
      SignMod F V0 (ycoord (2*h+1) (A0-1)) ∧
      SignMod F (c p v) (ycoord (2*h+1) (A0-1)) ∧
      ∃ rp rn : V, (rExpr (integerPorts p)).evalRing (fun j => ι (v j)) = ι rp-ι rn ∧
        SignMod (c p v) (absdiff rp rn) (2*h+1) := by
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
  obtain ⟨tau,f,V0,Z0,y,htau,hf,hVp,hy,ht,hf2,hV,hZ,hZeq,haux⟩ := graph_adjacent p v hb hv hz
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
  have hcpos : 0<c p v := by
    have hsquare : 0<c p v*c p v := pos_of_mul_pos_right
      (show 0<v 3*(c p v*c p v) from hU) (by simp)
    exact pos_of_mul_pos_left hsquare (by simp)
  have hcI : c p v∣I := dvd_trans (dvd_mul_right (c p v) (c p v)) hc
  let rank : DiffRing V := (rExpr (integerPorts p)).evalRing (fun j => ι (v j))
  let x : DiffRing V := (graph (integerPorts p)).v.evalRing (fun j => ι (v j))
  have hx : x=ι (F*F)*(ι (v 4*c p v)-rank)-ι (c p v) := by
    dsimp [x,rank]
    rw [v_shape]
    simp only [Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_add,Expr.evalRing_var,
      Expr.evalRing_ofNat,Nat.cast_one,Nat.cast_ofNat]
    rw [a_eval,delta_eval,U_eval,E_eval,c_eval]
    dsimp [F,a]
    simp only [map_mul,map_add,map_one,map_ofNat]
    ring
  have haux : xcoord (2*h+1) (D*I-2)=(D*I)*V0 := by
    simpa only [←hs] using hsx
  have hrank := signed_rank_index (c p v) F D I (v 4) V0 h x rank hcpos hJ2 hcI hstrong hx hV haux
  have hg := graph_signed_residue p v V0 hV
  have htarget : SignMod F (c p v) (ycoord (2*h+1) (A0-1)) :=
    sign_trans hF (sign_symm hg) htransfer
  refine ⟨tau,f,V0,y,I,j,h,htau,hf,hVp,hy,hI,hj,ht,hf2,rfl,hc,hjx,hjy,?_,?_,htransfer,htarget,hrank⟩
  · simpa only [←hs] using hsx
  · simpa only [←hs] using hsy




/-- The actual graph rank magnitude is signed-congruent to its odd main index. -/
theorem graph_rank_main_congruence (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ r rp rn : V, 0<r ∧ r%2=1 ∧ c p v=ycoord r (A p v-1) ∧
      (rExpr (integerPorts p)).evalRing (fun j => ι (v j))=ι rp-ι rn ∧
      SignMod (c p v) (absdiff rp rn) r := by
  obtain ⟨r,j0,d,I0,hr,_hrj,hodd,_hj,_hd,_hI,_hdx,hc,_hnorm,_hjx,_hjy,_hdiv⟩ :=
    graph_main_norm p v hb hv hz
  obtain ⟨_tau,_f,_V0,_y,I,j,h,_htau,_hf,_hV,_hy,_hI2,hj,_ht,_hf2,_hIeq,hdiv,
    hjx,hjy,_hauxx,_hauxy,_htransfer,htarget,rp,rn,hrank,hRmod⟩ := graph_rank_index p v hb hv hz
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hCgt : 1<c p v := lt_of_le_of_lt (pos_iff_one_le.mp (mul_pos hk hY))
    (show k v*Y p v<k v*Y p v+v 8 from lt_add_of_pos_right _ (hv 8))
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
  have hdiv' : c p v*c p v∣ycoord j (A p v-1) := by rwa [hjy]
  have htarget' : SignMod (xcoord j (A p v-1)) (c p v) (ycoord (2*h+1) (A p v-1)) := by
    rwa [hjx]
  have hres := rank_to_main_index j (2*h+1) (A p v-1) (c p v) r (absdiff rp rn)
    hj hr3 hc hdiv' htarget' hRmod
  exact ⟨r,rp,rn,hr,hodd,hc,hrank,hres⟩

#print axioms TenPositive80RankMain.graph_rank_main_congruence
end TenPositive80RankMain
