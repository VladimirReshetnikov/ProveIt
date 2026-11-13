import Direct80RankMain

/-! Conditional rank equality; no assumed rank positivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80RankEquality
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open TenPositive80Graph TenPositive80Factors TenPositive80ResidueBinding TenPositive80RankMain
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sign_eq_without_rank_pos (c R r : V) (hr : 0<r)
    (hrsize : 2*r<c) (hRsize : 2*R<c) (hs : SignMod c R r) : R=r := by
  have hc : 0<c := lt_of_le_of_lt (by simp : (0:V)≤2*r) hrsize
  have hrle : r≤2*r := by simpa only [two_mul] using (show r≤r+r by simp)
  have hrlt : r<c := lt_of_le_of_lt hrle hrsize
  have hRpos : 0<R := by
    apply pos_iff_ne_zero.mpr
    intro hz
    rw [hz] at hs
    rcases hs with hs|hs
    · rw [zero_mod,mod_eq_self_of_lt hrlt] at hs
      exact (ne_of_gt hr) hs.symm
    · rw [zero_add,mod_eq_self_of_lt hrlt] at hs
      exact (ne_of_gt hr) hs
  exact sign_eq_of_half hRpos hr hRsize hrsize hs

/-- The size premise is deliberately explicit; it is not an established mask bound. -/
theorem graph_rank_equality_of_small (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v)
    (hsmall : ∀ rp rn : V,
      (rExpr (integerPorts p)).evalRing (fun j => ι (v j))=ι rp-ι rn →
        2*absdiff rp rn<c p v) :
    ∃ r rp rn : V, 0<r ∧ r%2=1 ∧ c p v=ycoord r (A p v-1) ∧
      (rExpr (integerPorts p)).evalRing (fun j => ι (v j))=ι rp-ι rn ∧
      absdiff rp rn=r := by
  obtain ⟨r,rp,rn,hr,hodd,hc,hrank,hres⟩ := graph_rank_main_congruence p v hb hv hz
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
  have hrsize : 2*r<c p v := by rw [hc]; exact twice_index_lt_y (A p v-1) r hr3
  exact ⟨r,rp,rn,hr,hodd,hc,hrank,sign_eq_without_rank_pos _ _ _ hr hrsize (hsmall rp rn hrank) hres⟩

#print axioms TenPositive80RankEquality.graph_rank_equality_of_small
end TenPositive80RankEquality
