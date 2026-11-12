import DiophantineConsistency.Compact44.P72Root

/-! Source-only proposal: graph-independent positive first-root replacement.
The four other residuals are fixed parameters; neither candidate graph is
imported or connected here. No Lean elaboration or compilation is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.DirectFirstRootModelDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticSignedPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Ring-shaped five-residual sum, with the same grouping as the drafts. -/
def fiveSquares (a b c d e : DiffRing V) : DiffRing V :=
  (a*a+b*b)+(c*c+d*d)+e*e

/-- Proposed generic extraction for five squares; no graph interpretation. -/
theorem fiveSquares_eq_zero_iff (a b c d e : DiffRing V) :
    fiveSquares a b c d e = 0 ↔
      a=0 ∧ b=0 ∧ c=0 ∧ d=0 ∧ e=0 := by
  constructor
  · intro h
    have ha := sq_nonneg a
    have hb := sq_nonneg b
    have hc := sq_nonneg c
    have hd := sq_nonneg d
    have he := sq_nonneg e
    have ha0 : a*a=0 := by dsimp [fiveSquares] at h; nlinarith
    have hb0 : b*b=0 := by dsimp [fiveSquares] at h; nlinarith
    have hc0 : c*c=0 := by dsimp [fiveSquares] at h; nlinarith
    have hd0 : d*d=0 := by dsimp [fiveSquares] at h; nlinarith
    have he0 : e*e=0 := by dsimp [fiveSquares] at h; nlinarith
    exact ⟨mul_self_eq_zero.mp ha0, mul_self_eq_zero.mp hb0,
      mul_self_eq_zero.mp hc0, mul_self_eq_zero.mp hd0, mul_self_eq_zero.mp he0⟩
  · rintro ⟨rfl,rfl,rfl,rfl,rfl⟩
    simp [fiveSquares]

/-- Cancelling a positive natural scale and taking the signed magnitude gives
 a positive root. The scaled equality is an explicit difference-ring premise. -/
theorem root_of_scaled_residual (M P N D : V) (hM : 0<M) (hD : 0<D)
    (h : (ι M*ι M)*((ι P-ι N)*(ι P-ι N)-ι D)=0) :
    0<magnitude (P,N) ∧ magnitude (P,N)*magnitude (P,N)=D := by
  have hM0 : ι M ≠ (0 : DiffRing V) := by
    intro he
    have he' : ι M=ι (0:V) := by simpa only [map_zero] using he
    exact (ne_of_gt hM) (ι_injective he')
  have hM2 : ι M*ι M ≠ (0 : DiffRing V) := mul_ne_zero hM0 hM0
  have hr : (ι P-ι N)*(ι P-ι N)-ι D=0 := (mul_eq_zero.mp h).resolve_left hM2
  have hs : ι (magnitude (P,N))*ι (magnitude (P,N))=ι D := by
    rw [P72Root.ι_magnitude_sq]
    exact sub_eq_zero.mp hr
  have hsq : magnitude (P,N)*magnitude (P,N)=D := by
    apply ι_injective
    simpa only [map_mul] using hs
  have hpositive : 0<magnitude (P,N) :=
    pos_of_mul_pos_left (by rw [hsq]; exact hD) (by simp)
  exact ⟨hpositive,hsq⟩

/-- A positive direct root supplies a positive old first coordinate using
 the negative root branch. No sign for the old difference is presumed. -/
theorem scaled_residual_of_root (M P D tau : V) (htau : 0<tau)
    (hsq : tau*tau=D) :
    0<P+tau ∧ (ι M*ι M)*((ι P-ι (P+tau))*(ι P-ι (P+tau))-ι D)=0 := by
  have hp : 0<P+tau := lt_of_lt_of_le htau (by simp)
  have ht : ι tau*ι tau=ι D := by
    have h := congrArg (ι : V →+* DiffRing V) hsq
    simpa only [map_mul] using h
  have he : (ι P-ι (P+tau))*(ι P-ι (P+tau))=ι D := by
    rw [map_add]
    calc
      (ι P-(ι P+ι tau))*(ι P-(ι P+ι tau))=ι tau*ι tau := by ring
      _=ι D := ht
  refine ⟨hp,?_⟩
  rw [he,sub_self,mul_zero]

/-- Proposed existential bridge for a scaled first residual and a direct root.
 The other four ring residuals are fixed and independent of the changed
 coordinate. This is a fact-level statement, not a theorem about either graph. -/
theorem positive_first_zero_iff (M P D : V) (b c d e : DiffRing V)
    (hM : 0<M) (hD : 0<D) :
    (∃ N : V, 0<N ∧ fiveSquares
      ((ι M*ι M)*((ι P-ι N)*(ι P-ι N)-ι D)) b c d e=0) ↔
    (∃ tau : V, 0<tau ∧ fiveSquares (ι tau*ι tau-ι D) b c d e=0) := by
  constructor
  · rintro ⟨N,hN,hzero⟩
    rcases (fiveSquares_eq_zero_iff _ _ _ _ _).mp hzero with ⟨ha,hb,hc,hd,he⟩
    obtain ⟨htau,hsq⟩ := root_of_scaled_residual M P N D hM hD ha
    refine ⟨magnitude (P,N),htau,(fiveSquares_eq_zero_iff _ _ _ _ _).mpr ?_⟩
    refine ⟨?_,hb,hc,hd,he⟩
    have hs : ι (magnitude (P,N))*ι (magnitude (P,N))=ι D := by
      have h := congrArg (ι : V →+* DiffRing V) hsq
      simpa only [map_mul] using h
    exact sub_eq_zero.mpr hs
  · rintro ⟨tau,htau,hzero⟩
    rcases (fiveSquares_eq_zero_iff _ _ _ _ _).mp hzero with ⟨ha,hb,hc,hd,he⟩
    have hs : tau*tau=D := by
      apply ι_injective
      simpa only [map_mul] using (sub_eq_zero.mp ha)
    obtain ⟨hN,hfirst⟩ := scaled_residual_of_root M P D tau htau hs
    exact ⟨P+tau,hN,(fiveSquares_eq_zero_iff _ _ _ _ _).mpr ⟨hfirst,hb,hc,hd,he⟩⟩

end DiophantineConsistency.DirectFirstRootModelDraft

#print axioms DiophantineConsistency.DirectFirstRootModelDraft.fiveSquares_eq_zero_iff
#print axioms DiophantineConsistency.DirectFirstRootModelDraft.root_of_scaled_residual
#print axioms DiophantineConsistency.DirectFirstRootModelDraft.scaled_residual_of_root
#print axioms DiophantineConsistency.DirectFirstRootModelDraft.positive_first_zero_iff
