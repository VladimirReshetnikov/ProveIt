import RingComparison
import DiophantineConsistency.Compact44.P72Root

/-! Source-only conditional positive model maps. The strict gamma and q-divisibility
hypotheses are NOT derived from graph zeros here. RingComparison and its graph
imports are uncompiled drafts; no Lean or endpoint result is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Conditional84To85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing Ring84To85Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta

/-- The natural 84→85 update. Its gamma difference is justified only
when slot 12 exceeds slot 6. -/
def to85 (beta : V) (v : Fin 14 → V) : Fin 14 → V :=
  Function.update (Function.update v 6 (q beta v*v 6)) 12 (v 12-v 6)

/-- The natural 85→84 update given an explicit q-quotient w. -/
def to84 (v : Fin 14 → V) (w : V) : Fin 14 → V :=
  Function.update (Function.update v 6 w) 12 (v 12+w)

theorem to85_positive (beta : V) (v : Fin 14 → V)
    (hv : ∀ j, 0<v j) (hgamma : v 6<v 12) : ∀ j, 0<to85 beta v j := by
  have hq : 0<q beta v := by dsimp [q]; simp
  intro j
  by_cases hj12 : j=12
  · subst j
    simpa [to85] using tsub_pos_of_lt hgamma
  · by_cases hj6 : j=6
    · subst j
      simpa [to85] using mul_pos hq (hv 6)
    · simpa [to85,hj12,hj6] using hv j

theorem to84_positive (v : Fin 14 → V) (w : V)
    (hv : ∀ j, 0<v j) (hw : 0<w) : ∀ j, 0<to84 v w j := by
  intro j
  by_cases hj12 : j=12
  · subst j
    simpa [to84] using add_pos (hv 12) hw
  · by_cases hj6 : j=6
    · subst j
      simpa [to84] using hw
    · simpa [to84,hj12,hj6] using hv j

/-- Proposed embedding compatibility for the natural 84→85 update. -/
theorem cast_to85 (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hgamma : v 6<v 12) :
    (fun j => ι (to85 beta v j)) = Ring84To85Draft.transform p (fun j => ι (v j)) := by
  have hg : ι (v 12-v 6)=ι (v 12)-ι (v 6) := P72Root.ι_tsub (le_of_lt hgamma)
  funext j
  by_cases hj12 : j=12
  · subst j
    simp [to85,Ring84To85Draft.transform,hg]
  · by_cases hj6 : j=6
    · subst j
      simp [to85,Ring84To85Draft.transform,q,hport,map_add,map_mul,map_one]
    · simp [to85,Ring84To85Draft.transform,hj12,hj6]

/-- Proposed embedding compatibility in the other direction; X=q*w is
an explicit natural equality and no quotient extraction is hidden. -/
theorem cast_to84 (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (w : V)
    (hport : (p 0 : DiffRing V)=ι beta) (hw : v 6=q beta v*w) :
    (fun j => ι (v j)) = Ring84To85Draft.transform p (fun j => ι (to84 v w j)) := by
  funext j
  by_cases hj12 : j=12
  · subst j
    simp [to84,Ring84To85Draft.transform,map_add] <;> ring
  · by_cases hj6 : j=6
    · subst j
      simp [to84,Ring84To85Draft.transform,q,hport,map_add,map_mul,map_one,hw]
    · simp [to84,Ring84To85Draft.transform,hj12,hj6]

/-- Conditional 84→85 positive map. Deriving the strict gamma premise from
an 84 graph zero remains a separate model theorem. -/
theorem map_84_to_85 (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hv : ∀ j, 0<v j)
    (hgamma : v 6<v 12) (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P85QcubeGraph.graph p).output v' := by
  refine ⟨to85 beta v,to85_positive beta v hv hgamma,?_⟩
  apply (internalZero_iff _ _).mpr
  have h := Ring84To85Draft.output_eval p (fun j => ι (v j))
  rw [← cast_to85 p beta v hport hgamma] at h
  rw [h]
  exact (internalZero_iff _ _).mp hz

/-- Conditional 85→84 positive map. Deriving q|X from the parent graph
and its compact Mersenne assumptions remains separate. -/
theorem map_85_to_84 (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) (hv : ∀ j, 0<v j)
    (hdiv : q beta v∣v 6) (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    ∃ v' : Fin 14 → V, (∀ j, 0<v' j) ∧ InternalZero (P84QcubeGraph.graph p).output v' := by
  obtain ⟨w,hw⟩ := hdiv
  have hwpos : 0<w := by
    apply pos_iff_ne_zero.mpr
    intro h0
    have hX : v 6=0 := by rw [hw,h0,mul_zero]
    exact (ne_of_gt (hv 6)) hX
  refine ⟨to84 v w,to84_positive v w hv hwpos,?_⟩
  apply (internalZero_iff _ _).mpr
  have h := Ring84To85Draft.output_eval p (fun j => ι (to84 v w j))
  rw [← cast_to84 p beta v w hport hw] at h
  rw [← h]
  exact (internalZero_iff _ _).mp hz

end DiophantineConsistency.Conditional84To85Draft

#print axioms DiophantineConsistency.Conditional84To85Draft.map_84_to_85
#print axioms DiophantineConsistency.Conditional84To85Draft.map_85_to_84
