module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentTransport
@[expose] public section

/-! Exact relational-source all-rule accepted-code closure. The child uses
free/setShift literally, with explicit lo+1 allocator and finite free extension. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

/-- GEN under the negative conclusion assumption is licensed by an actual
vacuity certificate, not inferred from a host-language freshness assertion. -/
noncomputable def universalSequent (v a c : V) (disj : Certificate (nativeOr a c))
    (intro : Certificate (wim (wal v a) c)) (vac : Certificate (wim c (wal v c))) : Certificate c := by
  let nc : Context [wn c] (wn c) := .assumption (by simp)
  let ca : Context [wn c] a := resolveDisjunction (.closed disj) nc
  let all : Context [wn c] (wal v a) := ca.generalizeSingleton v (negationVacuity v c vac)
  let cc : Context [wn c] c := .mp all (.closed intro)
  exact (Context.mp cc nc).deduction.dne.empty

theorem sequent_all_certificate (s p f lo z child : V) (hm : qqAll p∈s)
    (hl : ∀ q, q∈s → FormulaCovered 0 f lo z q)
    (hr : ∀ q, q∈s → FormulaCovered 0 f (lo+1) z q)
    (hchild : verifyValue child =
      sequentCode (parameters 0 (lo∷f) (lo+1) z)
        (insert (Bootstrapping.free language p) (setShift language s))+1) :
    ∃ code, verifyValue code=sequentCode (parameters 0 f lo z) s+1 := by
  have hp : IsSemiformula language 1 p := by simpa using (hl _ hm).2.1
  have hs : ∀ q, q∈s → IsUFormula language q := fun q hq => (hl q hq).2.1.isUFormula
  obtain ⟨disj,hdisj⟩ := insert_accepted_disjunction (parameters 0 (lo∷f) (lo+1) z)
    (setShift language s) (Bootstrapping.free language p) child hchild
  rw [translate_free_advance p f lo z hp,advance_parameters] at hdisj
  obtain ⟨shift,hshift⟩ := setShift_forward_certificate (parameters 0 f (lo+1) z) s lo hs
  have hshift' : verifyValue shift=wim (sequentCode (parameters 0 (lo∷f) (lo+1) z) (setShift language s))
      (sequentCode (parameters 0 f (lo+1) z) s)+1 := by
    simpa only [prependFree_parameters] using hshift
  let a := translate (parameters (lo∷0) f (lo+1) z) p
  let c := sequentCode (parameters 0 f (lo+1) z) s
  let d : Certificate (nativeOr a c) := (⟨disj,hdisj⟩ : Certificate
    (nativeOr a (sequentCode (parameters 0 (lo∷f) (lo+1) z) (setShift language s)))).mp
      (implicationMap (identity (wn a)) ⟨shift,hshift'⟩)
  obtain ⟨move,back,hmove,hback⟩ := formula_allocator_certificates (qqAll p) 0 f lo (lo+1) z (hl _ hm) (hr _ hm)
  obtain ⟨member,hmember⟩ := member_certificate (parameters 0 f (lo+1) z) s (qqAll p) hm
  let toC := implicationCompose (⟨move,hmove⟩ : Certificate
    (wim (translate (parameters 0 f lo z) (qqAll p)) (translate (parameters 0 f (lo+1) z) (qqAll p))))
    ⟨member,hmember⟩
  have hintro : verifyValue toC.code=wim (wal lo a) c+1 := by
    simpa only [translate_all _ _ hp.isUFormula,parameters_allocator,advance_parameters,a,c,wal,universalValue] using toC.accepted
  have hz : lo<z := lt_of_lt_of_le (lt_add_one lo) (hr _ hm).1.1.2.1
  have hfresh : FreshEnvironment lo 0 f (lo+1) z :=
    environments_eigenFresh (hl _ hm).1.1 (ne_of_lt hz)
  obtain ⟨vac,hvac⟩ := sequent_vacuity_certificate s lo 0 f (lo+1) z hr hfresh
  let out := universalSequent lo a c d ⟨toC.code,hintro⟩ ⟨vac,hvac⟩
  exact sequent_allocator_accepted s 0 f (lo+1) lo z out.code hr hl out.accepted

#print axioms universalSequent
#print axioms sequent_all_certificate
end M6.PA.RelationalSource.Numeric

