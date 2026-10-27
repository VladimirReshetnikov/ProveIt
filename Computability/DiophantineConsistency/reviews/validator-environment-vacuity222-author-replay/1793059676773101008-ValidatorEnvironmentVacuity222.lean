import ZFCinPA.ValidatorFormulaEncoder222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Uniform represented vacuity for the actual C222 Eind-aware encoder.
The syntax-only environment conventions and the represented Pi2 induction
pattern follow the existing configurable encoder. The atom proof is new:
it uses actual C222 Eind_vac and membership vacuity, never primitive equality
vacuity. Typed terms, exact bound-stack length, free fallback1 and the whole
future binder stream are explicit. No positivity, pairwise distinctness,
self-vacuity, seed truth or arbitrary Lean-predicate induction is assumed.
Uniform proof witnesses require IΣ2; the local lemmas use IΣ1. -/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorEnvironmentLabels254 (freeLabel)
open ValidatorFormulaEncoder222 ValidatorRelationalCore222 ValidatorProvability222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Avoid every stored label; all indices and the vector length are internal. -/
def Avoid (z env : V) : Prop := ∀ i<len env, z≠env.[i]
/-- The finite free vector has the additional fallback label 1. -/
def FreeAvoid (z env : V) : Prop := z≠1 ∧ Avoid z env
/-- Avoid all labels that the encoder may allocate below a binder. -/
def StreamAvoid (z fresh : V) : Prop := ∀ k : V, z≠fresh+2*k

lemma avoid_nil (z : V) : Avoid z (0 : V) := by simp [Avoid]
lemma avoid_cons {z env x : V} (he : Avoid z env) (hx : z≠x) : Avoid z (x∷env) := by
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i,rfl⟩)
  · simpa using hx
  · simpa using he i (by simpa using hi)
lemma free_label_avoids {z env : V} (he : FreeAvoid z env) (i : V) :
    z≠freeLabel env i := by
  classical
  by_cases hi : i<len env
  · simpa [freeLabel,hi] using he.2 i hi
  · simpa [freeLabel,hi] using he.1
lemma stream_head {z fresh : V} (h : StreamAvoid z fresh) : z≠fresh := by
  simpa using h 0
lemma stream_next {z fresh : V} (h : StreamAvoid z fresh) : StreamAvoid z (fresh+2) := by
  intro k
  rw [show (fresh+2)+2*k=fresh+2*(k+1) by ring]
  exact h (k+1)
lemma stream_of_lt {z fresh : V} (h : z<fresh) : StreamAvoid z fresh := by
  intro k
  exact ne_of_lt (lt_of_lt_of_le h (le_add_of_nonneg_right (Arithmetic.zero_le _)))

lemma term_label_avoids {n t : V} (ht : IsSemiterm ℒₛₑₜ n t)
    (F B z : V) (hlen : len B=n) (hF : FreeAvoid z F) (hB : Avoid z B) :
    z≠ValidatorEnvironmentLabels254.TermLabels.term F B t := by
  rcases ht.case with (⟨i,hi,rfl⟩ | ⟨i,rfl⟩ | ⟨k,f,args,hf,_,rfl⟩)
  · rw [ValidatorEnvironmentLabels254.TermLabels.term_bvar]
    exact hB i (by rwa [hlen])
  · rw [ValidatorEnvironmentLabels254.TermLabels.term_fvar]
    exact free_label_avoids hF i
  · have hf' : V ⊧/![k,f] (LeanProofs.ZFCinPA.instLORDefinableSet.func).val := hf
    rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.func : 𝚺₀.Semisentence 2) =
      .mkSigma “k f. ⊥” from rfl] at hf'
    simp at hf'

lemma atom_vac {n arity R terms : V} (hr : (ℒₛₑₜ).IsRel arity R)
    (ht : IsSemitermVec ℒₛₑₜ arity n terms)
    (F B fresh z : V) (hlen : len B=n) (hF : FreeAvoid z F) (hB : Avoid z B) :
    Vac z (atom ?[F,B,fresh] arity R terms) := by
  have hr' : V ⊧/![arity,R] (LeanProofs.ZFCinPA.instLORDefinableSet.rel).val := hr
  rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.rel : 𝚺₀.Semisentence 2) =
    .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” from rfl] at hr'
  have harity : arity=2 := by
    have hc : (arity=2 ∧ R=0) ∨ (arity=2 ∧ R=1) := by simpa using hr'
    exact hc.elim And.left And.left
  subst arity
  have hleft : z≠(ValidatorEnvironmentLabels254.TermLabels.vec F B 2 terms).[0] := by
    rw [ValidatorEnvironmentLabels254.TermLabels.vec_nth F B ht.isUTerm (by simp)]
    exact term_label_avoids (ht.nth (by simp)) F B z hlen hF hB
  have hright : z≠(ValidatorEnvironmentLabels254.TermLabels.vec F B 2 terms).[1] := by
    rw [ValidatorEnvironmentLabels254.TermLabels.vec_nth F B ht.isUTerm (by simp)]
    exact term_label_avoids (ht.nth (by simp)) F B z hlen hF hB
  classical
  simp only [atom,nth_adjoin_zero,nth_adjoin_one]
  split
  · exact ValidatorEind222.Eind_vac _ _ z hleft hright
  · exact vac_rel _ _ z hleft hright

/-! The induction predicate is genuinely Pi-two, not Pi-one. -/
private instance len_delta : 𝚫₁-Function₁[V] (len : V→V) :=
  len_defined.graph_delta.to_definable
private instance avoid_delta : 𝚫₁-Relation[V] Avoid := by unfold Avoid; definability
private instance stream_pi1 : 𝚷₁-Relation[V] StreamAvoid := by unfold StreamAvoid; definability

private lemma sigma1_to_pi2 {k : ℕ} {P : (Fin k→V)→Prop}
    (h : 𝚺₁.Definable P) : (𝚷-[2]).Definable P := by
  rcases h with ⟨φ,hφ⟩
  refine ⟨.mkPi φ.val (φ.sigma_prop.strict_mono 𝚷 (by decide)),?_⟩
  intro v
  simpa only [HierarchySymbol.Semiformula.val_mkPi] using (hφ.iff (v := v))
private lemma pi1_to_sigma2 {k : ℕ} {P : (Fin k→V)→Prop}
    (h : 𝚷₁.Definable P) : (𝚺-[2]).Definable P := by
  rcases h with ⟨φ,hφ⟩
  refine ⟨.mkSigma φ.val (φ.pi_prop.strict_mono 𝚺 (by decide)),?_⟩
  intro v
  simpa only [HierarchySymbol.Semiformula.val_mkSigma] using (hφ.iff (v := v))

private instance cProv_pi2 : 𝚷-[2]-Predicate[V] CProv :=
  sigma1_to_pi2 cProv_definable
private instance stream_sigma2 : 𝚺-[2]-Relation[V] StreamAvoid :=
  pi1_to_sigma2 stream_pi1
private instance avoid_sigma2 : 𝚺-[2]-Relation[V] Avoid :=
  avoid_delta.of_deltaOne
private instance len_sigma2 : 𝚺-[2]-Function₁[V] (len : V→V) :=
  len_delta.of_deltaOne
private instance encode_sigma2 : 𝚺-[2]-Function₄[V] encode :=
  (encode_defined.graph_delta.to_definable).of_deltaOne
private instance wim_sigma2 : 𝚺-[2]-Function₂[V] wim := wim_defined.to_definable₀
private instance wal_sigma2 : 𝚺-[2]-Function₂[V] wal := wal_defined.to_definable₀
private instance semiformula_sigma2 : 𝚺-[2]-Relation[V] (IsSemiformula ℒₛₑₜ) :=
  IsSemiformula.definable.of_deltaOne
private instance free_sigma2 : 𝚺-[2]-Relation[V] FreeAvoid := by
  unfold FreeAvoid
  definability
private instance vac_pi2 : 𝚷-[2]-Relation[V] Vac := by
  unfold Vac
  definability

/-- Keep the hierarchy proof separate from the constructor induction. Each
closure uses a fixed represented graph rather than unfolding the encoder. -/
private lemma vac_invariant_pi2 : 𝚷-[2]-Predicate[V]
    (fun p => ∀ n F B fresh z : V, IsSemiformula ℒₛₑₜ n p → len B=n →
      FreeAvoid z F → Avoid z B → StreamAvoid z fresh → Vac z (encode F B fresh p)) := by
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp
  · definability
  apply HierarchySymbol.Definable.imp
  · definability
  apply HierarchySymbol.Definable.imp
  · definability
  apply HierarchySymbol.Definable.imp
  · definability
  apply HierarchySymbol.Definable.imp
  · definability
  · definability

/-- Uniform vacuity for every internal encoded formula. IΣ₂ supports the
Pi-two induction over all environment choices and proof witnesses. -/
theorem encode_vac [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V} (hp : IsSemiformula ℒₛₑₜ n p)
    (F B fresh z : V) (hlen : len B=n) (hF : FreeAvoid z F)
    (hB : Avoid z B) (hs : StreamAvoid z fresh) : Vac z (encode F B fresh p) := by
  have main : ∀ p : V, ∀ n F B fresh z : V, IsSemiformula ℒₛₑₜ n p → len B=n →
      FreeAvoid z F → Avoid z B → StreamAvoid z fresh → Vac z (encode F B fresh p) := by
    apply InductionOnHierarchy.order_induction_sigma 𝚷 2
      (P := fun p => ∀ n F B fresh z : V, IsSemiformula ℒₛₑₜ n p → len B=n →
        FreeAvoid z F → Avoid z B → StreamAvoid z fresh → Vac z (encode F B fresh p))
    · exact vac_invariant_pi2
    · intro p ih n F B fresh z htyped hlen hF hB hs
      rcases IsSemiformula.case_iff.mp htyped with
        (⟨arity,R,terms,hr,ht,rfl⟩ | ⟨arity,R,terms,hr,ht,rfl⟩ | rfl | rfl |
          ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩)
      · rw [encode_rel F B fresh hr ht.isUTerm]
        exact atom_vac hr ht F B fresh z hlen hF hB
      · rw [encode_nrel F B fresh hr ht.isUTerm]
        exact vac_neg (atom_vac hr ht F B fresh z hlen hF hB)
      · simpa using vac_truth z
      · simpa using vac_falsum z
      · rw [encode_and F B fresh hp.isUFormula hq.isUFormula]
        exact vac_neg (vac_imp (ih p (by simp) n F B fresh z hp hlen hF hB hs)
          (vac_neg (ih q (by simp) n F B fresh z hq hlen hF hB hs)))
      · rw [encode_or F B fresh hp.isUFormula hq.isUFormula]
        exact vac_imp (vac_neg (ih p (by simp) n F B fresh z hp hlen hF hB hs))
          (ih q (by simp) n F B fresh z hq hlen hF hB hs)
      · rw [encode_all F B fresh hp.isUFormula]
        exact vac_all fresh (ih p (by simp) (n+1) F (fresh∷B) (fresh+2) z hp
          (by simp [hlen]) hF (avoid_cons hB (stream_head hs)) (stream_next hs))
      · rw [encode_exs F B fresh hp.isUFormula]
        exact vac_neg (vac_all fresh (vac_neg
          (ih p (by simp) (n+1) F (fresh∷B) (fresh+2) z hp
            (by simp [hlen]) hF (avoid_cons hB (stream_head hs)) (stream_next hs))))
  exact main p n F B fresh z hp hlen hF hB hs

/-- Closed-bound-context client, with the same explicit free/binder avoidance. -/
lemma encode_formula_vac [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {p : V} (hp : IsFormula ℒₛₑₜ p)
    (F fresh z : V) (hF : FreeAvoid z F) (hs : StreamAvoid z fresh) :
    Vac z (encode F 0 fresh p) :=
  encode_vac hp F 0 fresh z (by simp) hF (avoid_nil z) hs

/-- The same result exposes a numeric proof accepted by the actual represented
C222 history, uniformly over every internal well-typed source formula. -/
theorem encode_vac_witness [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B fresh z : V) (hlen : len B=n)
    (hF : FreeAvoid z F) (hB : Avoid z B) (hs : StreamAvoid z fresh) :
    ∃ code : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value code =
      wim (encode F B fresh p) (wal z (encode F B fresh p)) + 1 :=
  encode_vac hp F B fresh z hlen hF hB hs

/-- Malformed sources use the separate fixed truth-output branch. This is
not a claim that source zero is a well-formed formula. -/
theorem encode_malformed_vac (F B fresh z : V) {p : V}
    (hp : ¬IsUFormula ℒₛₑₜ p) : Vac z (encode F B fresh p) := by
  rw [encode_of_not_formula F B fresh hp]
  exact vac_truth z

end LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity222
