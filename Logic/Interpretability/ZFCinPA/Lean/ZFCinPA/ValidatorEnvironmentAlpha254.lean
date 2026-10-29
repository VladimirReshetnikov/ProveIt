import ZFCinPA.ValidatorLabelAvoidance
import ZFCinPA.ValidatorEqualityContextVacuity254
import ZFCinPA.ValidatorEqualityCore254

set_option autoImplicit false
noncomputable section

/-!
Source-only alpha-conversion draft. Every source formula, stack, label and
stream index is internal. The two future binder streams are explicitly apart
and avoid both old stacks and every free label, including fallback 1. This
module does not choose parity-separated streams or identify a fixed encoder.
-/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254 ValidatorProvability254 ValidatorQuantifierCore254
open ValidatorEqualityCore254 ValidatorEqualityContext254
open ValidatorEnvironmentLabels254 ValidatorEnvironmentVacuity254
open ValidatorEqualityContextVacuity254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def StreamEnv (s B : V) : Prop := ∀ k : V, Avoid (s+2*k) B
def StreamFree (s F : V) : Prop := ∀ k : V, FreeAvoid (s+2*k) F
def Apart (s t : V) : Prop := ∀ i j : V, s+2*i ≠ t+2*j

def FreshPair (F B B' s t : V) : Prop :=
  StreamFree s F ∧ StreamFree t F ∧
  StreamEnv s B ∧ StreamEnv s B' ∧
  StreamEnv t B ∧ StreamEnv t B' ∧ Apart s t


lemma streamFree_next {s F : V} (h : StreamFree s F) : StreamFree (s+2) F :=
  ValidatorLabelAvoidance.streamFree_next h

lemma streamEnv_cons_next {s B x : V} (h : StreamEnv s B)
    (hx : ∀ k : V, (s+2)+2*k≠x) : StreamEnv (s+2) (x∷B) :=
  ValidatorLabelAvoidance.streamEnv_cons_next h hx

lemma freshPair_next {F B B' s t : V} (h : FreshPair F B B' s t) :
    FreshPair F (s∷B) (t∷B') (s+2) (t+2) :=
  ValidatorLabelAvoidance.freshPair_next h

/-- Both cross-body vacuity arguments, with no assertion that a binder is
vacuous in its own body. The right side still has the left-to-right context. -/
lemma cross_body_vac [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ (n+1) p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (h : FreshPair F B B' s t) :
    Vac s (encode F (t∷B') (t+2) p) ∧
    Vac t (encode F (s∷B) (s+2) p) :=
  ValidatorLabelAvoidance.cross_body_vac (P := Vac) (enc := encode)
    (fun hp F B fresh z hlen hF hB hs => encode_vac hp F B fresh z hlen hF hB hs)
    hp F B B' s t hB hB' h

/-- Both directions deliberately share the same left-to-right context. -/
def EqUnder (h p q : V) : Prop :=
  CProv (wim h (wim p q)) ∧ CProv (wim h (wim q p))

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
private lemma h0 {G : List V} {a : V} : D (a::G) a := .cons_head
private lemma h1 {G : List V} {a b : V} : D (b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
private lemma h2 {G : List V} {a b c : V} : D (c::b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
private lemma ofDer {p : V} (d : D [] p) : CProv p :=
  d.sound cProv_classical (fun _ hm => absurd hm List.not_mem_nil)
private lemma ded1 {a p : V} (d : D [a] p) : CProv (wim a p) :=
  ofDer (Kalmar.deduction cProv_classical d)
private lemma ded2 {a b p : V} (d : D [b,a] p) : CProv (wim a (wim b p)) :=
  ofDer (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical d))
private lemma ded3 {a b c p : V} (d : D [c,b,a] p) :
    CProv (wim a (wim b (wim c p))) :=
  ofDer (Kalmar.deduction cProv_classical
    (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical d)))

lemma eqUnder_refl (h p : V) : EqUnder h p p := by
  have hp : CProv (wim h (wim p p)) :=
    cProv_mp (cProv_k (wim p p) h) (Kalmar.self_imp cProv_classical p)
  exact ⟨hp,hp⟩

lemma contra_under {h p q : V} (hpq : CProv (wim h (wim p q))) :
    CProv (wim h (wim (ValidatorQuantifierCore254.neg q) (ValidatorQuantifierCore254.neg p))) :=
  ded3 (.mp h1 (.mp (.mp (.ax hpq) h2) h0))

lemma eqUnder_neg {h p q : V} (he : EqUnder h p q) : EqUnder h (ValidatorQuantifierCore254.neg p) (ValidatorQuantifierCore254.neg q) :=
  ⟨contra_under he.2,contra_under he.1⟩

lemma imp_under {h p p' q q' : V}
    (hp : CProv (wim h (wim p' p))) (hq : CProv (wim h (wim q q'))) :
    CProv (wim h (wim (wim p q) (wim p' q'))) :=
  ded3 (.mp (.mp (.ax hq) h2) (.mp h1 (.mp (.mp (.ax hp) h2) h0)))

lemma eqUnder_imp {h p p' q q' : V} (hp : EqUnder h p p') (hq : EqUnder h q q') :
    EqUnder h (wim p q) (wim p' q') :=
  ⟨imp_under hp.2 hq.1,imp_under hp.1 hq.2⟩

lemma eqUnder_conj {h p p' q q' : V} (hp : EqUnder h p p') (hq : EqUnder h q q') :
    EqUnder h (conj p q) (conj p' q') :=
  eqUnder_neg (eqUnder_imp hp (eqUnder_neg hq))

lemma reverse_eq_premise {h r x y : V}
    (hr : CProv (wim h (wim (weq x y) r))) :
    CProv (wim h (wim (weq y x) r)) :=
  ded2 (.mp (.mp (.ax hr) h1) (.mp (.ax (eq_symm y x)) h0))

/-- Reverse transport changes the equality premise by its finite symmetry
proof; it never silently swaps the old stack context. -/
lemma eqUnder_all_of_cons (B B' p q x y : V)
    (hb : EqUnder (eqContext (x∷B) (y∷B')) p q)
    (vxh : Vac x (eqContext B B')) (vyh : Vac y (eqContext B B'))
    (vxq : Vac x q) (vyp : Vac y p) :
    EqUnder (eqContext B B') (wal x p) (wal y q) := by
  constructor
  · exact all_of_cons B B' p q x y hb.1 vxh vxq vyh (vac_all x vyp)
  · exact all_relational (eqContext B B') q p y x
      (reverse_eq_premise (discharge_cons B B' x y hb.2))
      vyh vyp vxh (vac_all y vxq)

lemma eqUnder_ex_of_cons (B B' p q x y : V)
    (hb : EqUnder (eqContext (x∷B) (y∷B')) p q)
    (vxh : Vac x (eqContext B B')) (vyh : Vac y (eqContext B B'))
    (vxq : Vac x q) (vyp : Vac y p) :
    EqUnder (eqContext B B') (ex x p) (ex y q) :=
  eqUnder_neg (eqUnder_all_of_cons B B' (ValidatorQuantifierCore254.neg p) (ValidatorQuantifierCore254.neg q) x y
    (eqUnder_neg hb) vxh vyh (vac_neg vxq) (vac_neg vyp))

lemma term_eq_under {n u : V} (hu : IsSemiterm ℒₛₑₜ n u)
    (F B B' : V) (hB : len B=n) :
    CProv (wim (eqContext B B') (weq (TermLabels.term F B u) (TermLabels.term F B' u))) := by
  rcases hu.case with (⟨i,hi,rfl⟩ | ⟨i,rfl⟩ | ⟨k,f,args,hf,_,rfl⟩)
  · rw [TermLabels.term_bvar,TermLabels.term_bvar]
    exact eqContext_projection B B' i (by rwa [hB])
  · rw [TermLabels.term_fvar,TermLabels.term_fvar]
    exact cProv_mp (cProv_k (weq (freeLabel F i) (freeLabel F i)) (eqContext B B'))
      (eq_refl (freeLabel F i))
  · have hf' : V ⊧/![k,f] (LeanProofs.ZFCinPA.instLORDefinableSet.func).val := hf
    rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.func : 𝚺₀.Semisentence 2) =
      .mkSigma “k f. ⊥” from rfl] at hf'
    simp at hf'

lemma atom_eq_under {n arity R terms : V} (hr : (ℒₛₑₜ).IsRel arity R)
    (ht : IsSemitermVec ℒₛₑₜ arity n terms) (F B B' s t : V) (hB : len B=n) :
    EqUnder (eqContext B B') (Formulas.atom ?[F,B,s] arity R terms)
      (Formulas.atom ?[F,B',t] arity R terms) := by
  have hr' : V ⊧/![arity,R] (LeanProofs.ZFCinPA.instLORDefinableSet.rel).val := hr
  rw [show (LeanProofs.ZFCinPA.instLORDefinableSet.rel : 𝚺₀.Semisentence 2) =
    .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” from rfl] at hr'
  have harity : arity=2 := by
    have hc : (arity=2 ∧ R=0) ∨ (arity=2 ∧ R=1) := by simpa using hr'
    exact hc.elim And.left And.left
  subst arity
  have hleft : CProv (wim (eqContext B B')
      (weq (TermLabels.vec F B 2 terms).[0] (TermLabels.vec F B' 2 terms).[0])) := by
    rw [TermLabels.vec_nth F B ht.isUTerm (by simp),TermLabels.vec_nth F B' ht.isUTerm (by simp)]
    exact term_eq_under (ht.nth (by simp)) F B B' hB
  have hright : CProv (wim (eqContext B B')
      (weq (TermLabels.vec F B 2 terms).[1] (TermLabels.vec F B' 2 terms).[1])) := by
    rw [TermLabels.vec_nth F B ht.isUTerm (by simp),TermLabels.vec_nth F B' ht.isUTerm (by simp)]
    exact term_eq_under (ht.nth (by simp)) F B B' hB
  have hleft' := compose hleft (eq_symm _ _)
  have hright' := compose hright (eq_symm _ _)
  classical
  simp only [Formulas.atom,nth_adjoin_zero,nth_adjoin_one]
  by_cases hz : R=0
  · simp only [hz,if_pos]
    constructor
    · exact ded2 (.mp (.mp (.mp (.ax (eq_congr _ _ _ _))
        (.mp (.ax hleft) h1)) (.mp (.ax hright) h1)) h0)
    · exact ded2 (.mp (.mp (.mp (.ax (eq_congr _ _ _ _))
        (.mp (.ax hleft') h1)) (.mp (.ax hright') h1)) h0)
  · simp only [hz,if_neg]
    constructor
    · exact ded2 (.mp (.mp (.mp (.ax (rel_congr _ _ _ _))
        (.mp (.ax hleft) h1)) (.mp (.ax hright) h1)) h0)
    · exact ded2 (.mp (.mp (.mp (.ax (rel_congr _ _ _ _))
        (.mp (.ax hleft') h1)) (.mp (.ax hright') h1)) h0)

/-- The paired universal/existential step for the eventual formula induction. -/
lemma encoded_binder_steps [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ (n+1) p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t)
    (ih : EqUnder (eqContext (s∷B) (t∷B'))
      (encode F (s∷B) (s+2) p) (encode F (t∷B') (t+2) p)) :
    EqUnder (eqContext B B') (encode F B s (^∀ p)) (encode F B' t (^∀ p)) ∧
    EqUnder (eqContext B B') (encode F B s (^∃ p)) (encode F B' t (^∃ p)) := by
  have hv := cross_body_vac hp F B B' s t hB hB' hf
  rcases hf with ⟨_,_,hsB,hsB',htB,htB',_⟩
  have vs : Vac s (eqContext B B') := eqContext_vac B B' s (hB.trans hB'.symm)
    (by simpa using hsB 0) (by simpa using hsB' 0)
  have vt : Vac t (eqContext B B') := eqContext_vac B B' t (hB.trans hB'.symm)
    (by simpa using htB 0) (by simpa using htB' 0)
  constructor
  · rw [encode_all F B s hp.isUFormula,encode_all F B' t hp.isUFormula]
    exact eqUnder_all_of_cons B B' _ _ s t ih vs vt hv.1 hv.2
  · rw [encode_exs F B s hp.isUFormula,encode_exs F B' t hp.isUFormula]
    exact eqUnder_ex_of_cons B B' _ _ s t ih vs vt hv.1 hv.2

/-! The uniform proof-existence invariant is Pi-two. These graph interfaces
keep hierarchy closure independent of the implementation of numeric syntax. -/
private instance len_delta : 𝚫₁-Function₁[V] (len : V→V) :=
  len_defined.graph_delta.to_definable
private instance avoid_delta : 𝚫₁-Relation[V] Avoid := by unfold Avoid; definability
private instance free_delta : 𝚫₁-Relation[V] FreeAvoid := by unfold FreeAvoid; definability
private instance streamEnv_pi1 : 𝚷₁-Relation[V] StreamEnv := by unfold StreamEnv; definability
private instance streamFree_pi1 : 𝚷₁-Relation[V] StreamFree := by unfold StreamFree; definability
private instance apart_pi1 : 𝚷₁-Relation[V] Apart := by unfold Apart; definability
private instance freshPair_pi1 : 𝚷₁-Relation₅[V] FreshPair := by unfold FreshPair; definability

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
private instance freshPair_sigma2 : 𝚺-[2]-Relation₅[V] FreshPair :=
  pi1_to_sigma2 freshPair_pi1
private instance len_sigma2 : 𝚺-[2]-Function₁[V] (len : V→V) := len_delta.of_deltaOne
private instance encode_sigma2 : 𝚺-[2]-Function₄[V] encode :=
  (encode_defined.graph_delta.to_definable).of_deltaOne
private instance eqContext_sigma2 : 𝚺-[2]-Function₂[V] eqContext :=
  (eqContext_defined.graph_delta.to_definable).of_deltaOne
private instance wim_sigma2 : 𝚺-[2]-Function₂[V] wim := wim_defined.to_definable₀
private instance semiformula_sigma2 : 𝚺-[2]-Relation[V] (IsSemiformula ℒₛₑₜ) :=
  IsSemiformula.definable.of_deltaOne
private instance eqUnder_pi2 : 𝚷-[2]-Relation₃[V] EqUnder := by
  unfold EqUnder
  definability

private lemma alpha_invariant_pi2 : 𝚷-[2]-Predicate[V]
    (fun p => ∀ n F B B' s t : V, IsSemiformula ℒₛₑₜ n p → len B=n → len B'=n →
      FreshPair F B B' s t → EqUnder (eqContext B B') (encode F B s p) (encode F B' t p)) := by
  apply HierarchySymbol.Definable.all
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
  · definability

/-- All-internal alpha transport, in both directions under the same represented
stack-equality context. The future-stream invariant is an explicit premise. -/
theorem encode_eq_under [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (F B B' s t : V)
    (hB : len B=n) (hB' : len B'=n) (hf : FreshPair F B B' s t) :
    EqUnder (eqContext B B') (encode F B s p) (encode F B' t p) := by
  have main : ∀ p : V, ∀ n F B B' s t : V, IsSemiformula ℒₛₑₜ n p →
      len B=n → len B'=n → FreshPair F B B' s t →
      EqUnder (eqContext B B') (encode F B s p) (encode F B' t p) := by
    apply InductionOnHierarchy.order_induction_sigma 𝚷 2
      (P := fun p => ∀ n F B B' s t : V, IsSemiformula ℒₛₑₜ n p → len B=n → len B'=n →
        FreshPair F B B' s t → EqUnder (eqContext B B') (encode F B s p) (encode F B' t p))
    · exact alpha_invariant_pi2
    · intro p ih n F B B' s t htyped hB hB' hf
      rcases IsSemiformula.case_iff.mp htyped with
        (⟨arity,R,terms,hr,ht,rfl⟩ | ⟨arity,R,terms,hr,ht,rfl⟩ | rfl | rfl |
          ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩)
      · rw [encode_rel F B s hr ht.isUTerm,encode_rel F B' t hr ht.isUTerm]
        exact atom_eq_under hr ht F B B' s t hB
      · rw [encode_nrel F B s hr ht.isUTerm,encode_nrel F B' t hr ht.isUTerm]
        exact eqUnder_neg (atom_eq_under hr ht F B B' s t hB)
      · simpa using eqUnder_refl (eqContext B B') (0 : V)
      · simpa using eqUnder_refl (eqContext B B') (1 : V)
      · rw [encode_and F B s hp.isUFormula hq.isUFormula,
          encode_and F B' t hp.isUFormula hq.isUFormula]
        exact eqUnder_conj (ih p (by simp) n F B B' s t hp hB hB' hf)
          (ih q (by simp) n F B B' s t hq hB hB' hf)
      · rw [encode_or F B s hp.isUFormula hq.isUFormula,
          encode_or F B' t hp.isUFormula hq.isUFormula]
        exact eqUnder_imp (eqUnder_neg (ih p (by simp) n F B B' s t hp hB hB' hf))
          (ih q (by simp) n F B B' s t hq hB hB' hf)
      · exact (encoded_binder_steps hp F B B' s t hB hB' hf
          (ih p (by simp) (n+1) F (s∷B) (t∷B') (s+2) (t+2) hp
            (by simp [hB]) (by simp [hB']) (freshPair_next hf))).1
      · exact (encoded_binder_steps hp F B B' s t hB hB' hf
          (ih p (by simp) (n+1) F (s∷B) (t∷B') (s+2) (t+2) hp
            (by simp [hB]) (by simp [hB']) (freshPair_next hf))).2
  exact main p n F B B' s t hp hB hB' hf

/-- At empty bound stacks the equality context is truth. Stream selection and
any comparison to the fixed formulaEncoder remain separate clients. -/
lemma encode_formula_alpha [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {p : V} (hp : IsFormula ℒₛₑₜ p)
    (F s t : V) (hs : StreamFree s F) (ht : StreamFree t F) (hap : Apart s t) :
    CProv (wim (encode F 0 s p) (encode F 0 t p)) ∧
    CProv (wim (encode F 0 t p) (encode F 0 s p)) := by
  have hf : FreshPair F 0 0 s t :=
    ⟨hs,ht,(fun k => avoid_nil (s+2*k)),(fun k => avoid_nil (s+2*k)),
      (fun k => avoid_nil (t+2*k)),(fun k => avoid_nil (t+2*k)),hap⟩
  have he := encode_eq_under hp F 0 0 s t (by simp) (by simp) hf
  have hc : CProv (eqContext (0 : V) 0) := by simpa using (cProv_truth (V := V))
  exact ⟨cProv_mp he.1 hc,cProv_mp he.2 hc⟩

end LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254
