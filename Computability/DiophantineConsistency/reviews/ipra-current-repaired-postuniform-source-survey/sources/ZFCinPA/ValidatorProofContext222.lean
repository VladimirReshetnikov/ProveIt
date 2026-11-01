import ZFCinPA.ValidatorFormulaEncoder222
import ZFCinPA.ValidatorContextLists
import ZFCinPA.ValidatorImplicationContext
import ZFCinPA.ValidatorVectorMap

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Internal contexts for the actual C222 history predicate. The vector folds
and their fixed graphs precede every use in induction; all context lengths,
indices and finite-set codes are internal elements of an arbitrary IΣ1 model.
Only fixed finite propositional certificates use Lean lists. Adapted from the
list calculus in R2Ctx, which is not imported: every provability premise and
witness here is the actual C222 predicate, and equality atoms use Eind through
the new encoder. The predicate-independent lists (`imps`, `shiftList`, `Enum`)
are shared with R2Ctx through `ValidatorContextLists` and re-exported here. No source axiom image, NNF proof interpretation, vacuity,
closed ZF-to-C222 reduction, or HA endpoint is asserted. -/

namespace LeanProofs.ZFCinPA.ValidatorProofContext222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorFormulaEncoder222
open ValidatorEnvironmentLabels254 (tail)
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA.ValidatorContextLists
export LeanProofs.ZFCinPA.ValidatorContextLists (imps imps_nil imps_cons impsDef
  imps_defined imps_definable imps_graph imps_total_unique shiftList shiftList_nil
  shiftList_cons shiftListDef shiftList_defined shiftList_definable shiftList_len_nth
  mem_shiftList Enum enum_of_mem enumDef enum_defined enum_definable exists_enum)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Finite propositional reasoning -/

lemma self_imp (a : V) : CProv (wim a a) :=
  ValidatorImplicationContext.ded1 CProv cProv_classical (ValidatorImplicationContext.h0 CProv)

/-! ## Implication chains -/

/-- Derivability in a context. -/
def Der (G g : V) : Prop := CProv (imps G g)

def derDef : 𝚺₁.Semisentence 2 := .mkSigma
  “G g. ∃ p, !impsDef p G g ∧ !cProvDef p”
instance der_defined : 𝚺₁-Relation[V] Der via derDef :=
  .mk fun e => by simp [derDef, Der]

/-- The context assertion contains an actual internal checker witness. -/
theorem der_iff_history (G g : V) :
    Der G g ↔ ∃ d : V, ArithmeticHistory222.value d = imps G g + 1 := Iff.rfl

@[simp] theorem der_nil (g : V) : Der (0 : V) g ↔ CProv g := by simp [Der]

lemma cProv_imps_k (x : V) : ∀ G : V, CProv (wim x (imps G x)) :=
  ValidatorImplicationContext.imps_k CProv imps imps_nil imps_cons cProv_classical x

lemma der_of {G x : V} (h : CProv x) : Der G x := cProv_mp (cProv_imps_k x G) h

lemma cProv_imps_mp (a b : V) : ∀ G : V,
    CProv (wim (imps G (wim a b)) (wim (imps G a) (imps G b))) :=
  ValidatorImplicationContext.imps_mp CProv imps imps_nil imps_cons cProv_classical a b

lemma der_mp {G a b : V} (hab : Der G (wim a b)) (ha : Der G a) : Der G b :=
  cProv_mp (cProv_mp (cProv_imps_mp a b G) hab) ha

lemma der_hyp : ∀ G : V, ∀ i < len G, Der G G.[i] :=
  ValidatorImplicationContext.hyp CProv imps imps_nil imps_cons cProv_classical

lemma der_mem {G x : V} (h : x ∈ᵥ G) : Der G x := by
  obtain ⟨i, hi, rfl⟩ := h
  exact der_hyp G i hi

lemma cProv_ded (a g : V) : ∀ G : V, CProv (wim (wim a (imps G g)) (imps G (wim a g))) :=
  ValidatorImplicationContext.imps_ded CProv imps imps_nil imps_cons cProv_classical a g

lemma der_ded {G a g : V} (h : Der (a ∷ G) g) : Der G (wim a g) := by
  unfold Der at *
  rw [imps_cons] at h
  exact cProv_mp (cProv_ded a g G) h

lemma cProv_undeduct (a g : V) : ∀ G : V, CProv (wim (imps G (wim a g)) (wim a (imps G g))) :=
  ValidatorImplicationContext.imps_undeduct CProv imps imps_nil imps_cons cProv_classical a g

lemma der_undeduct {G a g : V} (h : Der G (wim a g)) : Der (a ∷ G) g := by
  unfold Der at *
  rw [imps_cons]
  exact cProv_mp (cProv_undeduct a g G) h

/-- Subsumption, internalized: every member of `G'` is a member of `G`. -/
lemma cProv_sub (G g : V) : ∀ G' : V, (∀ x, x ∈ᵥ G' → x ∈ᵥ G) →
    Der G (wim (imps G' g) g) :=
  ValidatorImplicationContext.sub CProv imps imps_nil imps_cons cProv_classical G g

lemma der_sub {G G' g : V} (hsub : ∀ x, x ∈ᵥ G' → x ∈ᵥ G) (h : Der G' g) : Der G g :=
  der_mp (cProv_sub G g G' hsub) (der_of h)

/-- Proof by contradiction in a context. -/
lemma der_byContra {G a : V} (h : Der (neg a ∷ G) 1) : Der G a :=
  der_mp (der_of (double_neg_elim a)) (der_ded h)

/-- From a context containing `¬a`, a derivation of `a` closes it. -/
lemma der_absurd {G a : V} (hn : neg a ∈ᵥ G) (h : Der G a) : Der G 1 :=
  der_mp (der_mem hn) h

/-! ## Lists of negated encodings -/

namespace NegEnc

def blueprint : VecRec.Blueprint 2 where
  nil := .mkSigma “y F s. y = 0”
  adjoin := .mkSigma “y p ps ih F s. ∃ e, !encodeDef e F 0 s p ∧ ∃ n, !wimDef n e 1 ∧
    !adjoinDef y n ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin param p _ ih := neg (encode (param 0) 0 (param 1) p) ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end NegEnc

/-- The negated encodings of the members of `L`, in order. -/
noncomputable def negEnc (F s L : V) : V := NegEnc.construction.result ![F, s] L

@[simp] lemma negEnc_nil (F s : V) : negEnc F s (0 : V) = 0 := by
  simp [negEnc, NegEnc.construction]
@[simp] lemma negEnc_cons (F s p L : V) :
    negEnc F s (p ∷ L) = neg (encode F 0 s p) ∷ negEnc F s L := by
  simp [negEnc, NegEnc.construction]

def negEncDef : 𝚺₁.Semisentence 4 := .mkSigma “y F s L. !NegEnc.blueprint.resultDef y L F s”

instance negEnc_defined : 𝚺₁-Function₃[V] negEnc via negEncDef := .mk fun v ↦ by
  have h := (NegEnc.construction (V := V)).eval_resultDef ![v 0, v 3, v 1, v 2]
  have e : (fun i : Fin 2 ↦ (![v 0, v 3, v 1, v 2] : Fin 4 → V) i.succ.succ) = ![v 1, v 2] :=
    funext fun i ↦ by match i with | 0 => rfl | 1 => rfl
  rw [e] at h
  simpa [negEncDef, negEnc] using h

instance negEnc_definable : 𝚺₁-Function₃[V] negEnc := negEnc_defined.to_definable

lemma negEnc_len_nth (F s : V) : ∀ L : V, len (negEnc F s L) = len L ∧
    ∀ i < len L, (negEnc F s L).[i] = neg (encode F 0 s L.[i]) := by
  letI : 𝚺₁-Function₁[V] (fun p ↦ neg (encode F 0 s p)) := by definability
  letI : 𝚺₁-Function₁[V] (negEnc F s) := by definability
  exact ValidatorVectorMap.len_nth (fun p ↦ neg (encode F 0 s p)) (negEnc F s)
    (negEnc_nil F s) (negEnc_cons F s)

lemma mem_negEnc (F s L y : V) :
    y ∈ᵥ negEnc F s L ↔ ∃ p, p ∈ᵥ L ∧ y = neg (encode F 0 s p) :=
  ValidatorVectorMap.mem _ _ L y (negEnc_len_nth F s L)

/-- The validator code of a sequent listed by `L`. -/
noncomputable def seqC (F s L : V) : V := imps (negEnc F s L) 1

def seqCDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out F s L. ∃ G, !negEncDef G F s L ∧ !impsDef out G 1”
instance seqC_defined : 𝚺₁-Function₃[V] seqC via seqCDef :=
  .mk fun e => by simp [seqCDef, seqC]

theorem seqC_graph (out F s L : V) :
    V ⊧/![out,F,s,L] seqCDef.val ↔ out = seqC F s L :=
  (seqC_defined (V := V)).df ![out,F,s,L]

theorem seqC_iff_der (F s L : V) : CProv (seqC F s L) ↔ Der (negEnc F s L) 1 :=
  Iff.rfl

/-! ## Shifted lists -/

/-- Shifting the listed formulas is tailing the free environment. -/
lemma negEnc_shiftList (F s : V) : ∀ L : V, (∀ p, p ∈ᵥ L → IsUFormula ℒₛₑₜ p) →
    negEnc F s (shiftList L) = negEnc (tail F) s L := by
  intro L hL
  apply nth_ext' (len L)
  · simpa [(shiftList_len_nth L).1] using (negEnc_len_nth F s (shiftList L)).1
  · exact (negEnc_len_nth (tail F) s L).1
  · intro i hi
    rw [(negEnc_len_nth F s (shiftList L)).2 i (by simpa [(shiftList_len_nth L).1] using hi),
      (shiftList_len_nth L).2 i hi, (negEnc_len_nth (tail F) s L).2 i hi,
      encode_shift (hL _ (nth_mem_memVec hi)) F 0 s]

/-! ## Enumerations of sets -/


/-- Sequent provability does not depend on the internal enumeration order or
duplicates. This is context subsumption, not a source-axiom interpretation. -/
theorem seqC_enum_iff (F s : V) {L K S : V} (hL : Enum L S) (hK : Enum K S) :
    CProv (seqC F s L) ↔ CProv (seqC F s K) := by
  have sub : ∀ A B : V, Enum A S → Enum B S →
      ∀ x, x ∈ᵥ negEnc F s A → x ∈ᵥ negEnc F s B := by
    intro A B hA hB x hx
    obtain ⟨p, hp, rfl⟩ := (mem_negEnc F s A x).mp hx
    exact (mem_negEnc F s B _).mpr ⟨p, hB.mem.mpr (hA.mem.mp hp), rfl⟩
  exact ⟨fun h => der_sub (sub L K hL hK) h,
    fun h => der_sub (sub K L hK hL) h⟩

end LeanProofs.ZFCinPA.ValidatorProofContext222
