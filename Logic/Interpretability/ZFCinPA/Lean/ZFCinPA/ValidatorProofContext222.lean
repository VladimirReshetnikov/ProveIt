import ZFCinPA.ValidatorFormulaEncoder222
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
the new encoder. No source axiom image, NNF proof interpretation, vacuity,
closed ZF-to-C222 reduction, or HA endpoint is asserted. -/

namespace LeanProofs.ZFCinPA.ValidatorProofContext222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorFormulaEncoder222
open ValidatorEnvironmentLabels254 (tail)
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀

/-! ## Finite propositional reasoning -/

lemma self_imp (a : V) : CProv (wim a a) :=
  ValidatorImplicationContext.ded1 CProv cProv_classical (ValidatorImplicationContext.h0 CProv)

/-! ## Implication chains -/

namespace Imps

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y g. y = g”
  adjoin := .mkSigma “y p ps ih g. !wimDef y p ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil param := param 0
  adjoin _ p _ ih := wim p ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end Imps

/-- `imps [g₁, …, gₙ] g = g₁ → (g₂ → ⋯ → (gₙ → g))`. -/
noncomputable def imps (G g : V) : V := Imps.construction.result ![g] G

@[simp] lemma imps_nil (g : V) : imps (0 : V) g = g := by simp [imps, Imps.construction]
@[simp] lemma imps_cons (a G g : V) : imps (a ∷ G) g = wim a (imps G g) := by
  simp [imps, Imps.construction]

def impsDef : 𝚺₁.Semisentence 3 := Imps.blueprint.resultDef

instance imps_defined : 𝚺₁-Function₂[V] imps via impsDef := .mk fun v ↦ by
  have e : (fun i : Fin 1 ↦ v i.succ.succ) = ![v 2] :=
    funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; rfl
  rw [impsDef, (Imps.construction (V := V)).eval_resultDef v, e]
  rfl

instance imps_definable : 𝚺₁-Function₂[V] imps := imps_defined.to_definable

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

theorem imps_graph (out G g : V) :
    V ⊧/![out,G,g] impsDef.val ↔ out = imps G g :=
  (imps_defined (V := V)).df ![out,G,g]

theorem imps_total_unique (G g : V) :
    ∃! out : V, V ⊧/![out,G,g] impsDef.val :=
  ⟨imps G g, (imps_graph _ _ _).mpr rfl, fun _ h => (imps_graph _ _ _).mp h⟩

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

namespace ShiftList

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y p ps ih. ∃ q, !(shiftGraph ℒₛₑₜ) q p ∧ !adjoinDef y q ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ p _ ih := shift ℒₛₑₜ p ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end ShiftList

noncomputable def shiftList (L : V) : V := ShiftList.construction.result ![] L

@[simp] lemma shiftList_nil : shiftList (0 : V) = 0 := by simp [shiftList, ShiftList.construction]
@[simp] lemma shiftList_cons (p L : V) : shiftList (p ∷ L) = shift ℒₛₑₜ p ∷ shiftList L := by
  simp [shiftList, ShiftList.construction]

def shiftListDef : 𝚺₁.Semisentence 2 := ShiftList.blueprint.resultDef

instance shiftList_defined : 𝚺₁-Function₁[V] shiftList via shiftListDef := .mk fun v ↦ by
  have e : (fun i : Fin 0 ↦ v i.succ.succ) = ![] := funext fun i ↦ i.elim0
  rw [shiftListDef, (ShiftList.construction (V := V)).eval_resultDef v, e]
  rfl

instance shiftList_definable : 𝚺₁-Function₁[V] shiftList := shiftList_defined.to_definable

lemma shiftList_len_nth : ∀ L : V, len (shiftList L) = len L ∧
    ∀ i < len L, (shiftList L).[i] = shift ℒₛₑₜ L.[i] := by
  exact ValidatorVectorMap.len_nth (shift ℒₛₑₜ) shiftList shiftList_nil shiftList_cons

lemma mem_shiftList (L y : V) : y ∈ᵥ shiftList L ↔ ∃ p, p ∈ᵥ L ∧ y = shift ℒₛₑₜ p :=
  ValidatorVectorMap.mem _ _ L y (shiftList_len_nth L)

/-- Shifting the listed formulas is tailing the free environment. -/
lemma negEnc_shiftList (F s : V) : ∀ L : V, (∀ p, p ∈ᵥ L → IsUFormula ℒₛₑₜ p) →
    negEnc F s (shiftList L) = negEnc (tail F) s L := by
  intro L
  induction L using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro _; simp
  case adjoin p L ih =>
    intro hL
    rw [shiftList_cons, negEnc_cons, negEnc_cons,
      encode_shift (hL p (by simp)) F 0 s, ih (fun q hq ↦ hL q (memVec_adjoin_iff.mpr (Or.inr hq)))]

/-! ## Enumerations of sets -/

/-- `L` lists exactly the members of `s`. -/
def Enum (L s : V) : Prop := (∀ y ∈ s, y ∈ᵥ L) ∧ ∀ i < len L, L.[i] ∈ s

lemma Enum.mem {L s : V} (h : Enum L s) {y : V} : y ∈ᵥ L ↔ y ∈ s := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact h.2 i hi
  · exact h.1 y

lemma enum_of_mem {L s : V} (h : ∀ y, y ∈ᵥ L ↔ y ∈ s) : Enum L s :=
  ⟨fun y hy ↦ (h y).2 hy, fun _ hi ↦ (h _).1 (nth_mem_memVec hi)⟩

def enumDef : 𝚺₁.Semisentence 2 := .mkSigma
  “L s. (∀ y < s, y ∈ s → !memVecDef.sigma y L) ∧ ∃ l, !lenDef l L ∧
    ∀ i < l, ∃ y, !nthDef y L i ∧ y ∈ s”
instance enum_defined : 𝚺₁-Relation[V] Enum via enumDef :=
  .mk fun e => by
    simp only [enumDef]
    simp
    constructor
    · rintro ⟨h, hl⟩
      exact ⟨fun y hy => h y (lt_of_mem hy) hy, hl⟩
    · rintro ⟨h, hl⟩
      exact ⟨fun y _ hy => h y hy, hl⟩
instance enum_definable : 𝚫₁-Relation[V] Enum := by unfold Enum; definability

lemma exists_enum : ∀ s : V, ∃ L, Enum L s := by
  apply insert_induction_sigmaOne
  · definability
  · exact ⟨0, enum_of_mem fun y ↦ by simp⟩
  · rintro a s - ⟨L, hL⟩
    exact ⟨a ∷ L, enum_of_mem fun y ↦ by simp [hL.mem]⟩

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
