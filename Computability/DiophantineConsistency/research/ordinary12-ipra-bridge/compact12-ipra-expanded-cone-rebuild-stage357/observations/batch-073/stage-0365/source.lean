import ZFCinPA.ValidatorEnvironmentLabels254
import ZFCinPA.ValidatorContextLists
import ZFCinPA.ValidatorImplicationContext
import ZFCinPA.ValidatorVectorMap
import ZFCinPA.ValidatorQuantifierCore254

set_option autoImplicit false
noncomputable section

/-!
# R2: hypothesis contexts of internal length for the literal validator

A Foundation sequent is an internal finite set of formula codes, of internal
(possibly nonstandard) size. Its validator translation is an implication chain
`imps G g = g₁ → (g₂ → ⋯ → g)` over an internal list `G`; `Der G g` says the
chain is `CProv`-provable. This module supplies the context calculus, by
`Σ₁`-induction on internal lists, with every step internalized as one `CProv`
statement:

* `der_of`, `der_mp`, `der_hyp`, `der_ded`/`der_undeduct` (deduction in both
  directions), `der_sub` (any context whose members are among those of a larger
  one: weakening, exchange and contraction at once), `der_gen` (generalization
  through a context whose members are vacuous in the variable);
* the sequent code `seqC F s L = imps (negEnc F s L) 1`, with `negEnc` the
  list of negated encodings, and `negEnc_shiftList`.

`imps`, `shiftList` and the enumeration predicate `Enum L s` (`L` lists exactly
the members of the set `s`; `exists_enum`) do not mention `CProv`. They live in
`ValidatorContextLists`, shared with `ValidatorProofContext222`, and are
re-exported here.
-/

namespace LeanProofs.ZFCinPA.R2Ctx

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254 LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA.ValidatorContextLists
export LeanProofs.ZFCinPA.ValidatorContextLists (imps imps_nil imps_cons impsDef
  imps_defined imps_definable imps_graph imps_total_unique shiftList shiftList_nil
  shiftList_cons shiftListDef shiftList_defined shiftList_definable shiftList_len_nth
  mem_shiftList Enum enum_of_mem enumDef enum_defined enum_definable exists_enum)

variable {V : Type*} [ORingStructure V]

lemma sigma1_to_pi2 {k : ℕ} {P : (Fin k → V) → Prop}
    (h : 𝚺₁.Definable P) : (𝚷-[2]).Definable P := by
  rcases h with ⟨φ, hφ⟩
  refine ⟨.mkPi φ.val (φ.sigma_prop.strict_mono 𝚷 (by decide)), ?_⟩
  intro v
  simpa only [HierarchySymbol.Semiformula.val_mkPi] using (hφ.iff (v := v))

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance wal_sigma1 : 𝚺₁-Function₂[V] wal := wal_defined.to_definable₀
instance wel_sigma1 : 𝚺₁-Function₂[V] wel := wel_defined.to_definable₀
instance weq_sigma1 : 𝚺₁-Function₂[V] weq := weq_defined.to_definable₀

/-! ## Finite propositional reasoning -/

abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
lemma h0 {G : List V} {a : V} : D (a::G) a := ValidatorImplicationContext.h0 CProv
lemma h1 {G : List V} {a b : V} : D (b::a::G) a :=
  ValidatorImplicationContext.h1 CProv
lemma h2 {G : List V} {a b c : V} : D (c::b::a::G) a :=
  ValidatorImplicationContext.h2 CProv
lemma h3 {G : List V} {a b c e : V} : D (e::c::b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
lemma ofDer {p : V} (d : D [] p) : CProv p :=
  d.sound cProv_classical (fun _ hm => absurd hm List.not_mem_nil)
lemma ded1 {a p : V} (d : D [a] p) : CProv (wim a p) :=
  ValidatorImplicationContext.ded1 CProv cProv_classical d
lemma ded2 {a b p : V} (d : D [b,a] p) : CProv (wim a (wim b p)) :=
  ValidatorImplicationContext.ded2 CProv cProv_classical d
lemma ded3 {a b c p : V} (d : D [c,b,a] p) : CProv (wim a (wim b (wim c p))) :=
  ValidatorImplicationContext.ded3 CProv cProv_classical d
lemma ded4 {a b c e p : V} (d : D [e,c,b,a] p) :
    CProv (wim a (wim b (wim c (wim e p)))) :=
  ValidatorImplicationContext.ded3 CProv cProv_classical (Kalmar.deduction cProv_classical d)

lemma self_imp (a : V) : CProv (wim a a) := ded1 h0

/-! ## Implication chains -/

/-- Derivability in a context. -/
def Der (G g : V) : Prop := CProv (imps G g)

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

end LeanProofs.ZFCinPA.R2Ctx
