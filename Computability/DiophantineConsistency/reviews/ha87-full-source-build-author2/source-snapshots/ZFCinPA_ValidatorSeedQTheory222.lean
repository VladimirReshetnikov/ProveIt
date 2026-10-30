import ZFCinPA.ValidatorSeedFixedImages222
import BusyBeaver.ZFC.KLowerQHyp
import ZFCinPA.Translation

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! # The quotient-interface theory interpreted in the seed theory

`qTheory = logicalTheory ∪ {qAx}`, where `qAx` is one fixed sentence stating
the eight non-GIC fields of `KQHyp.QHyp`: the equivalence laws and
extensionality of profile bisimilarity, profile pairs, and interpreted union,
power and singleton-closed containers. Every model of `qTheory` is a `QHyp`
structure (`models_qhyp`), so the quotient/WF interpretation of ZF can run over
`qTheory` exactly as over the raw CP/GIC theory.

In the other direction `qTheory` is interpreted in `seedTheory` by the
moving-marker tagged relativization: the logical part by the accepted finite
and GIC images, and `qAx` by `ValidatorSeedFixedImages222.fixed_image`, whose
semantic premise is `KLower.tag_qhyp` applied in every model of `seedTheory`.
-/
namespace LeanProofs.ZFCinPA.ValidatorSeedQTheory222
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open SetTheory.BusyBeaver.ZFC
open _root_.SetTheory (Form Sat scons)
open _root_.SetTheory.Form

/-! ## The quotient-interface sentence -/

/-- The fields of `QHyp` that `translate` expresses, as an ordinary formula:
read with membership `Member` and equality `Eqv`. -/
def qOrdinary : Form :=
  fAnd (fAll (fEq 0 0)) <|
  fAnd (fAll (fAll (fImp (fEq 1 0) (fEq 0 1)))) <|
  fAnd (fAll (fAll (fAll (fImp (fEq 2 1) (fImp (fEq 1 0) (fEq 2 0)))))) <|
  fAnd (fAll (fAll (fImp (fAll (fAnd (fImp (fMem 0 2) (fMem 0 1)) (fImp (fMem 0 1) (fMem 0 2))))
    (fEq 1 0)))) <|
  fAnd (fAll (fEx (fAll (fAnd (fImp (fMem 0 1) (fEx (fAnd (fMem 0 3) (fMem 1 0))))
    (fImp (fEx (fAnd (fMem 0 3) (fMem 1 0))) (fMem 0 1)))))) <|
  fAnd (fAll (fEx (fAll (fAnd (fImp (fMem 0 1) (fAll (fImp (fMem 0 1) (fMem 0 3))))
    (fImp (fAll (fImp (fMem 0 1) (fMem 0 3))) (fMem 0 1)))))) <|
  fAll (fEx (fAnd (fMem 1 0) (fAll (fImp (fMem 0 1) (fEx (fAnd (fMem 0 2)
    (fAll (fAnd (fImp (fMem 0 1) (fEq 0 2)) (fImp (fEq 0 2) (fMem 0 1))))))))))

/-- Profile pairs exist. -/
def qPairs : Form := fAll (fAll (fEx (ProfileSyntax.pairForm 0 2 1)))

/-- The full quotient-interface formula (without GIC). -/
def qForm : Form := fAnd (KQ1Model.translate qOrdinary) qPairs

section QSemantics

open Profile ProfilePairs ProfileAxioms ProfileCollection ProfileComposition

variable {V : Type*} (mem : V → V → Prop)

/-- The eight non-GIC fields of `QHyp`. -/
def QFields : Prop :=
  (∀ x, Eqv mem x x) ∧
  (∀ x y : V, Eqv mem x y → Eqv mem y x) ∧
  (∀ x y z : V, Eqv mem x y → Eqv mem y z → Eqv mem x z) ∧
  (∀ x y, (∀ z, Member mem z x ↔ Member mem z y) → Eqv mem x y) ∧
  (∀ a, ∃ b, ∀ z, Member mem z b ↔ ∃ x, Member mem x a ∧ Member mem z x) ∧
  (∀ a, ∃ p, ∀ x, Member mem x p ↔ InterpretedSub mem x a) ∧
  (∀ root, ∃ v, Member mem root v ∧ ∀ x, Member mem x v →
    ∃ s, Member mem s v ∧ ∀ z, Member mem z s ↔ Eqv mem z x) ∧
  (∀ a b, ∃ p, Pair mem p a b)

theorem sat_qForm (env : ℕ → V) : Sat mem env qForm ↔ QFields mem := by
  simp only [qForm, qOrdinary, qPairs, QFields, Sat, KQ1Model.sat_translate, KQ1Model.RelSat,
    ProfileSyntax.sat_pairForm, scons, InterpretedSub, iff_iff_implies_and_implies, and_assoc]

theorem qfields_of_qhyp {mem : V → V → Prop} (h : KQHyp.QHyp mem) : QFields mem :=
  ⟨h.refl, fun _ _ => h.symm, fun _ _ _ => h.trans, h.ext, h.union, h.power, h.singleton,
    h.pairs⟩

theorem qhyp_of_qfields {mem : V → V → Prop} (hg : ProfileModel.ModelsGIC mem)
    (h : QFields mem) : KQHyp.QHyp mem where
  gic := hg
  refl := h.1
  symm := fun {x y} => h.2.1 x y
  trans := fun {x y z} => h.2.2.1 x y z
  ext := h.2.2.2.1
  pairs := h.2.2.2.2.2.2.2
  union := h.2.2.2.2.1
  power := h.2.2.2.2.2.1
  singleton := h.2.2.2.2.2.2.1

end QSemantics

/-- The quotient-interface axiom. -/
def qAx : SetTheorySentence := (toSet 0 qForm).univCl

/-- **The quotient-interface theory.** -/
def qTheory : SetTheory := ValidatorSeedLogicalImages222.logicalTheory ∪ {qAx}

instance qTheory_delta1 : qTheory.Δ₁ :=
  ValidatorSeedLogicalImages222.logicalTheory_delta1.add (Theory.Δ₁.singleton qAx)

instance : 𝗘𝗤 ℒₛₑₜ ⪯ qTheory :=
  LO.Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl h)))

/-! ## Every model of `qTheory` is a `QHyp` structure -/

section Models

variable {M : Type} [Nonempty M] [SetStructure M]

theorem sat_of_models_univCl (φ : Form) (h : M↓[ℒₛₑₜ] ⊧ (toSet 0 φ).univCl)
    (e : ℕ → M) : Sat (memRel M) e φ :=
  (eval_toSet φ 0 ![] e e (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mp
    (models_iff_proposition.mp h e)

theorem models_univCl_of_sat (φ : Form) (h : ∀ e : ℕ → M, Sat (memRel M) e φ) :
    M↓[ℒₛₑₜ] ⊧ (toSet 0 φ).univCl :=
  models_iff_proposition.mpr fun e =>
    (eval_toSet φ 0 ![] e e (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mpr (h e)

/-- Global-image collection for every native matrix, from the GIC schema. -/
theorem models_gic_of_mem {T : SetTheory} [M↓[ℒₛₑₜ] ⊧* T] (hT : gicTheory ⊆ T) :
    ProfileModel.ModelsGIC (memRel M) := by
  intro phi _ env
  apply (ProfileSyntax.sat_gicForm (memRel M) phi env).mpr
  have h := models_iff_proposition.mp
    (models_of_mem (T := T) (hT ⟨toSet 2 phi, rfl⟩)) env
  have key : ∀ x y : M, (toSet 2 phi).Eval ![x, y] env ↔
      DeepPositiveClosure.MatrixRelation (memRel M) phi env x y := fun x y =>
    eval_toSet phi 2 ![x, y] env _ (fun i => by
      match i with
      | 0 => rfl
      | 1 => rfl) (fun j => by rw [Nat.add_comm]; rfl)
  simp [gicBodyMeta, gicAtomYB3, gicAtomXA3, gicAtomYB4, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton] at h
  intro a
  obtain ⟨b, h1, h2⟩ := h a
  refine ⟨b, fun y hy => ?_, fun x hx ⟨y, hy⟩ => ?_⟩
  · obtain ⟨x, hx⟩ := h1 y hy
    exact ⟨x, (key x y).1 hx⟩
  · obtain ⟨y', hy', h'⟩ := h2 x hx y ((key x y).2 hy)
    exact ⟨y', hy', (key x y').1 h'⟩

/-- **Every model of `qTheory` is a `QHyp` structure.** -/
theorem models_qhyp [M↓[ℒₛₑₜ] ⊧* qTheory] : KQHyp.QHyp (memRel M) := by
  have hg := models_gic_of_mem (M := M) (T := qTheory) (fun _ h => Or.inl (Or.inr h))
  have hq : M↓[ℒₛₑₜ] ⊧ qAx := models_of_mem (T := qTheory) (Or.inr rfl)
  exact qhyp_of_qfields hg
    ((sat_qForm (memRel M) (fun _ => Classical.arbitrary M)).mp
      (sat_of_models_univCl qForm hq _))

end Models

/-! ## Every model of `seedTheory` has the seed property for every formula -/

section Seed

open ValidatorFullSeedTheory222 ValidatorSourceFullSeed222

variable {M : Type} [Nonempty M] [SetStructure M] [M↓[ℒₛₑₜ] ⊧* seedTheory]

theorem seed_irreflexive (x : M) : x ∉ x := by
  have h : M↓[ℒₛₑₜ] ⊧ irreflexiveSentence := models_of_mem (T := seedTheory) (Or.inl (Or.inr rfl))
  intro hx
  have h' := h
  simp [models_iff, irreflexiveSentence] at h'
  exact h' x hx

/-- The seed schema instance for the translated matrix of a native formula. -/
theorem seed_formSeed : KLower.FormSeed (memRel M) := by
  intro φ env A
  have h := models_iff_proposition.mp
    (models_of_mem (T := seedTheory) (Or.inr ⟨toSet 2 φ, rfl⟩)) env
  have key : ∀ x y : M, (toSet 2 φ).Eval ![y, x] env ↔
      Sat (memRel M) (scons y (scons x env)) φ := fun x y =>
    eval_toSet φ 2 ![y, x] env _ (fun i => by
      match i with
      | 0 => rfl
      | 1 => rfl) (fun j => by rw [Nat.add_comm]; rfl)
  simp [fullSeedBodyMeta, seedSubset, seedMem, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton] at h
  obtain ⟨C, hclos, hroot⟩ := h A
  refine ⟨C, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, hzC⟩ := hroot y ((key A y).2 hy)
    exact ⟨z, (key A z).1 hz, hzC⟩
  · obtain ⟨⟨x, hx⟩, hcl⟩ := hclos y hy
    refine ⟨x, (key x y).1 hx, fun x' hsub y' hy' => ?_⟩
    obtain ⟨z, hz, hzC⟩ := hcl x' hsub y' ((key x' y').2 hy')
    exact ⟨z, (key x' z).1 hz, hzC⟩

end Seed

/-! ## The tagged image of `qAx` -/

section Tagged

open ValidatorFullSeedTheory222
attribute [local instance] ValidatorSeedFixedImages222.tagStructure

theorem qAx_taggedValid : ValidatorSeedFixedImages222.TaggedValid seedTheory qAx := by
  intro M _ _ _ t ht
  have hs := seed_formSeed (M := M)
  have hirr : ∀ x : M, ¬ memRel M x x := seed_irreflexive
  have hqh : KQHyp.QHyp (KLower.tmem (memRel M) t) := KLower.tag_qhyp hs hirr ht
  obtain ⟨x0, hx0⟩ := KLower.tag_inhabited hs hirr ht
  haveI : Nonempty {x : M // t ∈ x} := ⟨⟨x0, hx0⟩⟩
  have hf : QFields (memRel {x : M // t ∈ x}) := qfields_of_qhyp hqh
  have hm : {x : M // t ∈ x}↓[ℒₛₑₜ] ⊧ qAx :=
    models_univCl_of_sat qForm fun e => (sat_qForm _ e).mpr hf
  simpa [models_iff] using hm

end Tagged

/-! ## Internal axiom images and the refutation transfer -/

section Internal

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open ValidatorFullSeedTheory222 ValidatorSeedMarkerDischarge222
open ValidatorSeedMarkerRelativization222 ValidatorSeedLogicalImages222

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Every internal `qTheory` axiom has its tagged image.** -/
theorem axiomImages_qTheory : AxiomImages qTheory V := by
  intro p j hp hm hj
  change V ⊧/![p] (logicalTheory_delta1.ch ⋎ (Theory.Δ₁.singleton qAx).ch).val at hm
  simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq] at hm
  rcases hm with hl | hq
  · exact axiomImages_logicalTheory p j hp hl hj
  · have hq' : p = ORingStructure.numeral (Encodable.encode qAx) := by simpa using hq
    rw [hq', numeral_eq_natCast_app, ← LO.FirstOrder.Sentence.quote_eq_encode] at hp ⊢
    exact ValidatorSeedFixedImages222.fixed_image_derivable qAx qAx_taggedValid j

theorem provable_falsum_of_qTheory (h : Provable qTheory (^⊥ : V)) :
    Provable seedTheory (^⊥ : V) :=
  provable_falsum_of_tagged axiomImages_qTheory h

theorem qTheory_refutation_witness
    (h : Provable qTheory (^⊥ : V)) :
    ∃ d : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value d = 2 :=
  ValidatorSeedMarkerRelativization222.refutation_witness axiomImages_qTheory h

end Internal

end LeanProofs.ZFCinPA.ValidatorSeedQTheory222
