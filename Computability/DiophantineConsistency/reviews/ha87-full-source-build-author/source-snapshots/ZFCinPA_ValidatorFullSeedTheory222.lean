import ZFCinPA.OpenedClosure
import ZFCinPA.SchemaClosure
import ZFCinPA.ValidatorSourceFullSeed222
import ZFCinPA.ValidatorEqualityImages222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! The actual full-seed schema, with a concrete Δ₁ recognizer and all
internal axiom images in C222. The source theory is explicitly new; it is
not identified with raw GIC, containers, or the later tagged quotient. -/
namespace LeanProofs.ZFCinPA.ValidatorFullSeedTheory222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorSourceFullSeed222 ValidatorProvability222 ValidatorFormulaEncoder222
open ValidatorEnvironmentStreams222 ValidatorEnvironmentAlpha222 ValidatorEnvironmentVacuity222
open ValidatorQuantifierRules222 ValidatorEqualityImages222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The theory retains the frozen body and closes ALL its free parameters. -/
def seedSchema : SetTheory :=
  Set.range (fun K : SetTheorySemiproposition 2 => (fullSeedBodyMeta K).univCl)

def seedRecognizerBodyMeta (K : SetTheorySemiproposition 2) : SetTheoryProposition :=
  fullSeedBodyMeta (∼K)
def seedRecognizerBodyVal (k : V) : V :=
  fullSeedBodyVal (Bootstrapping.neg ℒₛₑₜ k)

theorem seedSchema_eq_negRange : seedSchema =
    Set.range (fun K : SetTheorySemiproposition 2 => (seedRecognizerBodyMeta K).univCl) := by
  ext σ
  constructor
  · rintro ⟨K,rfl⟩
    refine ⟨∼K,?_⟩
    simp [seedRecognizerBodyMeta]
  · rintro ⟨K,rfl⟩
    exact ⟨∼K,rfl⟩

private theorem quote_negative {n : ℕ} (K : SetTheorySemiproposition n) :
    (⌜∼K⌝ : V)=Bootstrapping.neg ℒₛₑₜ (⌜K⌝ : V) := by
  simp [FirstOrder.Semiformula.quote_def]

theorem recognizerBody_quote (K : SetTheorySemiproposition 2) :
    seedRecognizerBodyVal (⌜K⌝ : V) = (⌜seedRecognizerBodyMeta K⌝ : V) := by
  unfold seedRecognizerBodyVal seedRecognizerBodyMeta
  rw [←quote_negative,fullSeedBodyVal_quote]

private theorem subst01_quote (K : SetTheorySemiproposition 2) :
    subst ℒₛₑₜ ((^#0∷^#1∷0) : ℕ) (⌜K⌝ : ℕ) = ⌜K⌝ := by
  apply Bootstrapping.subst_eq_self (FirstOrder.Semiformula.quote_isSemiformula K) (by simp)
  intro i hi
  have : i=0 ∨ i=1 := by omega
  rcases this with rfl | rfl <;> simp

theorem neg_subst_le_fullSeedBody (k : V) :
    Bootstrapping.neg ℒₛₑₜ (subst ℒₛₑₜ (^#0∷^#1∷0) k) ≤ fullSeedBodyVal k := by
  unfold fullSeedBodyVal Bootstrapping.imp
  exact le_of_lt <| lt_trans (lt_or_left _ _) <| lt_trans (lt_forall _) <|
    lt_trans (lt_or_right _ _) <| lt_trans (lt_forall _) <|
    lt_trans (lt_K!_right _ _) <| lt_trans (lt_exists _) <|
    lt_trans (lt_or_right _ _) <| lt_trans (lt_forall _) <|
    lt_trans (lt_K!_left _ _) <| lt_trans (lt_exists _) (lt_forall _)

/-- Negating the parameter exposes its identity copy positively. This is
only a recognizer parameterization; the theory itself is unchanged. -/
theorem recognizerBody_quote_bound (K : SetTheorySemiproposition 2) :
    (⌜K⌝ : ℕ) ≤ seedRecognizerBodyVal (⌜K⌝ : ℕ) := by
  have h := neg_subst_le_fullSeedBody (V := ℕ) (⌜∼K⌝ : ℕ)
  rw [subst01_quote,quote_negative] at h
  have hk := FirstOrder.Semiformula.quote_isSemiformula (V := ℕ) K
  rw [hk.isUFormula.neg_neg] at h
  exact (le_def.mp h).elim Nat.le_of_eq Nat.le_of_lt

private def mem01Code : ℕ := ⌜seedMem 3 0 1⌝
private def mem05Code : ℕ := ⌜seedMem 7 0 5⌝
private def mem02Code : ℕ := ⌜seedMem 4 0 2⌝
private def subsetCode : ℕ := ⌜seedSubset⌝

private def matrixAt (i j k : V) : V := subst ℒₛₑₜ (^#i∷^#j∷0) k
private def matrixAtGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out i j k. ∃ bi bj tail vec,
    !qqBvarDef bi i ∧ !qqBvarDef bj j ∧ !adjoinDef tail bj 0 ∧
      !adjoinDef vec bi tail ∧ !(Bootstrapping.substsGraph ℒₛₑₜ) out vec k”
private instance matrixAt_defined : 𝚺₁-Function₃ (matrixAt : V→V→V→V) via matrixAtGraph :=
  .mk fun v => by simp [matrixAtGraph,matrixAt]

private def leftBody (k : V) : V :=
  ^∀ (Bootstrapping.imp ℒₛₑₜ ((mem01Code : ℕ) : V) (^∃
    ((matrixAt 1 0 k) ^⋏ ^∀ (Bootstrapping.imp ℒₛₑₜ ((subsetCode : ℕ) : V)
      (^∀ (Bootstrapping.imp ℒₛₑₜ (matrixAt 0 1 k)
        (^∃ ((matrixAt 0 2 k) ^⋏ ((mem05Code : ℕ) : V)))))))))
private def leftBodyGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out k. ∃ s10 s01 s02,
    !matrixAtGraph s10 1 0 k ∧ !matrixAtGraph s01 0 1 k ∧ !matrixAtGraph s02 0 2 k ∧
    ∃ c7 e7 i6 a6 i5 a5 c4 e4 i3,
      !qqAndDef c7 s02 ↑mem05Code ∧ !qqExsDef e7 c7 ∧
      !(Bootstrapping.impGraph ℒₛₑₜ) i6 s01 e7 ∧ !qqAllDef a6 i6 ∧
      !(Bootstrapping.impGraph ℒₛₑₜ) i5 ↑subsetCode a6 ∧ !qqAllDef a5 i5 ∧
      !qqAndDef c4 s10 a5 ∧ !qqExsDef e4 c4 ∧
      !(Bootstrapping.impGraph ℒₛₑₜ) i3 ↑mem01Code e4 ∧ !qqAllDef out i3”
private instance leftBody_defined : 𝚺₁-Function₁ (leftBody : V→V) via leftBodyGraph :=
  .mk fun v => by
    simp [leftBodyGraph,leftBody,numeral_eq_natCast]

private def rightBody (k : V) : V :=
  ^∀ (Bootstrapping.imp ℒₛₑₜ (matrixAt 0 2 k)
    (^∃ ((matrixAt 0 3 k) ^⋏ ((mem02Code : ℕ) : V))))
private def rightBodyGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out k. ∃ s02 s03, !matrixAtGraph s02 0 2 k ∧ !matrixAtGraph s03 0 3 k ∧
    ∃ cr er ir, !qqAndDef cr s03 ↑mem02Code ∧ !qqExsDef er cr ∧
      !(Bootstrapping.impGraph ℒₛₑₜ) ir s02 er ∧ !qqAllDef out ir”
private instance rightBody_defined : 𝚺₁-Function₁ (rightBody : V→V) via rightBodyGraph :=
  .mk fun v => by
    simp [rightBodyGraph,rightBody,numeral_eq_natCast]

private lemma mem01_cast : ((mem01Code : ℕ) : V)=(⌜seedMem 3 0 1⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote (seedMem 3 0 1)
private lemma mem05_cast : ((mem05Code : ℕ) : V)=(⌜seedMem 7 0 5⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote (seedMem 7 0 5)
private lemma mem02_cast : ((mem02Code : ℕ) : V)=(⌜seedMem 4 0 2⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote (seedMem 4 0 2)
private lemma subset_cast : ((subsetCode : ℕ) : V)=(⌜seedSubset⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote seedSubset

/-- Fixed finite graph of the actual negative-parameter full body. Its two
sides preserve all five matrix occurrences, with [0,2] occurring twice. -/
def recognizerBodyGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out k. ∃ nk l r co eo, !(Bootstrapping.negGraph ℒₛₑₜ) nk k ∧
    !leftBodyGraph l nk ∧ !rightBodyGraph r nk ∧
      !qqAndDef co l r ∧ !qqExsDef eo co ∧ !qqAllDef out eo”

instance recognizerBody_defined :
    𝚺₁-Function₁ (seedRecognizerBodyVal : V→V) via recognizerBodyGraph :=
  .mk fun v => by
    simp [recognizerBodyGraph,seedRecognizerBodyVal,fullSeedBodyVal,leftBody,rightBody,matrixAt,
      mem01_cast,mem05_cast,mem02_cast,subset_cast]

/-- Literal bounded closure recognizer, with both total-graph presentations. -/
def seedCh : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ m < p+1, ∃ b < p+1,
      !qqAllsDef p b m ∧ !(Bootstrapping.isUFormula ℒₛₑₜ).sigma b ∧
      !(Bootstrapping.shiftGraph ℒₛₑₜ) b b ∧ !(Bootstrapping.bvGraph ℒₛₑₜ) m b ∧
      ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(Bootstrapping.substsGraph ℒₛₑₜ) s fv b ∧
      ∃ K < s+1, !(Bootstrapping.isSemiformula ℒₛₑₜ).sigma 2 K ∧ !recognizerBodyGraph s K”)
  (.mkPi “p.
    ∃ m < p+1, ∃ b < p+1,
      (∀ y, !qqAllsDef y b m → y=p) ∧ !(Bootstrapping.isUFormula ℒₛₑₜ).pi b ∧
      (∀ y, !(Bootstrapping.shiftGraph ℒₛₑₜ) y b → y=b) ∧
      (∀ y, !(Bootstrapping.bvGraph ℒₛₑₜ) y b → y=m) ∧
      ∀ fv, !fvarVecDef fv m → ∀ s, !(Bootstrapping.substsGraph ℒₛₑₜ) s fv b →
      ∃ K < s+1, !(Bootstrapping.isSemiformula ℒₛₑₜ).pi 2 K ∧
        ∀ ib, !recognizerBodyGraph ib K → s=ib”)

abbrev SeedR : V→Prop := SchemaRecognizer ℒₛₑₜ 2 seedRecognizerBodyVal
instance seedR_defined : 𝚫₁-Predicate[V] (SeedR : V→Prop) via seedCh := .mk <| by
  constructor
  · intro v
    simp [seedCh,HierarchySymbol.Semiformula.val_sigma,eq_comm]
  · intro v
    simp [seedCh,HierarchySymbol.Semiformula.val_sigma,SchemaRecognizer,
      lt_succ_iff_le,eq_comm,Nat.cast_ofNat]

instance seedSchema_delta1 : seedSchema.Δ₁ where
  ch := seedCh
  mem_iff φ := by
    have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] seedCh.val) ↔ SeedR (⌜φ⌝ : ℕ) := by simp
    rw [h,show SeedR (⌜φ⌝ : ℕ)=
      SchemaRecognizer ℒₛₑₜ 2 seedRecognizerBodyVal (⌜φ⌝ : ℕ) from rfl,
      schemaRecognizer_quote_iff seedRecognizerBodyMeta seedRecognizerBodyVal
        (recognizerBody_quote (V := ℕ)) recognizerBody_quote_bound φ,
      seedSchema_eq_negRange]
    exact (mem_range_univCl_iff seedRecognizerBodyMeta φ).symm
  isDelta1 := HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun W _ _ => by
    haveI := seedR_defined (V := W)
    simp

private lemma fvarVec_isTermVec (slots : V) :
    IsSemitermVec ℒₛₑₜ slots 0 (fvarVec slots) :=
  ModelCodedBindFree.fvarVec_isTermVec slots

private lemma shift_qqAlls {body : V} (hb : IsUFormula ℒₛₑₜ body) (count : V) :
    shift ℒₛₑₜ (qqAlls body count)=qqAlls (shift ℒₛₑₜ body) count :=
  OpenedClosure.shift_qqAlls hb count

private theorem free_subst_qVec_fvarVec {k B : V}
    (hB : IsSemiformula ℒₛₑₜ (k+1) B) (hs : shift ℒₛₑₜ B=B) :
    free ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ (fvarVec k)) B)=
      subst ℒₛₑₜ (fvarVec (k+1)) B :=
  OpenedClosure.free_subst_qVec_fvarVec hB hs

section Images

def pc (s m b F i : V) : V :=
  encode F 0 s (subst ℒₛₑₜ (fvarVec (m-i)) (qqAlls b i))

private instance avoid_delta : 𝚫₁-Relation[V] Avoid := by unfold Avoid; definability
private instance free_delta : 𝚫₁-Relation[V] FreeAvoid := by unfold FreeAvoid; definability
private instance streamFree_pi1 : 𝚷₁-Relation[V] StreamFree := by unfold StreamFree; definability

/-- Every length is internal. Free parameters are varied at each actual
ALL step; no fixed-context GEN or standard-length induction is used. Each step
extends the free environment by one eigenlabel, so the parameter stays below
`alternateStart F s ∷ F` and bounded-parameter order induction in IΣ₁ applies. -/
theorem closure_image {m b s : V} (hb : IsSemiformula ℒₛₑₜ m b)
    (hbs : shift ℒₛₑₜ b=b)
    (base : ∀ F : V, StreamFree s F →
      CProv (encode F 0 s (subst ℒₛₑₜ (fvarVec m) b))) :
    ∀ F : V, StreamFree s F → CProv (encode F 0 s (qqAlls b m)) := by
  haveI hpc : 𝚺₁-Function₂[V] (fun F i => pc s m b F i) := by unfold pc; definability
  have key : ∀ i F : V, i≤m → StreamFree s F → CProv (pc s m b F i) := by
    refine bounded_all_sigma1_order_induction' (f := fun F => alternateStart F s ∷ F)
      (P := fun i F => i≤m → StreamFree s F → CProv (pc s m b F i))
      (by definability) (by definability) ?_
    intro i F ih hi hF
    rcases zero_or_succ i with rfl | ⟨j,rfl⟩
    · simpa [pc] using base F hF
    · obtain ⟨k,rfl⟩ : ∃ k, m=k+(j+1) := ⟨m-(j+1),(tsub_add_cancel_of_le hi).symm⟩
      have e1 : k+(j+1)-j=k+1 := by
        rw [add_comm j 1,←add_assoc,add_tsub_cancel_right]
      have hB : IsSemiformula ℒₛₑₜ (k+1) (qqAlls b j) :=
        IsSemiformula.qqAlls (by rwa [add_assoc,add_comm 1 j])
      have hBs : shift ℒₛₑₜ (qqAlls b j)=qqAlls b j := by
        rw [shift_qqAlls hb.isUFormula,hbs]
      have hf := fvarVec_isTermVec (V := V) k
      have hw : IsSemitermVec ℒₛₑₜ (k+1) 1 (qVec ℒₛₑₜ (fvarVec k)) := by simpa using hf.qVec
      have hq : IsSemiformula ℒₛₑₜ 1
          (subst ℒₛₑₜ (qVec ℒₛₑₜ (fvarVec k)) (qqAlls b j)) := hB.subst hw
      have ih' := ih j (by simp) (eigen F s∷F) le_rfl (le_trans (by simp) hi)
        (fresh_resources F s hF).2.2.1
      simp only [pc,e1] at ih'
      rw [←free_subst_qVec_fvarVec hB hBs] at ih'
      simp only [pc,add_tsub_cancel_right]
      rw [qqAlls_succ,substs_all hB.isUFormula]
      exact all_rule hq F s hF ih'
  intro F hF
  have h := key m F le_rfl hF
  simp only [pc,tsub_self] at h
  have hc : IsSemiformula ℒₛₑₜ 0 (qqAlls b m) := IsSemiformula.qqAlls (by simpa using hb)
  rwa [subst_eq_self hc (fvarVec_isTermVec 0) (by simp)] at h

theorem recognized_seed_image {p : V} (hp : SeedR p) (F s : V)
    (hs : StreamFree s F) : CProv (encode F 0 s p) := by
  obtain ⟨m,_,b,_,rfl,hbu,hbs,hbv,K,_,hK,hbody⟩ := hp
  have hb : IsSemiformula ℒₛₑₜ m b := by
    rw [isSemiformula_iff]
    exact ⟨hbu,by simp [hbv]⟩
  apply closure_image hb hbs (s := s) _ F hs
  intro G hG
  rw [hbody]
  exact typed_fullSeed_image hK.neg G s hG

theorem axOK_seedSchema : ValidatorSourceDerivation222.AxOK seedSchema V := by
  intro p _ hp F s hs
  have hR : SeedR p := by
    change V ⊧/![p] seedCh.val at hp
    simpa using hp
  exact recognized_seed_image hR F s hs

end Images

def irreflexiveSentence : SetTheorySentence := “∀ x, x ∈ x → ⊥”
def seedTheory : SetTheory := ((𝗘𝗤 ℒₛₑₜ) ∪ {irreflexiveSentence}) ∪ seedSchema
instance seedTheory_delta1 : seedTheory.Δ₁ :=
  (equalityDelta.add (Theory.Δ₁.singleton irreflexiveSentence)).add seedSchema_delta1

theorem axOK_seedTheory :
    ValidatorSourceDerivation222.AxOK seedTheory V := by
  intro p hp hm F s hs
  change V ⊧/![p] ((equalityDelta.ch ⋎
    (Theory.Δ₁.singleton irreflexiveSentence).ch) ⋎ seedCh).val at hm
  simp only [HierarchySymbol.Semiformula.val_or,LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq] at hm
  rcases hm with (he|hi)|hseed
  · letI := equalityDelta
    exact axOK_equality p hp he F s hs
  · have hi' : p=ORingStructure.numeral (Encodable.encode irreflexiveSentence) := by simpa using hi
    rw [hi',numeral_eq_natCast_app,←LO.FirstOrder.Sentence.quote_eq_encode]
    exact irreflexivity_image F s
  · have hR : SeedR p := by simpa using hseed
    exact recognized_seed_image hR F s hs

theorem seedTheory_refutation_witness
    (h : Provable seedTheory (^⊥ : V)) :
    ∃ d : V, ArithmeticHistory222.value d=2 :=
  ValidatorSourceDerivation222.refutation_witness axOK_seedTheory h

end LeanProofs.ZFCinPA.ValidatorFullSeedTheory222
