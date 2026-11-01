import DiophantineConsistency.PRAHistoryFixpointCollector
import DiophantineConsistency.PRAHistoryUnderExtension
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryUnderCanonical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRASelectCode
  PRACharacteristicBit PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness
  PRAHistoryFixpointCollector PRAPrimitiveRecursionInduction

def alwaysOne : Code 2 := .comp oneCode (.nil 2)
def underMatrix : Semisentence language 3 :=
  Rew.embSubsts ![#1,#0] ▹ Semiformula.lMap embedding underDef.val

theorem underMatrix_bounded : Hierarchy 𝚺 0 underMatrix :=
  Hierarchy.rew _ (ParsonsHierarchyMap.hierarchy underDef.sigma_prop)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelAlwaysOne (e : Fin 2 → M) : Structure.func (L := language) alwaysOne e =
    Structure.func (L := language) oneCode Fin.elim0 := by
  rw [alwaysOne,modelComposition]
  congr 1
  exact Subsingleton.elim _ _

theorem modelAlwaysBit : M↓[language] ⊧ bitSentence alwaysOne := by
  apply (bitSentence_iff alwaysOne).mpr
  intro e
  rw [modelAlwaysOne]
  exact Or.inr rfl
end models

theorem PRA_proves_alwaysBit : PRA ⊢ bitSentence alwaysOne := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelAlwaysBit

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [M↓[language] ⊧* PRA] in
theorem modelUnderMatrix (n d ih : M) :
    (underMatrix).Eval ![n,d,ih] Empty.elim ↔ underDef.val.Evalb ![d,n] := by
  rw [underMatrix,Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![n,d,ih] Empty.elim ∘
      Rew.embSubsts ![#1,#0] ∘ Semiterm.bvar) = ![d,n] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have he : (Semiterm.val (L := language) ![n,d,ih] Empty.elim ∘
      Rew.embSubsts ![#1,#0] ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]

theorem modelUnderCollector (ins : Code 2) (pred : Code 3)
    (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hpred : PRA ⊢ oneCorrectSentence pred underMatrix) (n ih : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    underDef.val.Evalb ![Structure.func (L := language) (collectCode alwaysOne ins) ![n,ih],n] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  have hp (x y : M) : Structure.func (L := language) pred ![x,y,ih] =
      Structure.func (L := language) oneCode Fin.elim0 ↔ underDef.val.Evalb ![y,x] := by
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hpred
    exact ((oneCorrectSentence_iff pred underMatrix).mp hm ![x,y,ih]).trans (modelUnderMatrix x y ih)
  let base : Code 1 := .comp (.zero 0) (.nil 1)
  let step := collectStep alwaysOne ins
  let e : ℕ → M := fun _ => ih
  have he : (fun i : Fin 1 => e i.val) = ![ih] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hzero : Structure.func (L := language) base ![ih] =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
    dsimp only [base]
    rw [modelComposition]
    congr 1
    exact Subsingleton.elim _ _
  have hbase : Structure.func (L := language) pred
      (Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0)
        (Fin.cases (Structure.func (L := language) base (fun i : Fin 1 => e i.val))
          (fun i : Fin 1 => e i.val))) = Structure.func (L := language) oneCode Fin.elim0 := by
    rw [he]
    change Structure.func (L := language) pred
      ![(0 : M),Structure.func (L := language) base ![ih],ih] = _
    rw [hzero]
    apply (hp 0 0).mpr
    simp [underDef, expDef, Semiformula.eval_substs]
  have hstep : ∀ x y : M, Structure.func (L := language) pred
      (Fin.cases x (Fin.cases y (fun i : Fin 1 => e i.val))) =
        Structure.func (L := language) oneCode Fin.elim0 →
      Structure.func (L := language) pred
        (Fin.cases (Structure.func (L := language) Code.succ (fun _ => x))
          (Fin.cases (Structure.func (L := language) step
            (Fin.cases x (Fin.cases y (fun i : Fin 1 => e i.val))))
            (fun i : Fin 1 => e i.val))) = Structure.func (L := language) oneCode Fin.elim0 := by
    intro x y hy
    rw [he] at hy ⊢
    change Structure.func (L := language) pred ![x,y,ih] = _ at hy
    change Structure.func (L := language) pred
      ![Structure.func (L := language) Code.succ (fun _ => x),
        Structure.func (L := language) step ![x,y,ih],ih] = _
    have hstepValue : Structure.func (L := language) step ![x,y,ih] =
        Structure.func (L := language) ins ![x,y] := by
      dsimp only [step]
      rw [collectStep,modelSelectAmong,modelBin,modelBin]
      simp only [modelProjection]
      rw [modelAlwaysOne,modelSelectOne]
      rfl
    rw [hstepValue,←modelAddOne]
    change Structure.func (L := language) pred ![x+1,Structure.func (L := language) ins ![x,y],ih] = _
    apply (hp (x+1) _).mpr
    have hgraph := PRAHistorySeqConsCode.modelInsert ins hins x y
    rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hgraph
    exact PRAHistoryUnderExtension.append_under y _ x ((hp x y).mp hy) hgraph
  have h := modelRecursiveWitness (M := M) pred base step e hbase hstep n
  rw [he] at h
  change Structure.func (L := language) pred
      ![n,Structure.func (L := language) (collectCode alwaysOne ins) ![n,ih],ih] = _ at h
  exact (hp n _).mp h
theorem modelUnderBits (d n i : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    underDef.val.Evalb ![d,n] → (bitDef.val.Evalb ![i,d] ↔ i < n) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  intro hd
  obtain ⟨ins,hins⟩ := PRAHistoryInsertCode.PRA_has_insertCode
  obtain ⟨pred,_,_,hpred⟩ := PRA_proves_boundedBooleanCharacteristic underMatrix underMatrix_bounded
  have hbnd : Hierarchy 𝚺 0 PRAHistoryInsertCode.bitGraph :=
    ParsonsHierarchyMap.hierarchy bitDef.sigma_prop
  obtain ⟨bit,_,_,hbit⟩ := PRA_proves_boundedBooleanCharacteristic PRAHistoryInsertCode.bitGraph hbnd
  let a := Structure.func (L := language) (collectCode alwaysOne ins) ![n,(0 : M)]
  have ha : underDef.val.Evalb ![a,n] := modelUnderCollector ins pred hins hpred n 0
  have hplus : d+1 = a+1 :=
    ((PRAHistoryUnderExtension.under_iff_exponential d n).mp hd).uniq
      ((PRAHistoryUnderExtension.under_iff_exponential a n).mp ha)
  have heq : d = a := add_right_cancel hplus
  rw [heq]
  have h := modelCollectInvariant alwaysOne ins bit PRA_proves_alwaysBit hins hbit n i (0 : M)
  rw [modelAlwaysOne] at h
  simpa [a] using h
end models

noncomputable def underBitsBody : ArithmeticSemisentence 2 :=
  “d n. !underDef d n → ∀ i, (i ∈ d ↔ i < n)”

theorem candidate_under_bits : PRA ⊢ Semiformula.lMap embedding (∀⁰* underBitsBody) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  rw [Semiformula.models_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  have h (hd : underDef.val.Evalb ![e 0,e 1]) (i : M) := modelUnderBits (e 0) (e 1) i hd
  simpa [underBitsBody, Semiformula.Operator.val, operator_mem_def,
    Semiformula.Operator.LT.sentence_eq, LogicalConnective.iff, iff_def] using h
end DiophantineConsistency.PRAHistoryUnderCanonical
