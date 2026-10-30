import DiophantineConsistency.PRAConditionalSigmaNormalization
import DiophantineConsistency.PRAFormulaParameters
import DiophantineConsistency.PRABoundedInduction
import DiophantineConsistency.ParsonsHierarchyMap
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAStrictSigmaCertificate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAFormulaParameters PRABoundedInduction
  PRAConditionalSigmaNormalization PRAFiniteMultiParameterInduction
  PRAMultiParameterInduction PRAParameterPackingIteration PRAISigmaOneFiniteTranslation

def matrixSub (k : ℕ) : Fin (2+k) → Semiterm language Empty (3+k) :=
  Fin.append ![#1,#0] (fun i => .bvar ⟨2+i.val, by omega⟩)

def matrix (D : ArithmeticSemiformula ℕ 2) :
    Semisentence language (3 + (Semiformula.lMap embedding D).fvSup) :=
  Rew.embSubsts (matrixSub (Semiformula.lMap embedding D).fvSup) ▹
    packParameters (Semiformula.lMap embedding D)

def descriptor (D : ArithmeticSemiformula ℕ 2) : Descriptor :=
  ⟨(Semiformula.lMap embedding D).fvSup, matrix D⟩

theorem matrix_bounded (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D) :
    Hierarchy 𝚺 0 (descriptor D).matrix := by
  exact Hierarchy.rew _ (packParameters_bounded (Semiformula.lMap embedding D)
    (ParsonsHierarchyMap.hierarchy hD))
theorem parameter_projection {M : Type} [Structure language M] (k : ℕ) (x y : M) (e : ℕ → M) :
    (Semiterm.val (L := language) (parameterVal k x y (fun i => e i.val)) Empty.elim ∘ matrixSub k) =
      Fin.append ![y,x] (fun i : Fin k => e i.val) := by
  let v := parameterVal k x y (fun i => e i.val)
  have i0 : (0 : Fin (3+k)) = Fin.castAdd k (0 : Fin 3) := by
    apply Fin.ext
    change 0 % (3+k) = 0
    exact Nat.zero_mod _
  have i1 : (1 : Fin (3+k)) = Fin.castAdd k (1 : Fin 3) := by
    apply Fin.ext
    change 1 % (3+k) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hv0 : v 0 = x := by simp [v,parameterVal,i0,Fin.append_left]
  have hv1 : v 1 = y := by simp [v,parameterVal,i1,Fin.append_left]
  have hvfree (i : Fin k) : v ⟨2+i.val, by omega⟩ = e i.val := by
    by_cases hi : i.val = 0
    · have hidx : (⟨2+i.val, by omega⟩ : Fin (3+k)) = Fin.castAdd k (2 : Fin 3) := by
        apply Fin.ext
        simp [hi]
      rw [hidx]
      simp [v,parameterVal,Fin.append_left,hi]
    · let j : Fin k := ⟨i.val-1, by omega⟩
      have hidx : (⟨2+i.val, by omega⟩ : Fin (3+k)) = Fin.natAdd 3 j := by
        apply Fin.ext
        simp [j]
        omega
      rw [hidx]
      change (Fin.append ![x,y,e 0] (fun q : Fin k => e q.succ.val)) (Fin.natAdd 3 j) = e i.val
      rw [Fin.append_right]
      have hj : j.succ.val = i.val := by simp [j]; omega
      rw [hj]
  funext i
  induction i using Fin.addCases with
  | left i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [matrixSub,Fin.append_left] using hv1
    · refine Fin.cases ?_ (fun z => Fin.elim0 z) j
      simpa [matrixSub,Fin.append_left] using hv0
  | right i => simpa [matrixSub,Fin.append_right] using hvfree i
theorem packedEval2 {M : Type} [Structure language M] (A : Semiproposition language 2)
    (x y : M) (e : ℕ → M) :
    (packParameters A).Eval (Fin.append ![y,x] (fun i => e i.val)) Empty.elim ↔ A.Eval ![y,x] e := by
  rw [packParameters_eval A _ (fun i => e (i + A.fvSup))]
  have hb : (fun i : Fin 2 => (Fin.append ![y,x] (fun j : Fin A.fvSup => e j.val))
      (i.castAdd A.fvSup)) = ![y,x] := by
    funext i
    exact Fin.append_left _ _ i
  have hf : (fun i => if hi : i < A.fvSup then
      (Fin.append ![y,x] (fun j : Fin A.fvSup => e j.val)) (Fin.natAdd 2 ⟨i,hi⟩)
      else e ((i - A.fvSup) + A.fvSup)) = e := by
    funext i
    by_cases hi : i < A.fvSup
    · simp only [hi, ↓reduceDIte, Fin.append_right]
    · simp only [hi, ↓reduceDIte]
      congr 1
      omega
  rw [hb,hf]

theorem matrix_eval {M : Type} [Structure language M] (D : ArithmeticSemiformula ℕ 2)
    (x y : M) (e : ℕ → M) :
    (matrix D).Eval (parameterVal (Semiformula.lMap embedding D).fvSup x y (fun i => e i.val)) Empty.elim ↔
      (Semiformula.lMap embedding D).Eval ![y,x] e := by
  unfold matrix
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := language)
      (parameterVal (Semiformula.lMap embedding D).fvSup x y (fun i => e i.val)) Empty.elim ∘
      Rew.embSubsts (matrixSub (Semiformula.lMap embedding D).fvSup) ∘ Semiterm.bvar) =
        Fin.append ![y,x] (fun i => e i.val) := by
    simpa only [Function.comp_def,Rew.embSubsts_bvar] using
      parameter_projection (Semiformula.lMap embedding D).fvSup x y e
  have hf : (Semiterm.val (L := language)
      (parameterVal (Semiformula.lMap embedding D).fvSup x y (fun i => e i.val)) Empty.elim ∘
      Rew.embSubsts (matrixSub (Semiformula.lMap embedding D).fvSup) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hb,hf]
  exact packedEval2 (Semiformula.lMap embedding D) x y e
theorem predicate_eval {M : Type} [Structure language M] (D : ArithmeticSemiformula ℕ 2)
    (x : M) (e : ℕ → M) :
    (multiSigma (descriptor D).arity (descriptor D).matrix).Eval ![x] e ↔
      (Semiformula.lMap embedding (∃⁰ D)).Eval ![x] e := by
  rw [modelMultiSigma]
  simp only [Semiformula.lMap_exs, Semiformula.eval_ex]
  apply exists_congr
  intro y
  exact matrix_eval D x y e

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelStrictInduction (D : ArithmeticSemiformula ℕ 2)
    (h : M↓[language] ⊧ strictAxiom (descriptor D)) :
    M↓[language] ⊧ mappedInduction (∃⁰ D) := by
  simp only [strictAxiom, models_iff, Semiformula.eval_univCl] at h
  simp only [mappedInduction, ParsonsMapInduction.map_succInd, models_iff, Semiformula.eval_univCl]
  intro e
  have hc (x : M) := predicate_eval D x e
  have hi := (PRATwoParameterInductionTransfer.modelSuccInd _ e).mp (h e)
  apply (PRATwoParameterInductionTransfer.modelSuccInd _ e).mpr
  intro hb hs x
  apply (hc x).mp
  apply hi ((hc _).mpr hb)
  intro z hz
  exact (hc _).mpr (hs z ((hc z).mp hz))
end models

theorem strict_certificate (D : ArithmeticSemiformula ℕ 2) (hD : Hierarchy 𝚺 0 D) :
    Certificate (∃⁰ D) := by
  refine ⟨descriptor D, matrix_bounded D hD, ?_⟩
  letI : 𝗘𝗤 language ⪯ (PRA ∪ {strictAxiom (descriptor D)}) :=
    Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hBoth
  letI : M↓[language] ⊧* PRA := by
    constructor
    intro σ hσ
    exact hBoth.models _ (Or.inl hσ)
  exact modelStrictInduction D (hBoth.models _ (Or.inr rfl))
end DiophantineConsistency.PRAStrictSigmaCertificate
