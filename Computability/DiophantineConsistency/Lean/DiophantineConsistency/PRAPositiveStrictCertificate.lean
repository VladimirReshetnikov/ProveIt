import DiophantineConsistency.PRAPositiveCode
import DiophantineConsistency.PRAConditionalSigmaNormalization
import DiophantineConsistency.PRATwoParameterInductionTransfer
import DiophantineConsistency.ParsonsMapInduction
/-! Every positive arithmetic predicate has a strict bounded-induction
certificate, uniformly including the case of no free parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAPositiveStrictCertificate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation
  PRAPositiveCode PRAConditionalSigmaNormalization PRAFiniteMultiParameterInduction
  PRAISigmaOneFiniteTranslation PRAMultiParameterInduction PRAParameterPackingN
  PRATwoParameterInductionTransfer ParsonsMapInduction

def codeArgs (n : ℕ) : Fin (n+2) → Semiterm language Empty (3+n) :=
  Fin.cases (#0) (Fin.cases (#1) (fun i : Fin n => .bvar (Fin.natAdd 3 i)))

def codeMatrix {n : ℕ} (pred : Code (n+2)) : Semisentence language (3+n) :=
  Semiformula.rel Language.ORing.Rel.eq ![.func pred (codeArgs n),.func oneCode Fin.elim0]

def codeDescriptor {n : ℕ} (pred : Code (n+2)) : Descriptor := ⟨n,codeMatrix pred⟩

theorem codeMatrix_bounded {n : ℕ} (pred : Code (n+2)) : Hierarchy 𝚺 0 (codeMatrix pred) := by
  simp [codeMatrix]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelCodeMatrix {n : ℕ} (pred : Code (n+2)) (x y z : M) (v : Fin n → M) :
    (codeMatrix pred).Eval (Fin.append ![x,y,z] v) Empty.elim ↔
      Structure.func (L := language) pred (Fin.cases x (Fin.cases y v)) =
        Structure.func (L := language) oneCode Fin.elim0 := by
  simp only [codeMatrix, Semiformula.eval_rel, eqRel]
  change Structure.func (L := language) pred (Semiterm.val (Fin.append ![x,y,z] v) Empty.elim ∘ codeArgs n) =
    Structure.func (L := language) oneCode (Semiterm.val (Fin.append ![x,y,z] v) Empty.elim ∘ Fin.elim0) ↔ _
  have hz : (Semiterm.val (L := language) (Fin.append ![x,y,z] v) Empty.elim ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have i0 : (0 : Fin (3+n)) = Fin.castAdd n (0 : Fin 3) := by
    apply Fin.ext
    change 0 % (3+n) = 0
    exact Nat.zero_mod _
  have i1 : (1 : Fin (3+n)) = Fin.castAdd n (1 : Fin 3) := by
    apply Fin.ext
    change 1 % (3+n) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hv0 : (Fin.append ![x,y,z] v) 0 = x := by simp [i0,Fin.append_left]
  have hv1 : (Fin.append ![x,y,z] v) 1 = y := by simp [i1,Fin.append_left]
  have hv : (Semiterm.val (L := language) (Fin.append ![x,y,z] v) Empty.elim ∘ codeArgs n) =
      Fin.cases x (Fin.cases y v) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (Fin.append ![x,y,z] v) 0 = x
      exact hv0
    · refine Fin.cases ?_ (fun k => ?_) j
      · change (Fin.append ![x,y,z] v) 1 = y
        exact hv1
      · change (Fin.append ![x,y,z] v) (Fin.natAdd 3 k) = v k
        exact Fin.append_right _ _ k
  rw [hv,hz]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelCodeSigma {n : ℕ} (pred : Code (n+2)) (x : M) (e : ℕ → M) :
    (multiSigma n (codeMatrix pred)).Eval ![x] e ↔
      ∃ y : M, Structure.func (L := language) pred
        (Fin.cases x (Fin.cases y (fun i : Fin n => e (i.val+1)))) =
        Structure.func (L := language) oneCode Fin.elim0 := by
  rw [modelMultiSigma]
  apply exists_congr
  intro y
  exact modelCodeMatrix pred x y (e 0) (fun i => e (i.val+1))

/-- The descriptor's first free induction parameter is ignored; shifting the
original finite parameters into the remaining slots works also when n=0. -/
theorem modelCodeInduction (φ : ArithmeticSemiformula ℕ 1)
    (pred : Code ((Semiformula.lMap embedding φ).fvSup+2))
    (hc : ∀ (x : M) (e : ℕ → M),
      (Semiformula.lMap embedding φ).Eval ![x] e ↔
        ∃ y : M, Structure.func (L := language) pred
          (Fin.cases x (Fin.cases y (fun i : Fin (Semiformula.lMap embedding φ).fvSup => e i.val))) =
          Structure.func (L := language) oneCode Fin.elim0)
    (h : M↓[language] ⊧ strictAxiom (codeDescriptor pred)) :
    M↓[language] ⊧ mappedInduction φ := by
  simp only [strictAxiom, codeDescriptor, models_iff, Semiformula.eval_univCl] at h
  simp only [mappedInduction, map_succInd, models_iff, Semiformula.eval_univCl]
  intro e
  let e' : ℕ → M := fun i => e (i-1)
  have he (i : Fin (Semiformula.lMap embedding φ).fvSup) : e' (i.val+1) = e i.val := by
    simp [e']
  have hpred (x : M) : (multiSigma _ (codeMatrix pred)).Eval ![x] e' ↔
      (Semiformula.lMap embedding φ).Eval ![x] e := by
    rw [modelCodeSigma, hc x e]
    simp only [he]
  have hi := (modelSuccInd _ e').mp (h e')
  apply (modelSuccInd _ e).mpr
  intro hb hs x
  apply (hpred x).mp
  apply hi ((hpred _).mpr hb)
  intro z hz
  exact (hpred _).mpr (hs z ((hpred z).mp hz))
end models

theorem positive_certificate (φ : ArithmeticSemiformula ℕ 1)
    (hφ : ParsonsBasePositive.Positive φ) : Certificate φ := by
  obtain ⟨pred,hpred⟩ := positive_has_code φ hφ
  refine ⟨codeDescriptor pred, codeMatrix_bounded pred, ?_⟩
  letI : 𝗘𝗤 language ⪯ (PRA ∪ {strictAxiom (codeDescriptor pred)}) :=
    Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hBoth
  letI : M↓[language] ⊧* PRA := by
    constructor
    intro σ hσ
    exact hBoth.models _ (Or.inl hσ)
  exact modelCodeInduction φ pred (hpred M) (hBoth.models _ (Or.inr rfl))
end DiophantineConsistency.PRAPositiveStrictCertificate
