import DiophantineConsistency.PRAPositiveMapPack
/-! Bounded existential normal forms for positive arithmetic predicates with
all free parameters retained. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPositivePackedNormal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAFormulaParameters PRAPositiveNormalization PRAPositiveNormalize PRAPositiveMapPack

theorem packedEval1 {M : Type} [Structure language M] (A : Semiproposition language 1)
    (x : M) (e : ℕ → M) :
    (packParameters A).Eval (Fin.append ![x] (fun i => e i.val)) Empty.elim ↔ A.Eval ![x] e := by
  rw [packParameters_eval A _ (fun i => e (i + A.fvSup))]
  have hb : (fun i : Fin 1 => (Fin.append ![x] (fun j : Fin A.fvSup => e j.val))
      (i.castAdd A.fvSup)) = ![x] := by
    funext i
    exact Fin.append_left _ _ i
  have hf : (fun i => if hi : i < A.fvSup then
      (Fin.append ![x] (fun j : Fin A.fvSup => e j.val)) (Fin.natAdd 1 ⟨i,hi⟩)
      else e ((i - A.fvSup) + A.fvSup)) = e := by
    funext i
    by_cases hi : i < A.fvSup
    · simp only [hi, ↓reduceDIte, Fin.append_right]
    · simp only [hi, ↓reduceDIte]
      congr 1
      omega
  rw [hb,hf]

theorem exists_packed_normal (φ : ArithmeticSemiformula ℕ 1) (hφ : ParsonsBasePositive.Positive φ) :
    ∃ C : Semisentence language ((1 + (Semiformula.lMap embedding φ).fvSup)+1),
      Hierarchy 𝚺 0 C ∧
      ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
        [M↓[language] ⊧* PRA], ∀ (x : M) (e : ℕ → M),
          (Semiformula.lMap embedding φ).Eval ![x] e ↔
            ∃ y : M, C.Eval (Fin.cases y (Fin.append ![x] (fun i => e i.val))) Empty.elim := by
  let A := Semiformula.lMap embedding φ
  obtain ⟨N⟩ := exists_normal (packed A (mapped hφ))
  refine ⟨N.matrix,N.bounded, ?_⟩
  intro M _ _ _ _ x e
  exact (packedEval1 A x e).symm.trans (N.correct M (Fin.append ![x] (fun i => e i.val)))
end DiophantineConsistency.PRAPositivePackedNormal
