import DiophantineConsistency.HerbrandInteractiveFourTriple
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandFourTriplePrenexAdapter
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandInteractiveFourTriple

/-- `φ` uses bound variables `[v,w,y,x,z₃,z₂,z₁,z₀]`; `χ` uses `[w,y,x,z₃,z₂,z₁,z₀]`. -/
def liftedGoal (φ : Semiproposition language 8) : Semiproposition language 8 :=
  φ

def liftedChallenge (χ : Semiproposition language 7) : Semiproposition language 8 :=
  Rew.subst ![#1, #2, #3, #4, #5, #6, #7] ▹ χ

def sourceMatrix (φ : Semiproposition language 8) (χ : Semiproposition language 7) : Semiproposition language 7 :=
  (∃⁰ liftedGoal φ) ⋎ χ

def negativePrefix (φ : Semiproposition language 8) (χ : Semiproposition language 7) : Semiproposition language 7 :=
  ∀⁰ (∼(liftedGoal φ ⋎ liftedChallenge χ))

theorem prefix_normalized (φ : Semiproposition language 8) (χ : Semiproposition language 7)
    (hφ : φ.Open) (hχ : χ.Open) : UniversalPrefix (negativePrefix φ χ) := by
  simp [negativePrefix, UniversalPrefix, Semiformula.Open, liftedGoal, liftedChallenge,
    PRAFormulaParameters.qr_rew] at hφ hχ ⊢
  simp_all

theorem matrix_equiv {M : Type} [Nonempty M] [Structure language M]
    (φ : Semiproposition language 8) (χ : Semiproposition language 7)
    (b : Fin 7 → M) (e : ℕ → M) :
    (sourceMatrix φ χ).Eval b e ↔ (∼(negativePrefix φ χ)).Eval b e := by
  have hshift (v : M) : (liftedChallenge χ).Eval (v :> b) e ↔ χ.Eval b e := by
    have hv : (Semiterm.val (L := language) (v :> b) e ∘ ![#1, #2, #3, #4, #5, #6, #7]) = b := by
      funext i
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      exact Fin.cases rfl (fun i => Fin.elim0 i) i
    simp [liftedChallenge, Semiformula.eval_substs, hv]
  change ((∃ v : M, (liftedGoal φ).Eval (v :> b) e) ∨ χ.Eval b e) ↔ _
  simp only [negativePrefix, LogicalConnective.HomClass.map_neg, Semiformula.eval_all]
  simp only [show ∀ v : M, (liftedGoal φ ⋎ liftedChallenge χ).Eval (v :> b) e ↔
      (liftedGoal φ).Eval (v :> b) e ∨ χ.Eval b e from fun v => by
        change ((liftedGoal φ).Eval (v :> b) e ∨ (liftedChallenge χ).Eval (v :> b) e) ↔ _
        rw [hshift v]]
  classical
  constructor
  · rintro (⟨v,hv⟩ | hχ) h
    · exact h v (Or.inl hv)
    · exact h (Classical.choice inferInstance) (Or.inr hχ)
  · intro h
    by_contra hn
    apply h
    intro v hv
    exact hn (hv.elim (fun hv => Or.inl ⟨v,hv⟩) Or.inr)
/-- Rewrites an actual proof into the syntactic universal-prefix shape required
by the unpaired interactive extractor. -/
theorem normalize_proof (φ : Semiproposition language 8) (χ : Semiproposition language 7)
    (p : UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (sourceMatrix φ χ)))))))).univCl) :
    UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (∼(negativePrefix φ χ))))))))).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hTheory
  have hmodel := models_of_provable hTheory p
  simp only [models_iff, Semiformula.eval_univCl, Semiformula.eval_ex,
    Semiformula.eval_all] at hmodel ⊢
  intro e
  obtain ⟨z₀,z₁,z₂,z₃,hz⟩ := hmodel e
  refine ⟨z₀,z₁,z₂,z₃, fun x y w => ?_⟩
  exact (matrix_equiv φ χ ![w,y,x,z₃,z₂,z₁,z₀] e).mp (hz x y w)

/-- The exact open target/challenge source shape feeds the staged extractor. -/
theorem extract (φ : Semiproposition language 8) (χ : Semiproposition language 7)
    (hφ : φ.Open) (hχ : χ.Open)
    (p : UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (sourceMatrix φ χ)))))))).univCl) :
    ∃ n, (UniversalAxiom ⊢ (output (negativePrefix φ χ).fvSup (negativePrefix φ χ) (List.range n)).univCl) ∧
      (∀ j k i, (HerbrandTupleSchedule.candidate j k).FVar? i → i < (negativePrefix φ χ).fvSup+3*j) ∧
      (∀ j i, (bad (negativePrefix φ χ).fvSup j (negativePrefix φ χ)).FVar? i →
        i ≤ (negativePrefix φ χ).fvSup+3*j+2) := by
  exact separated_interactive (negativePrefix φ χ) (prefix_normalized φ χ hφ hχ) (normalize_proof φ χ p)
end DiophantineConsistency.HerbrandFourTriplePrenexAdapter
