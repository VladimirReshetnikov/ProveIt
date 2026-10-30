import DiophantineConsistency.HerbrandExistentialPack
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandCommonParameters
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAFormulaParameters HerbrandUniversalTree HerbrandExistentialTreeRew HerbrandExistentialPack

private theorem fixed_no_free {n : ℕ} (φ : Semiproposition language n) (r : ℕ) (hr : φ.fvSup ≤ r) :
    (Rew.fixitr n r ▹ φ).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  rw [Rew.eq_bind (Rew.fixitr n r)]
  simp only [Function.comp_def, Rew.fixitr_bvar, Rew.fixitr_fvar, Fin.natAdd_mk]
  intro h
  rcases Semiformula.fvar?_rew h with (⟨z,hz⟩ | ⟨z,hz,hx⟩)
  · simp at hz
  · have hz' : z < r := lt_of_lt_of_le (Semiformula.lt_fvSup_of_fvar? hz) hr
    simp [hz'] at hx

def pack {n : ℕ} (φ : Semiproposition language n) (r : ℕ) (hr : φ.fvSup ≤ r) :
    Semisentence language (n + r) :=
  (Rew.fixitr n r ▹ φ).toEmpty (fixed_no_free φ r hr)

theorem pack_emb {n : ℕ} (φ : Semiproposition language n) (r : ℕ) (hr : φ.fvSup ≤ r) :
    (Rewriting.emb (pack φ r hr) : Semiproposition language (n+r)) = Rew.fixitr n r ▹ φ := by
  simp [pack]

theorem pack_open {n : ℕ} (φ : Semiproposition language n) (r : ℕ) (hr : φ.fvSup ≤ r)
    (h : φ.Open) : (pack φ r hr).Open := by
  have he := pack_emb φ r hr
  have hq := congrArg Semiformula.qr he
  have hb : (Rewriting.emb (pack φ r hr) : Semiproposition language _).qr = (pack φ r hr).qr :=
    qr_rew (pack φ r hr) (Rew.emb : Rew language Empty _ ℕ _)
  rw [hb, qr_rew] at hq
  exact hq.trans h

theorem pack_tree {n : ℕ} (φ : Semiproposition language n) (r : ℕ) (hr : φ.fvSup ≤ r)
    (h : ExistentialTree φ) : ExistentialTree (pack φ r hr) := by
  unfold pack
  apply toEmpty_tree
  exact existential_rew h _

theorem pack_eval {M : Type} [Structure language M] {n : ℕ}
    (φ : Semiproposition language n) (r : ℕ) (hr : φ.fvSup ≤ r)
    (v : Fin (n+r) → M) (fallback : ℕ → M) :
    (pack φ r hr).Eval v Empty.elim ↔
      φ.Eval (fun i => v (i.castAdd r))
        (fun i => if hi : i < r then v (Fin.natAdd n ⟨i,hi⟩) else fallback (i-r)) := by
  unfold pack
  rw [←Semiformula.eval_toEmpty (f := fallback) (fixed_no_free φ r hr)]
  rw [Semiformula.eval_rew]
  simp only [Function.comp_def, Rew.fixitr_bvar, Semiterm.val_bvar, Rew.fixitr_fvar]
  have heq : (fun i => Semiterm.val v fallback
      (if hi : i < r then (#(Fin.natAdd n ⟨i,hi⟩) : SyntacticSemiterm language (n+r)) else &(i-r))) =
      (fun i => if hi : i < r then v (Fin.natAdd n ⟨i,hi⟩) else fallback (i-r)) := by
    funext i
    split <;> rfl
  rw [heq]
end DiophantineConsistency.HerbrandCommonParameters
