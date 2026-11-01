import DiophantineConsistency.HerbrandGeneratedSubmodel
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandUniversalTree
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax HerbrandGeneratedSubmodel

/-- Positive Boolean combinations of universal-prefix formulas. -/
def UniversalTree {ξ : Type} : {n : ℕ} → Semiformula language ξ n → Prop
  | _, φ ⋏ ψ => UniversalTree φ ∧ UniversalTree ψ
  | _, φ ⋎ ψ => UniversalTree φ ∧ UniversalTree ψ
  | _, ∀⁰ φ => UniversalTree φ
  | _, φ => φ.Open

theorem open_tree {ξ : Type} {n : ℕ} (φ : Semiformula language ξ n) (h : φ.Open) : UniversalTree φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp [UniversalTree, Semiformula.Open]
  | hfalsum => simp [UniversalTree, Semiformula.Open]
  | hrel r v => simp [UniversalTree]
  | hnrel r v => simp [UniversalTree]
  | hand p q ihp ihq =>
    simp only [UniversalTree, Semiformula.Open, Semiformula.qr_and, max_eq_zero] at h ⊢
    exact ⟨ihp h.1, ihq h.2⟩
  | hor p q ihp ihq =>
    simp only [UniversalTree, Semiformula.Open, Semiformula.qr_or, max_eq_zero] at h ⊢
    exact ⟨ihp h.1, ihq h.2⟩
  | hall p ih => simp [Semiformula.Open, Semiformula.qr] at h
  | hexs p ih => simp [Semiformula.Open, Semiformula.qr] at h

theorem prefix_tree {ξ : Type} {n : ℕ} (φ : Semiformula language ξ n) (h : UniversalPrefix φ) : UniversalTree φ := by
  induction φ using Semiformula.rec' with
  | hall p ih => exact ih h
  | hverum => exact open_tree _ h
  | hfalsum => exact open_tree _ h
  | hrel r v => exact open_tree _ h
  | hnrel r v => exact open_tree _ h
  | hand p q ihp ihq => exact open_tree _ h
  | hor p q ihp ihq => exact open_tree _ h
  | hexs p ih => exact open_tree _ h

theorem down {M : Type} [Structure language M] (D : ClosedDomain language M)
    {ξ : Type} {n : ℕ} (φ : Semiformula language ξ n) (h : UniversalTree φ)
    (b : Fin n → D.carrier) (f : ξ → D.carrier) :
    Semiformula.Eval (fun i => (b i).val) (fun x => (f x).val) φ →
      Semiformula.Eval (s := induced D) b f φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => exact (eval_open D _ h b f).mpr
  | hnrel r v => exact (eval_open D _ h b f).mpr
  | hand p q ihp ihq =>
    rcases h with ⟨hp,hq⟩
    intro h
    exact ⟨ihp hp b h.1, ihq hq b h.2⟩
  | hor p q ihp ihq =>
    rcases h with ⟨hp,hq⟩
    intro h
    exact h.elim (fun hp' => Or.inl (ihp hp b hp')) (fun hq' => Or.inr (ihq hq b hq'))
  | hall p ih =>
    simp only [UniversalTree] at h
    simp only [Semiformula.eval_all]
    intro hall x
    have hbase := hall x.val
    apply ih h (x :> b)
    have hb : (fun i => ((x :> b) i).val) = (x.val :> fun i => (b i).val) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hb]
    exact hbase
  | hexs p ih => simp [UniversalTree, Semiformula.Open, Semiformula.qr] at h
/-- Positive Boolean combinations of existential formulas over open leaves. -/
inductive ExistentialTree {ξ : Type} : {n : ℕ} → Semiformula language ξ n → Prop
  | base {n} {φ : Semiformula language ξ n} (h : φ.Open) : ExistentialTree φ
  | and {n} {φ ψ : Semiformula language ξ n} : ExistentialTree φ → ExistentialTree ψ → ExistentialTree (φ ⋏ ψ)
  | or {n} {φ ψ : Semiformula language ξ n} : ExistentialTree φ → ExistentialTree ψ → ExistentialTree (φ ⋎ ψ)
  | ex {n} {φ : Semiformula language ξ (n+1)} : ExistentialTree φ → ExistentialTree (∃⁰ φ)

theorem neg_tree {ξ : Type} {n : ℕ} {φ : Semiformula language ξ n}
    (h : ExistentialTree φ) : UniversalTree (∼φ) := by
  induction h with
  | base h => exact open_tree _ (Semiformula.open_neg.mpr h)
  | and hp hq ihp ihq => exact ⟨ihp,ihq⟩
  | or hp hq ihp ihq => exact ⟨ihp,ihq⟩
  | ex hp ihp => exact ihp
end DiophantineConsistency.HerbrandUniversalTree
