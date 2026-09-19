/-
  BRIDGE between the two first-order formalisms used in this development.

  Exacting witnesses (`RelWitness`) are elementary embeddings in the sense of Mathlib's
  model theory (language `Lex`), while the formula toolkit (`PairForm`, definability,
  the ZF axioms) uses ProveIt's de Bruijn formulas `SetTheory.Form` with `Sat`.

  `toLex` translates a `Form` into a `Lex`-formula with the same meaning
  (`realize_toLex`).  Consequently the two maps of a witness are elementary for every
  `Form` (`RelWitness.sat_j`, `RelWitness.sat_incl`), which gives

  * `RelWitness.elem`   : `V_α ⊨ φ[x⃗] ↔ V_α ⊨ φ[j x⃗]` for `x⃗ ∈ X`;
  * `RelWitness.tarski_vaught` : existential statements with parameters in `X` that hold
    in `V_α` have witnesses in `X`.

  Nothing is admitted in this file.
-/
import Cardinals.Foundations.Exacting
import Cardinals.Foundations.PairForm

universe u

namespace Cardinals

open ZFSet FirstOrder FirstOrder.Language
open SetTheory (Form Sat scons)
open SetTheory.Form

namespace Bridge

/-- The `Lex`-variable that plays the role of the de Bruijn index `k` under `n` binders:
the last bound variable is index `0`; free variables start at index `n`. -/
def var (n k : ℕ) : ℕ ⊕ Fin n :=
  if h : k < n then Sum.inr ⟨n - 1 - k, by omega⟩ else Sum.inl (k - n)

/-- The de Bruijn environment corresponding to a `Lex`-assignment. -/
def env {M : Type*} (n : ℕ) (v : ℕ → M) (xs : Fin n → M) (k : ℕ) : M :=
  Sum.elim v xs (var n k)

theorem env_zero {M : Type*} (v : ℕ → M) (xs : Fin 0 → M) : env 0 v xs = v := by
  funext k
  simp [env, var]

theorem env_snoc {M : Type*} (n : ℕ) (v : ℕ → M) (xs : Fin n → M) (a : M) :
    env (n + 1) v (Fin.snoc xs a) = scons a (env n v xs) := by
  funext k
  cases k with
  | zero =>
    have h0 : (0 : ℕ) < n + 1 := Nat.succ_pos n
    have hlast : (⟨n + 1 - 1 - 0, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
    simp only [env, var, dif_pos h0, Sum.elim_inr, hlast, Fin.snoc_last, scons]
  | succ k =>
    by_cases h : k < n
    · have h1 : k + 1 < n + 1 := by omega
      have hcast : (⟨n + 1 - 1 - (k + 1), by omega⟩ : Fin (n + 1)) =
          Fin.castSucc ⟨n - 1 - k, by omega⟩ := Fin.ext (by simp; omega)
      simp only [env, var, dif_pos h1, dif_pos h, Sum.elim_inr, hcast, Fin.snoc_castSucc, scons]
    · have h1 : ¬ k + 1 < n + 1 := by omega
      have hsub : k + 1 - (n + 1) = k - n := by omega
      simp only [env, var, dif_neg h1, dif_neg h, Sum.elim_inl, hsub, scons]

/-- Translation of ProveIt formulas into `Lex`-formulas (the unary predicate is not
used). -/
def toLex : Form → (n : ℕ) → Lex.BoundedFormula ℕ n
  | fMem i j, n => Relations.boundedFormula₂ (ExRel.mem : Lex.Relations 2)
      (Term.var (var n i)) (Term.var (var n j))
  | fEq i j, n => Term.bdEqual (Term.var (var n i)) (Term.var (var n j))
  | fBot, _ => ⊥
  | fImp a b, n => (toLex a n).imp (toLex b n)
  | fAnd a b, n => toLex a n ⊓ toLex b n
  | fOr a b, n => toLex a n ⊔ toLex b n
  | fAll a, n => ∀' toLex a (n + 1)
  | fEx a, n => ∃' toLex a (n + 1)

theorem realize_toLex (A Y : ZFSet.{u}) (φ : Form) :
    ∀ (n : ℕ) (v : ℕ → Str A Y) (xs : Fin n → Str A Y),
      (toLex φ n).Realize v xs ↔ Sat (memOn A) (env n v xs) φ := by
  induction φ with
  | fMem i j =>
    intro n v xs
    simp only [toLex, BoundedFormula.realize_rel₂, Term.realize_var]
    rfl
  | fEq i j =>
    intro n v xs
    simp only [toLex, BoundedFormula.realize_bdEqual, Term.realize_var]
    rfl
  | fBot =>
    intro n v xs
    simp only [toLex, BoundedFormula.realize_bot]
    rfl
  | fImp a b iha ihb =>
    intro n v xs
    simp only [toLex, BoundedFormula.realize_imp, iha, ihb]
    rfl
  | fAnd a b iha ihb =>
    intro n v xs
    simp only [toLex, BoundedFormula.realize_inf, iha, ihb]
    rfl
  | fOr a b iha ihb =>
    intro n v xs
    simp only [toLex, BoundedFormula.realize_sup, iha, ihb]
    rfl
  | fAll a iha =>
    intro n v xs
    simp only [toLex, BoundedFormula.realize_all, iha]
    show _ ↔ ∀ d, Sat (memOn A) (scons d (env n v xs)) a
    exact forall_congr' fun d => by rw [← env_snoc]; exact Iff.rfl
  | fEx a iha =>
    intro n v xs
    simp only [toLex, BoundedFormula.realize_ex, iha]
    show _ ↔ ∃ d, Sat (memOn A) (scons d (env n v xs)) a
    exact exists_congr fun d => by rw [← env_snoc]; exact Iff.rfl

/-- A `Lex`-elementary embedding between set structures is elementary for every
ProveIt formula. -/
theorem sat_of_elementary {A B Y Z : ZFSet.{u}} (f : Str A Y ↪ₑ[Lex] Str B Z) (φ : Form)
    (e : ℕ → Str A Y) :
    Sat (memOn B) (fun k => f (e k)) φ ↔ Sat (memOn A) e φ := by
  have h := f.map_boundedFormula (toLex φ 0) e default
  rw [realize_toLex, realize_toLex, env_zero, env_zero] at h
  exact h

end Bridge

namespace RelWitness

variable {lam α : Ordinal.{u}} {Y : ZFSet.{u}} (w : RelWitness lam α Y)

/-- The value of `j` as a set. -/
noncomputable def jv (x : Str w.X Y) : ZFSet.{u} := (w.j x).1

/-- The inclusion of `X` into `V_ α`, on carriers. -/
noncomputable def up (x : Str w.X Y) : Carrier (V_ α) := ⟨x.1, w.X_sub x.2⟩

theorem incl_eq (x : Str w.X Y) : w.incl x = w.up x := Subtype.ext (w.incl_val x)

/-- `j` is elementary for ProveIt formulas. -/
theorem sat_j (φ : Form) (e : ℕ → Str w.X Y) :
    Sat (memOn (V_ α)) (fun k => w.j (e k)) φ ↔ Sat (memOn w.X) e φ :=
  Bridge.sat_of_elementary w.j φ e

/-- The inclusion of `X` is elementary for ProveIt formulas. -/
theorem sat_incl (φ : Form) (e : ℕ → Str w.X Y) :
    Sat (memOn (V_ α)) (fun k => w.up (e k)) φ ↔ Sat (memOn w.X) e φ := by
  have h := Bridge.sat_of_elementary w.incl φ e
  simp only [incl_eq] at h
  exact h

/-- **Elementarity in the form used everywhere:** for parameters in `X`, a formula holds
in `V_ α` of the parameters iff it holds of their `j`-images. -/
theorem elem (φ : Form) (e : ℕ → Str w.X Y) :
    Sat (memOn (V_ α)) (fun k => w.up (e k)) φ ↔ Sat (memOn (V_ α)) (fun k => w.j (e k)) φ :=
  (w.sat_incl φ e).trans (w.sat_j φ e).symm

/-- **Tarski–Vaught:** an existential statement with parameters in `X` that holds in
`V_ α` has a witness in `X`. -/
theorem tarski_vaught (φ : Form) (e : ℕ → Str w.X Y)
    (h : ∃ d : Carrier (V_ α), Sat (memOn (V_ α)) (scons d (fun k => w.up (e k))) φ) :
    ∃ d : Str w.X Y, Sat (memOn (V_ α)) (scons (w.up d) (fun k => w.up (e k))) φ := by
  have h1 : Sat (memOn (V_ α)) (fun k => w.up (e k)) (fEx φ) := h
  rw [w.sat_incl] at h1
  obtain ⟨d, hd⟩ := h1
  refine ⟨d, ?_⟩
  have h2 := (w.sat_incl φ (scons d e)).mpr hd
  refine (SetTheory.Sat_ext φ _ _ (fun k => ?_)).mp h2
  cases k <;> rfl

end RelWitness

end Cardinals
