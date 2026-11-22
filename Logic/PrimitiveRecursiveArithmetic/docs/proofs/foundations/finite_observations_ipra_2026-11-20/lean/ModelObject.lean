import ConciseIPRA.PR
import ModelCase

/-! Fixed finite-net upper-cut formulas in the actual object calculus. An atom
interprets a signed predicate at a chosen threshold. Source and target cut
thresholds may differ: the atomic implications carry their error relaxation.
All finite sets and the formula are parameters of this proof constructor. -/
namespace ModelObject
open LeanProofs.ConciseIPRA
open scoped LeanProofs.ConciseIPRA Fm

variable {α β : Type} {k : Nat} {Γ : List (Fm PTm k)}

def someCut (L : List α) (P : α → Fm PTm k) : Fm PTm k :=
  match L with
  | [] => .bot
  | a :: rest => P a ⋎ someCut rest P

def everyCut (L : List α) (P : α → Fm PTm k) : Fm PTm k :=
  match L with
  | [] => Fm.bot ⟶ Fm.bot
  | a :: rest => P a ⋏ everyCut rest P

theorem someIntro (L : List α) (P : α → Fm PTm k) (a : α) (ha : a ∈ L)
    (h : Γ ⊢[PRAAx] P a) : Γ ⊢[PRAAx] someCut L P := by
  induction L with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with e | mem
    · subst b; exact .orI₁ h
    · exact .orI₂ (ih mem)

theorem someElim (L : List α) (P : α → Fm PTm k) (goal : Fm PTm k)
    (h : ∀ a ∈ L, Γ ⊢[PRAAx] P a ⟶ goal) :
    Γ ⊢[PRAAx] someCut L P ⟶ goal := by
  induction L with
  | nil => exact .impI (.botE _ Prf.hyp0)
  | cons a xs ih =>
    have first := h a List.mem_cons_self
    have tail := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    exact .impI (.orE Prf.hyp0 (.impE first.wk.wk Prf.hyp0) (.impE tail.wk.wk Prf.hyp0))

theorem everyIntro (L : List α) (P : α → Fm PTm k)
    (h : ∀ a ∈ L, Γ ⊢[PRAAx] P a) : Γ ⊢[PRAAx] everyCut L P := by
  induction L with
  | nil => exact .impI Prf.hyp0
  | cons a xs ih =>
    exact .andI (h _ List.mem_cons_self) (ih fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem everyProj (L : List α) (P : α → Fm PTm k) (a : α) (ha : a ∈ L)
    (h : Γ ⊢[PRAAx] everyCut L P) : Γ ⊢[PRAAx] P a := by
  induction L with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with e | mem
    · subst b; exact .andE₁ h
    · exact ih mem (.andE₂ h)

theorem infCut {s : ModelCase.Net α} {t : ModelCase.Net β} {R : α → β → Prop}
    (cover : ModelCase.Corresponds s t R) (P : α → Fm PTm k) (Q : β → Fm PTm k)
    (localPrf : ∀ a b, R a b → (Γ ⊢[PRAAx] P a ⟶ Q b)) :
    Γ ⊢[PRAAx] someCut s.elems P ⟶ someCut t.elems Q := by
  apply someElim
  intro a ha
  obtain ⟨b, hb, hab⟩ := cover.forth a ha
  exact .impI (someIntro _ Q b hb (.impE (localPrf a b hab).wk Prf.hyp0))

theorem supCut {s : ModelCase.Net α} {t : ModelCase.Net β} {R : α → β → Prop}
    (cover : ModelCase.Corresponds s t R) (P : α → Fm PTm k) (Q : β → Fm PTm k)
    (localPrf : ∀ a b, R a b → (Γ ⊢[PRAAx] P a ⟶ Q b)) :
    Γ ⊢[PRAAx] everyCut s.elems P ⟶ everyCut t.elems Q := by
  apply Prf.impI
  apply everyIntro
  intro b hb
  obtain ⟨a, ha, hab⟩ := cover.back b hb
  exact .impE (localPrf a b hab).wk (everyProj _ P a ha Prf.hyp0)

/-- Negations can be pushed to atoms for this lattice fragment. Signed atoms
also include rational constants at a threshold. -/
inductive Lattice (A : Nat → Type) : Nat → Type
  | atom {n} (symbol : A n) : Lattice A n
  | min {n} (p q : Lattice A n) : Lattice A n
  | max {n} (p q : Lattice A n) : Lattice A n
  | infQ {n} (body : Lattice A (n+1)) : Lattice A n
  | supQ {n} (body : Lattice A (n+1)) : Lattice A n

def cut {A : Nat → Type} (net : ModelCase.Net α)
    (atomCut : ∀ {n}, A n → (Fin n → α) → Fm PTm k) :
    {n : Nat} → Lattice A n → (Fin n → α) → Fm PTm k
  | _, .atom p, env => atomCut p env
  | _, .min p q, env => cut net atomCut p env ⋎ cut net atomCut q env
  | _, .max p q, env => cut net atomCut p env ⋏ cut net atomCut q env
  | _, .infQ p, env => someCut net.elems (fun a => cut net atomCut p (ModelCase.extend a env))
  | _, .supQ p, env => everyCut net.elems (fun a => cut net atomCut p (ModelCase.extend a env))

/-- An object proof at every externally fixed pair of finite nets. For the
reverse inequality instantiate this theorem with the transposed relation. -/
theorem cutTransfer {A : Nat → Type} {s : ModelCase.Net α} {t : ModelCase.Net β}
    {R : α → β → Prop} (cover : ModelCase.Corresponds s t R)
    (pA : ∀ {n}, A n → (Fin n → α) → Fm PTm k)
    (pB : ∀ {n}, A n → (Fin n → β) → Fm PTm k)
    (atoms : ∀ {n} (p : A n) env env', ModelCase.Related R env env' →
      (Γ ⊢[PRAAx] pA p env ⟶ pB p env'))
    {n} (p : Lattice A n) (env : Fin n → α) (env' : Fin n → β)
    (h : ModelCase.Related R env env') :
    Γ ⊢[PRAAx] cut s pA p env ⟶ cut t pB p env' := by
  induction p with
  | atom p => exact atoms p env env' h
  | min p q ihp ihq =>
    have hp := ihp env env' h
    have hq := ihq env env' h
    exact .impI (.orE Prf.hyp0 (.orI₁ (.impE hp.wk.wk Prf.hyp0))
      (.orI₂ (.impE hq.wk.wk Prf.hyp0)))
  | max p q ihp ihq =>
    exact .impI (.andI (.impE (ihp env env' h).wk (.andE₁ Prf.hyp0))
      (.impE (ihq env env' h).wk (.andE₂ Prf.hyp0)))
  | infQ p ih =>
    exact infCut cover _ _ (fun a b hab => ih _ _ (ModelCase.extend_related h hab))
  | supQ p ih =>
    exact supCut cover _ _ (fun a b hab => ih _ _ (ModelCase.extend_related h hab))

#print axioms cutTransfer
end ModelObject
