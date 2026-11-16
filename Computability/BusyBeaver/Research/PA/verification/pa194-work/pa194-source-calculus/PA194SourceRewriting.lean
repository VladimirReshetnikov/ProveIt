import Foundation.FirstOrder.Arithmetic.Schemata
import PA194SourceSyntax
import M6.Logic.NativeRenaming

/-! Exact compatibility with Foundation's actual substitution machinery.
These are syntax equalities, not an assumed proof translation. -/
namespace M6.PA.RelationalSource
open LO LO.FirstOrder NativeCalculus

theorem termLabel_q {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m)
    (b : Fin n → Nat) (f : ξ → Nat) (b' : Fin m → Nat) (f' : ζ → Nat)
    (h : ∀ t,termLabel (ω t) b' f' = termLabel t b f) (fresh : Nat)
    (t : Semiterm language ξ (n+1)) :
    termLabel (ω.q t) (Fin.cases fresh b') f' = termLabel t (Fin.cases fresh b) f := by
  cases t with
  | bvar i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Rew.q_bvar_zero,termLabel,Fin.cases_zero]
    · rw [Rew.q_bvar_succ,termLabel_bShift]
      exact h (.bvar j)
  | fvar i =>
    rw [Rew.q_fvar,termLabel_bShift]
    exact h (.fvar i)
  | func fn _ => nomatch fn

theorem atomNamed_rew {ξ ζ : Type} {n m k : Nat} (ω : Rew language ξ n ζ m)
    (r : Relation k) (ts : Fin k → Semiterm language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (b' : Fin m → Nat) (f' : ζ → Nat)
    (h : ∀ t,termLabel (ω t) b' f' = termLabel t b f) :
    atomNamed r (ω ∘ ts) b' f' = atomNamed r ts b f := by
  cases r <;> simp only [atomNamed,Function.comp_apply,h]

theorem toNamed_rew {ξ ζ : Type} {n m : Nat} (p : Semiformula language ξ n)
    (ω : Rew language ξ n ζ m) (b : Fin n → Nat) (f : ξ → Nat)
    (b' : Fin m → Nat) (f' : ζ → Nat) (lo : Nat)
    (h : ∀ t,termLabel (ω t) b' f' = termLabel t b f) :
    toNamed (Semiformula.rewAux ω p) b' f' lo = toNamed p b f lo := by
  induction p generalizing m lo with
  | verum | falsum => rfl
  | rel r ts => exact atomNamed_rew ω r ts b f b' f' h
  | nrel r ts => exact congrArg Named.neg (atomNamed_rew ω r ts b f b' f' h)
  | and p q ihp ihq | or p q ihp ihq =>
    simp only [Semiformula.rewAux,toNamed,ihp ω b b' lo h,ihq ω b b' lo h]
  | all p ih | exs p ih =>
    simp only [Semiformula.rewAux,toNamed,
      ih ω.q (Fin.cases lo b) (Fin.cases lo b') (lo+1) (termLabel_q ω b f b' f' h lo)]

theorem termLabel_rename {ξ : Type} {n : Nat} (t : Semiterm language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (x y : Nat) :
    renameLabel x y (termLabel t b f) =
      termLabel t (renameLabel x y ∘ b) (renameLabel x y ∘ f) := by
  cases t with
  | bvar i | fvar i => rfl
  | func fn _ => nomatch fn

theorem atomNamed_replace {ξ : Type} {n k : Nat} (r : Relation k)
    (ts : Fin k → Semiterm language ξ n) (b : Fin n → Nat) (f : ξ → Nat) (x y : Nat) :
    (atomNamed r ts b f).replace x y =
      atomNamed r ts (renameLabel x y ∘ b) (renameLabel x y ∘ f) := by
  cases r <;> simp only [atomNamed,Named.replace,termLabel_rename]

theorem toNamed_replace {ξ : Type} {n : Nat} (p : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo x y : Nat) (hx : x < lo) (hx0 : x ≠ 0) :
    (toNamed p b f lo).replace x y =
      toNamed p (renameLabel x y ∘ b) (renameLabel x y ∘ f) lo := by
  induction p generalizing lo with
  | verum => rfl
  | falsum =>
    -- Bottom is the fixed relative code1, not an ordinary renamed predicate.
    simp [toNamed,Named.replace,renameLabel,Ne.symm hx0]
  | rel r ts => exact atomNamed_replace r ts b f x y
  | nrel r ts => exact congrArg Named.neg (atomNamed_replace r ts b f x y)
  | and p q ihp ihq | or p q ihp ihq =>
    simp only [toNamed,Named.replace,ihp b lo hx,ihq b lo hx]
  | all p ih | exs p ih =>
    have hlo : renameLabel x y lo = lo := by simp [renameLabel,Nat.ne_of_gt hx]
    have hpush : renameLabel x y ∘ Fin.cases lo b =
        Fin.cases lo (renameLabel x y ∘ b) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hlo
      · rfl
    simp only [toNamed,Named.replace,ih (Fin.cases lo b) (lo+1) (by omega),hpush]

#print axioms toNamed_rew
end M6.PA.RelationalSource

