import DiophantineConsistency.Norm38MacroCuts

/-! Candidate typed prefix-embedding and generic lookup preservation. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixEmbedding
open Norm38MacroLanguage

inductive PrefixPath : {m n : Nat} → Dag m → Dag n → (Fin m → Fin n) → Prop where
  | base {m : Nat} (d : Dag m) : PrefixPath d d (fun i => i)
  | step {m n : Nat} {d : Dag m} {e : Dag n} {f : Fin m → Fin n}
      (h : PrefixPath d e f) (t : Term n) :
      PrefixPath d (Dag.snoc e t) (fun i => (f i).castSucc)

theorem lookup {R : Type*} [CommRing R] {m n : Nat} {d : Dag m} {e : Dag n}
    {f : Fin m → Fin n} (h : PrefixPath d e f) (a : Fin 9 → R) (i : Fin m) :
    e.values a (f i) = d.values a i := by
  induction h with
  | base => rfl
  | step h t ih =>
    exact (Norm38MacroCuts.snoc_previous a _ t _).trans ih

theorem lookup_two {R : Type*} [CommRing R] {n : Nat}
    (d : Dag n) (t : Term n) (u : Term (n + 1)) (a : Fin 9 → R) (i : Fin n) :
    (Dag.snoc (Dag.snoc d t) u).values a i.castSucc.castSucc = d.values a i := by
  exact lookup (PrefixPath.step (PrefixPath.step (PrefixPath.base d) t) u) a i

#print axioms lookup
#print axioms lookup_two
end DiophantineConsistency.Norm38MacroPrefixEmbedding
