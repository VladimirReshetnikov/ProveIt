import DiophantineConsistency.HAProofs

/-! # Finite intuitionistic deduction over the existing arithmetic syntax

These constructions combine actual `HA.Derives` trees. Combining relative
proofs concatenates their finite axiom lists; it does not appeal to a model,
classical PA provability, or a completeness theorem. No quantifier rule or
arithmetic axiom is changed here.
-/

set_option Elab.async false
namespace DiophantineConsistency.HA
open SetTheory.PA

namespace Derives

theorem mp {G : List Formula} {a b : Formula}
    (hab : Derives G (.imp a b)) (ha : Derives G a) : Derives G b :=
  .impE G a b hab ha

theorem prepend {G : List Formula} {a : Formula} (h : Derives G a)
    (b : Formula) : Derives (b :: G) a :=
  h.weaken _ (fun _ hx => List.mem_cons_of_mem _ hx)

theorem imp_trans {G : List Formula} {a b c : Formula}
    (hab : Derives G (.imp a b)) (hbc : Derives G (.imp b c)) :
    Derives G (.imp a c) :=
  .impI G a c ((hbc.prepend a).mp
    ((hab.prepend a).mp (.ass _ a List.mem_cons_self)))

theorem and_left (G : List Formula) (a b : Formula) :
    Derives G (.imp (.and a b) a) :=
  .impI G _ _ (.andE1 _ a b (.ass _ _ List.mem_cons_self))

theorem and_right (G : List Formula) (a b : Formula) :
    Derives G (.imp (.and a b) b) :=
  .impI G _ _ (.andE2 _ a b (.ass _ _ List.mem_cons_self))

end Derives

namespace Relative

theorem mono_axioms {B B' : Formula → Prop} {G : List Formula} {a : Formula}
    (h : Relative B G a) (hB : ∀ x, B x → B' x) : Relative B' G a := by
  obtain ⟨L, hL, hp⟩ := h
  exact ⟨L, fun x hx => hB x (hL x hx), hp⟩

theorem weaken {B : Formula → Prop} {G G' : List Formula} {a : Formula}
    (h : Relative B G a) (hG : ∀ x ∈ G, x ∈ G') : Relative B G' a := by
  obtain ⟨L, hL, hp⟩ := h
  refine ⟨L, hL, hp.weaken _ ?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ hx
  · exact List.mem_append_right _ (hG x hx)

theorem prepend {B : Formula → Prop} {G : List Formula} {a : Formula}
    (h : Relative B G a) (b : Formula) : Relative B (b :: G) a :=
  h.weaken (fun _ hx => List.mem_cons_of_mem _ hx)

/-- Two finite axiom lists suffice for any two-premise deduction rule. -/
theorem combine {B : Formula → Prop} {G : List Formula} {a b c : Formula}
    (ha : Relative B G a) (hb : Relative B G b)
    (rule : ∀ H, Derives H a → Derives H b → Derives H c) :
    Relative B G c := by
  obtain ⟨L, hL, ha⟩ := ha
  obtain ⟨K, hK, hb⟩ := hb
  refine ⟨L ++ K, ?_, rule ((L ++ K) ++ G) (ha.weaken _ ?_) (hb.weaken _ ?_)⟩
  · intro x hx
    exact (List.mem_append.mp hx).elim (hL x) (hK x)
  · intro x hx
    simp only [List.mem_append] at hx ⊢
    exact hx.elim (fun h => Or.inl (Or.inl h)) Or.inr
  · intro x hx
    simp only [List.mem_append] at hx ⊢
    exact hx.elim (fun h => Or.inl (Or.inr h)) Or.inr

theorem mp {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (hab : Relative B G (.imp a b)) (ha : Relative B G a) : Relative B G b :=
  hab.combine ha (fun _ => Derives.mp)

theorem imp_intro {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (h : Relative B (a :: G) b) : Relative B G (.imp a b) := by
  obtain ⟨L, hL, hp⟩ := h
  refine ⟨L, hL, .impI _ a b (hp.weaken _ ?_)⟩
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  exact hx.elim (fun h => Or.inr (Or.inl h))
    (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h)))

theorem and_intro {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (ha : Relative B G a) (hb : Relative B G b) : Relative B G (.and a b) :=
  ha.combine hb (fun H => Derives.andI H a b)

theorem and_left {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (h : Relative B G (.and a b)) : Relative B G a := by
  obtain ⟨L, hL, hp⟩ := h
  exact ⟨L, hL, .andE1 _ a b hp⟩

theorem and_right {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (h : Relative B G (.and a b)) : Relative B G b := by
  obtain ⟨L, hL, hp⟩ := h
  exact ⟨L, hL, .andE2 _ a b hp⟩

theorem imp_trans {B : Formula → Prop} {G : List Formula} {a b c : Formula}
    (hab : Relative B G (.imp a b)) (hbc : Relative B G (.imp b c)) :
    Relative B G (.imp a c) :=
  hab.combine hbc (fun _ => Derives.imp_trans)

end Relative

namespace Proves

theorem of_derives {a : Formula} (h : Derives [] a) : Proves a :=
  relative_of_derives h

theorem mp {a b : Formula} (hab : Proves (.imp a b)) (ha : Proves a) :
    Proves b := Relative.mp hab ha

theorem and_intro {a b : Formula} (ha : Proves a) (hb : Proves b) :
    Proves (.and a b) := Relative.and_intro ha hb

theorem and_left {a b : Formula} (h : Proves (.and a b)) : Proves a :=
  Relative.and_left h

theorem and_right {a b : Formula} (h : Proves (.and a b)) : Proves b :=
  Relative.and_right h

theorem imp_trans {a b c : Formula} (hab : Proves (.imp a b))
    (hbc : Proves (.imp b c)) : Proves (.imp a c) :=
  Relative.imp_trans hab hbc

end Proves
end DiophantineConsistency.HA
