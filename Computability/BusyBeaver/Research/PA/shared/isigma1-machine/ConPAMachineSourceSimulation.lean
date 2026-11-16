import ConPAMachineSegments

/-! Compare an arithmetic source execution to a literal binary table using
positive model-length segments between source boundaries. -/

set_option autoImplicit false

namespace ConPA.Machine
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem synchronizeSource (T : Table) (source : V → V) (hs : 𝚺₁-Function₁ source)
    (R : V → V → Prop) (hr : 𝚺₁-Relation R) (startup : V)
    (initial : R (source 0) (run T startup))
    (advance : ∀ n t : V, R (source n) (run T t) →
      ∃ k : V, 0 < k ∧ R (source (n + 1)) (runFrom T k (run T t))) :
    ∀ n : V, ∃ t : V, n ≤ t ∧ R (source n) (run T t) := by
  letI := hs
  letI := hr
  letI := Stutter.runDefinable (V := V) T
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => exact ⟨startup, zero_le, initial⟩
  | succ n ih =>
    obtain ⟨t, hle, halign⟩ := ih
    obtain ⟨k, hk, hnext⟩ := advance n t halign
    refine ⟨t + k, add_le_add hle (pos_iff_one_le.mp hk), ?_⟩
    rw [run_add]
    exact hnext

/-- A source boundary is aligned with a working literal configuration. A
nonterminal boundary advances after a positive physical segment. A terminal
boundary supplies a segment to an absorbing literal halt. The source and
literal halt events then agree, including at nonstandard times. -/
theorem halt_iff_source (T : Table) (halt : Nat) (source : V → V) (hs : 𝚺₁-Function₁ source)
    (terminal : V → Prop) (R : V → V → Prop) (hr : 𝚺₁-Relation R) (startup : V)
    (initial : R (source 0) (run T startup))
    (live : ∀ s c, R s c → π₁ c ≠ (halt : V))
    (absorb : ∀ c : V, π₁ c = (halt : V) → step T c = c)
    (advance : ∀ n c : V, R (source n) c → ¬terminal (source n) →
      ∃ k : V, 0 < k ∧ R (source (n + 1)) (runFrom T k c))
    (finish : ∀ s c, R s c → terminal s → ∃ k : V, π₁ (runFrom T k c) = (halt : V)) :
    (∃ t : V, π₁ (run T t) = (halt : V)) ↔ ∃ n : V, terminal (source n) := by
  classical
  constructor
  · rintro ⟨t, hhalt⟩
    by_contra hsource
    have advance' (n k : V) (halign : R (source n) (run T k)) :=
      advance n _ halign (fun ht => hsource ⟨n, ht⟩)
    obtain ⟨u, htu, hrel⟩ := synchronizeSource T source hs R hr startup initial advance' t
    exact live _ _ hrel (Stutter.haltPersists T halt absorb t u htu hhalt)
  · rintro ⟨n, hterminal⟩
    by_contra hmachine
    have working (m t : V) (halign : R (source m) (run T t)) : ¬terminal (source m) := by
      intro hterm
      obtain ⟨k, hk⟩ := finish _ _ halign hterm
      exact hmachine ⟨t + k, (congrArg (fun c => π₁ c) (run_add T t k)).trans hk⟩
    have advance' (m t : V) (halign : R (source m) (run T t)) :=
      advance m _ halign (working m t halign)
    obtain ⟨t, _, hrel⟩ := synchronizeSource T source hs R hr startup initial advance' n
    exact working n t hrel hterminal

#print axioms halt_iff_source
end models
end ConPA.Machine
