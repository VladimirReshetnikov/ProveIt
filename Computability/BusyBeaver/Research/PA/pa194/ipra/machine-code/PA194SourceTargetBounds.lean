import PA194SourceControllerBinding
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
/-! Resolver range lemmas adapted from the retained PA196 upstream source
`PA196/Arithmetic/Machine/InternalCodedSourceTable.lean`, specialized to the
pinned PA194 table. -/
namespace PA194SourceTargetBounds
open M6

def DestinationBound (size : Nat) (n : Option Nat) : Prop := ∀ j, n=some j → j<size

def InstructionBound (size : Nat) : Source.Instruction → Prop
  | .inc _ n => DestinationBound size n
  | .dec _ z n => DestinationBound size z ∧ DestinationBound size n
  | .jump n => DestinationBound size n
  | .halt => True

lemma findSite_range (p : Source.Path) (sites : List Source.Site) (j : Nat)
    (h : Source.findSite p sites=some j) : j<sites.length := by
  induction sites generalizing j with
  | nil => simp [Source.findSite] at h
  | cons s sites ih =>
    simp only [Source.findSite] at h
    split at h
    · cases h; simp
    · cases ht : Source.findSite p sites with
      | none => simp [ht] at h
      | some k =>
        simp only [ht,Option.map_eq_map,Option.map_some,Option.some.injEq] at h
        subst j
        simpa using Nat.succ_lt_succ (ih k ht)

lemma after_range (sites : Array Source.Site) (p : Source.Path) (n : Option Nat)
    (h : Source.after sites p=some n) : DestinationBound sites.size n := by
  cases hs : Source.successor p with
  | none => simp [Source.after,hs] at h; subst n; simp [DestinationBound]
  | some q =>
    cases hl : Source.locate sites q with
    | none => simp [Source.after,hs,hl] at h
    | some j =>
      simp only [Source.after,hs,hl,Option.map_eq_map,Option.map_some,Option.some.injEq] at h
      subst n
      intro k hk
      cases hk
      simpa only [Array.length_toList] using findSite_range q sites.toList j hl

lemma resolve_range (sites : Array Source.Site) (s : Source.Site) (i : Source.Instruction)
    (h : Source.resolve sites s=some i) : InstructionBound sites.size i := by
  cases ho : s.op with
  | inc r =>
    simp only [Source.resolve,ho,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h
    obtain ⟨n,hn,rfl⟩ := h
    exact after_range sites s.path n hn
  | dec r =>
    simp only [Source.resolve,ho,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h
    obtain ⟨p,hp,z,hz,n,hn,rfl⟩ := h
    exact ⟨after_range sites p z hz,after_range sites s.path n hn⟩
  | breakTo k =>
    simp only [Source.resolve,ho,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h
    obtain ⟨p,hp,n,hn,rfl⟩ := h
    exact after_range sites p n hn
  | continueTo k =>
    simp only [Source.resolve,ho,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h
    obtain ⟨p,hp,n,hn,rfl⟩ := h
    intro j hj
    cases hj
    simpa only [Array.length_toList] using findSite_range p sites.toList n hn
  | halt => simp [Source.resolve,ho] at h; subst i; trivial

theorem literalInstructionBound (i : Nat) (inst : Source.Instruction)
    (h : Source.resolveAt PA194SourceProgram.sites i=some inst) : InstructionBound 3673 inst := by
  simp only [Source.resolveAt,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff] at h
  obtain ⟨s,hs,hr⟩ := h
  simpa only [PA194SourceProgram.sites_count] using resolve_range PA194SourceProgram.sites s inst hr
#print axioms literalInstructionBound
end PA194SourceTargetBounds
