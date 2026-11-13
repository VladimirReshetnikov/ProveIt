module
public import PA196.Program
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Machine.InternalCodedSourceProgram
public import PA196.Arithmetic.Machine.OriginalCoverage
@[expose] public section
set_option maxRecDepth 100000
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 PA196.Arithmetic.Machine.PA
attribute [local irreducible] PA196.Program.sites

/-- Total resolution of the literal table follows from the accepted complete
source/certificate/destination collections; no fresh unchecked table is used. -/
theorem literal_resolved (i : Nat) (hi : i<3812) :
    ∃ inst, Source.resolveAt PA196.Program.sites i=some inst := by
  have h := OriginalCoverage.checked i hi
  unfold PA196.CheckCoverage.checkAt at h
  cases hc : PA196.CheckCoverage.codeAt i with
  | none => simp [hc] at h
  | some inst => exact ⟨inst,by rw [PA196.Program.resolve_tree]; exact hc⟩

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

def DestinationBound (size : Nat) (n : Option Nat) : Prop := ∀ j, n=some j → j<size

def InstructionBound (size : Nat) : Source.Instruction → Prop
  | .inc _ n => DestinationBound size n
  | .dec _ z n => DestinationBound size z ∧ DestinationBound size n
  | .jump n => DestinationBound size n
  | .halt => True

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

/-- Every resolved literal target is either genuine cyclic exit or an actual
working ordinal; malformed sentinel is never a valid table target. -/
theorem literal_instruction_bound (i : Nat) (inst : Source.Instruction)
    (h : Source.resolveAt PA196.Program.sites i=some inst) : InstructionBound 3812 inst := by
  simp only [Source.resolveAt,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff] at h
  obtain ⟨s,hs,hr⟩ := h
  simpa only [PA196.Program.sites_count] using resolve_range PA196.Program.sites s inst hr
#print axioms literal_resolved
#print axioms literal_instruction_bound
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

