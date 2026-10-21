import DecoderContext
import K215Decoder

/-! Concrete suffix-invariant propagation for the exact incoming K215 decoder
product. This is a runtime-prefix theorem, not a replacement for KSites215. -/
namespace K215Context
open FramedWindow DecoderCertificate DecoderContext K215Decoder
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem context_checked : contextCheck roles blocks = true := by decide +kernel

def rootRole : Role := roles[0]'(by decide)

theorem root_member : rootRole ∈ roles.toList := by decide +kernel

theorem root_data : rootRole.state = 84 ∧ rootRole.suffix = [true] := by decide +kernel

theorem initial_context (a : Int) (t : Tape) (marker : t (a-1) = true) :
    MatchesAt (beforeCells rootRole.suffix) a t := by
  rw [root_data.2]
  change MatchesAt [(-1,true)] a t
  intro i b hi
  by_cases h : i = -1
  · subst i
    have hb : true = b := by simpa [lookup] using hi
    subst b
    have he : -1+a = a-1 := by omega
    simpa [he] using marker
  · simp [lookup,h] at hi

/-- Every successful internal prefix execution follows from the single start
marker and its actual pointer bits; all exterior tape cells are arbitrary. -/
theorem prefix_sound {bits : List Bool} {f : Role} {n : Nat}
    (hf : follow roles blocks rootRole bits = some (f,n))
    (a : Int) (t : Tape) (marker : t (a-1) = true) (ht : Reads t a bits) :
    run (fullStep native) n ⟨84,a,t⟩ =
      some ⟨f.state,a+(bits.length : Int),t⟩ ∧
    MatchesAt (beforeCells f.suffix) (a+(bits.length : Int)) t := by
  have h := follow_sound native all_blocks_checked context_checked root_member hf
    a t (initial_context a t marker) ht
  simpa only [root_data.1] using h

theorem prefix_positive {bits : List Bool} {f : Role} {n : Nat}
    (hf : follow roles blocks rootRole bits = some (f,n)) (hne : bits ≠ []) : 0 < n :=
  route_positive native all_blocks_checked (follow_route root_member hf) hne

theorem source_checked : sourceCheck sourceNodes roles blocks = true := by decide +kernel

theorem root_source : rootRole.node = sourceRoot := by decide +kernel

/-- Universal coverage of all INTERNAL paths of the supplied 202-node source
DAG, with no separate route or intermediate-window hypotheses. -/
theorem every_internal_source_path {bits : List Bool} {m : Nat}
    (hn : nodeFollow sourceNodes sourceRoot bits = some m)
    (a : Int) (t : Tape) (marker : t (a-1) = true) (ht : Reads t a bits) :
    ∃ (f : Role) (n : Nat), f.node = m ∧
      run (fullStep native) n ⟨84,a,t⟩ =
        some ⟨f.state,a+(bits.length : Int),t⟩ ∧
      MatchesAt (beforeCells f.suffix) (a+(bits.length : Int)) t ∧
      (bits ≠ [] → 0 < n) := by
  obtain ⟨f,n,hf,hm⟩ := source_path_follow source_checked root_member
    (by simpa only [root_source] using hn)
  have h := prefix_sound hf a t marker ht
  exact ⟨f,n,hm,h.1,h.2,fun hne => prefix_positive hf hne⟩

/-- Concrete negative controls distinguish false/missing predecessor facts
and inconsistent next-role metadata from valid contexts. -/
theorem rejects_missing_predecessor :
    edgeContextCheck roles blocks {rootRole with suffix := []} false = false := by decide +kernel

theorem rejects_wrong_predecessor :
    edgeContextCheck roles blocks {rootRole with suffix := [false]} false = false := by decide +kernel

theorem rejects_wrong_next_suffix :
    edgeContextCheck
      (roles.set 1 {(roles[1]'(by decide)) with suffix := [false,false]} (by decide))
      blocks rootRole false = false := by decide +kernel

theorem rejects_missing_target_role :
    edgeContextCheck #[] blocks rootRole false = false := by decide +kernel

theorem rejects_primitive_as_source_parent :
    sourceEdgeCheck sourceNodes roles blocks {rootRole with node := 0} false = false := by decide +kernel

#print axioms context_checked
#print axioms prefix_sound
#print axioms prefix_positive
#print axioms source_checked
#print axioms every_internal_source_path
#print axioms rejects_missing_predecessor
#print axioms rejects_wrong_predecessor
#print axioms rejects_wrong_next_suffix
end K215Context
