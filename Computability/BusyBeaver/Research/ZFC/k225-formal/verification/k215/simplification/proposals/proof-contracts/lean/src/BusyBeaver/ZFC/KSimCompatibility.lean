import BusyBeaver.ZFC.KSim

/-! Typed clients for the unchanged public API and the new semantic API. -/
namespace SetTheory.BusyBeaver.ZFC.KSimCompatibility
open KZip KRuntimeCore KSim RegisterPath

example {M : TMN} (B : BoxLemmas M) {br : Branch} {Q : List Bool} {e : SConf}
    (h : runTo M br Q e = true) (n : Nat) {vs : List Nat} (hv : Valid br vs) :
    Reach1 M (conc n vs (start Q)) (conc n vs e) :=
  runTo_sound B h n hv

example {M : TMN} (B : BoxLemmas M) (hNH : ∀ b, M 230 b = none)
    {Q : List Bool} (h : runHalt M Q = true) (n : Nat) {vs : List Nat}
    (hv : 10 ≤ vs.length) : KZip.Halts M (conc n vs (start Q)) :=
  runHalt_sound B hNH h n hv

example {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
    {c c' : Configuration} {T : Conf} (hc : Rel p c T) (hs : step p c = some c') :
    ∃ T', Rel p c' T' ∧ Reach1 M T T' := sim_step B hcov hc hs

example {M : TMN} {p : Program} (hcov : Covered M p)
    {c : Configuration} (hs : step p c = none) : AtHalt p c := sim_stop hcov hs

example {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
    (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf}
    (hc : Rel p c T) (hh : AtHalt p c) : KZip.Halts M T :=
  sim_halt B hcov hNH hc hh

example {M : TMN} (B : BoxLemmas M) {p : Program} (hcov : Covered M p)
    (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf} (hc : Rel p c T) :
    RegisterPath.Halts p c ↔ KZip.Halts M T := halts_iff B hcov hNH hc

example {M : TMN} {p : Program} (hcov : SemanticCovered M p)
    (hNH : ∀ b, M 230 b = none) {c : Configuration} {T : Conf} (hc : Rel p c T) :
    RegisterPath.Halts p c ↔ KZip.Halts M T := Semantic.halts_iff hcov hNH hc

end SetTheory.BusyBeaver.ZFC.KSimCompatibility
