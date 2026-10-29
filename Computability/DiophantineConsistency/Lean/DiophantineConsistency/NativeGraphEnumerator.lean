import DiophantineConsistency.NativeFormulaGraphs
import DiophantineConsistency.DirectGraphEnumerator

/-! # The refutation checker with fixed polynomial formula and stack blocks -/

namespace DiophantineConsistency.NativeGraphEnumerator

open SetTheory SetTheory.BusyBeaver.ZFC EnumPerm Code254 KCode222
open DirectGraphEnumerator (R ofEq identity constant successor add sub
  iterate pl np tw ws depth cache)
open DirectEnumerator (encodeState decodeState encodeOption rawStep rawStep_eq
  optionStep optionStep_encode)

attribute [local irreducible] Nat.unpair

def comp {f g : ℕ → ℕ} (r : R f) (s : R g) : R (fun n => f (g n)) :=
  GraphRep.composeDirect r (fun _ => s)

def ifEq {f g h k : ℕ → ℕ} (r : R f) (s : R g) (t : R h) (u : R k) :
    R (fun n => if f n = g n then h n else k n) := GraphRep.ifEqDirect r s t u

def ifZero {f g h : ℕ → ℕ} (r : R f) (s : R g) (t : R h) :
    R (fun n => if f n = 0 then g n else h n) := ifEq r (constant 0) s t

theorem ifEq_witnessCount {f g h k : ℕ → ℕ}
    (r : R f) (s : R g) (t : R h) (u : R k) :
    (ifEq r s t u).witnessCount =
      5 + r.witnessCount + s.witnessCount + t.witnessCount + u.witnessCount := by
  change 4 + (1 + (r.witnessCount + (s.witnessCount +
    (t.witnessCount + (u.witnessCount + 0))))) = _
  omega

def unpairLeft {f : ℕ → ℕ} (r : R f) : R (fun n => (unP (f n)).1) :=
  GraphRep.composeDirect CantorRepresentation.leftCoordinate (fun _ => r)

def unpairRight {f : ℕ → ℕ} (r : R f) : R (fun n => (unP (f n)).2) :=
  GraphRep.composeDirect CantorRepresentation.rightCoordinate (fun _ => r)

def cantorPair {a b : ℕ → ℕ} (ha : R a) (hb : R b) : R (fun n => P (a n) (b n)) := by
  let args : ∀ i : Fin 2, GraphRep
      (![fun v : Fin 1 → ℕ => a (v 0), fun v => b (v 0)] i) :=
    Fin.cases ha (Fin.cases hb (fun i => Fin.elim0 i))
  exact GraphRep.composeDirect CantorRepresentation.pairCoordinates args

def naturalPair {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => Nat.pair (a n) (b n)) := by
  let args : ∀ i : Fin 2, GraphRep
      (![fun v : Fin 1 → ℕ => a (v 0), fun v => b (v 0)] i) :=
    Fin.cases ha (Fin.cases hb (fun i => Fin.elim0 i))
  exact GraphRep.composeDirect GraphRep.pairCoordinates args

def state {a b c d e f : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) (hd : R d)
    (he : R e) (hf : R f) : R (fun n => encodeState ⟨a n, b n, c n, d n, e n, f n⟩) :=
  naturalPair ha (naturalPair hb (naturalPair hc (naturalPair hd (naturalPair he hf))))

def implication {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => wim (a n) (b n)) := NativeFormulaGraphs.implication ha hb

def gated {a b c : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) :
    R (fun n => gate (a n) (b n) (c n)) := NativeFormulaGraphs.gated ha hb hc

def stack {a h b c u t w : ℕ → ℕ} (ha : R a) (hh : R h) (hb : R b) (hc : R c)
    (hu : R u) (ht : R t) (hw : R w) :
    R (fun n => axStack (a n) (h n) (b n) (c n) (u n) (t n) (w n)) :=
  NativeFormulaGraphs.stack ha hh hb hc hu ht hw

def rawStepProgram {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => encodeOption (rawStep (a n) (b n) (decodeState n))) := by
  let tag := unpairLeft ha
  let rest := unpairRight ha
  let x := unpairLeft rest
  let y := unpairRight rest
  let av := add depth (unpairLeft y)
  let bv := add cache x
  let cv := sub tag (constant 3)
  let dv := add depth x
  let p := ifEq tag (constant 0)
    (ifEq cache (constant 1) (constant 0)
      (successor (state rest hb tw (unpairRight ws) depth (unpairLeft ws))))
    (ifEq tag (constant 1)
      (successor (state rest hb cache (cantorPair tw ws) depth cache))
      (ifEq tag (constant 2)
        (ifEq (implication tw dv) cache
          (successor (state y hb dv (cantorPair (constant 0) ws) dv (constant 0)))
          (successor (state y hb (constant 0) ws dv (constant 0))))
        (successor (state (unpairRight y) hb (gated av bv cv)
          (stack av cache bv cv depth tw ws) (constant 0) (constant 0)))))
  refine ofEq p ?_
  intro n
  dsimp only [rawStep]
  split_ifs <;> rfl

def enumStepProgram : R (fun n => encodeOption (enumStep (decodeState n))) := by
  let newPl := ifEq pl (constant 0) np (sub pl (constant 1))
  let newNp := ifEq pl (constant 0) (successor np) np
  refine ofEq (rawStepProgram newPl newNp) ?_
  intro n
  simp only [enumStep, fetch]
  split <;> simp_all only [rawStep_eq]

def optionStepProgram : R optionStep :=
  ifZero identity (constant 0) (comp enumStepProgram (sub identity (constant 1)))

@[simp] theorem optionStep_encode (o : Option St) :
    optionStep (encodeOption o) = encodeOption (o.bind enumStep) := by
  cases o <;> simp [optionStep, encodeOption]

def boundedRunProgram : R (fun n => encodeOption (boundedRun n initialState)) := by
  refine ofEq (iterate optionStepProgram (encodeOption (some initialState))) ?_
  exact DirectEnumerator.boundedRun_rec

/-- Closed code data for the exact bounded halting test used by the ZFC bridge. -/
def program : R haltingTest := by
  refine ofEq (ifZero boundedRunProgram (constant 1) (constant 0)) ?_
  intro n
  cases he : boundedRun n initialState <;> simp [encodeOption, haltingTest, he]

set_option maxRecDepth 10000 in
/-- Exact source-graph count; the proof reduces only the witness-count projection. -/
theorem enumStepProgram_witnessCount : enumStepProgram.witnessCount = 1742 := rfl

set_option maxRecDepth 10000 in
theorem directGraph_enumStepProgram_witnessCount :
    DirectGraphEnumerator.enumStepProgram.witnessCount = 6924 := rfl

#print axioms program

end DiophantineConsistency.NativeGraphEnumerator
