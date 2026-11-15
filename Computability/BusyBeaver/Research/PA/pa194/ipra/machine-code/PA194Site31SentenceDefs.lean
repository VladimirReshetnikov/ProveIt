import PA194Site31PhysicalClock
import PA194ActualLoopOrbit
import PA194ModelLoopFrameAt
import PA194StartupSentence
import PRAEqualityToIPRA
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
noncomputable section
namespace PA194Site31Sentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PRAModelIOpenPairing PRAExhaustion PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopFrameAt PA194ControllerLoopFrame PA194OneSpareReturn PA194StateOne PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch PA194RegisterFile PA194RegisterPermutation PA194Path27Header PA194StartupSentence
abbrev T := TermN 13
def A (a b : T) : T := app2 addCode a b
def P (a b : T) : T := app2 pairCode a b
def R (i : Fin 9) : T := .bvar ⟨i.val,by have h := i.isLt; omega⟩
def tail : T := .bvar 9
def k : T := .bvar 10
def count : T := .bvar 11
def spare : T := .bvar 12
def c (n : Nat) : T := state n
def plus1 (x : T) : T := A x one
def twice (x : T) : T := A x x
def sourceT (rs : Fin 9 → T) : T :=
 P (state 27) (P (rs 0) (P (rs 1) (P (rs 2) (P (rs 3) (P (rs 4) (P (rs 5) (P (rs 6) (P (rs 7) (P (rs 8) tail)))))))))
def packedT (gap cnt : T) (rs : Fin 9 → T) : T := P gap (P cnt (P spare (sourceT rs)))
def sourceOut : Fin 9 → T := ![plus1 (R 0),R 1,R 2,R 3,R 4,R 5,R 6,R 7,R 8]
def input : T := packedT (plus1 (plus1 k)) count R
def output : T := packedT (plus1 k) (plus1 count) sourceOut
def V : Fin 11 → T := ![R 2,R 8,R 1,R 4,R 3,R 7,R 0,R 5,R 6,spare,app2 repeatOutput count (c 0)]
def E : Fin 5 → T := ![V 6,V 7,V 8,V 9,V 10]
def marked : T := .func (PA194MarkedFile.markedFile 3) E
def EP : Fin 7 → T := ![V 0,V 1,V 2,V 3,V 4,V 5,marked]
def cc3 : T := .func (PA194CarryFile.costCode 3) ![E 1,E 2,E 3,E 4]
def cc6 : T := .func (PA194CarryFile.costCode 6) EP
def front : T := A (A (A one one) (E 0)) cc3
def H0 : T := A (A one one) one
def H1 : T := twice H0
def H2 : T := twice H1
def H3 : T := twice H2
def H4 : T := plus1 (twice H3)
def H5 : T := plus1 (twice H4)
def H6 : T := twice H5
def b : T := app2 ones (plus1 k) (twice H6)
def base : T := twice (plus1 (twice b))
def c6 : T := A (A (A (A (A (plus1 (plus1 (V 0))) (plus1 (plus1 (V 1)))) (plus1 (plus1 (V 2)))) (plus1 (plus1 (V 3)))) (plus1 (plus1 (V 4)))) (plus1 (plus1 (V 5)))
def cr : T := A (A (c 2) (plus1 (plus1 (V 5)))) (.func (PA194CarryFile.costCode 5) ![V 4,V 3,V 2,V 1,V 0,base])
def rc : T := A (c 4) (A (A (A (c 5) (c 6)) (c 2)) one)
def c15 : T := A (A (c 7) (c 3)) (c 5)
def scan : T := A (plus1 (plus1 (plus1 (plus1 k)))) (plus1 (plus1 k))
def pass : T := A (A c15 scan) (A (c 2) (A (c 3) rc))
def c71 : T := A (A pass (A (c 7) (c 1))) (plus1 (plus1 (plus1 k)))
def croot : T := A (plus1 (plus1 (A one k))) (A (c 3) (A (c 3) rc))
def clock24 : T := A (A (A c71 (A c6 cr)) croot) c15
def run (time x : T) : T := app2 PA194Stepper.stepper time x
def frame (site : Nat) (x : T) : T := .func (frameAt site readers) ![x]
def coreFor (x : T) : T := run (plus1 (plus1 k)) (run cc6 (run (plus1 (plus1 (plus1 (E 0)))) (run cc3
 (run (A (twice count) count) (run (c 2) (run (c 3) (run (A (twice count) count) (run one
 (run front (run cc6 (run (plus1 k) x)))))))))))
def afterT (x : T) : T := run (A (c 3) rc) (run one (run one (run (A (A one k) (c 3))
  (run (plus1 (A (plus1 (c 2)) k)) (run (c 2) (coreFor x))))))
def lhs : T := afterT (run clock24 (frame 31 input))
def rhs : T := frame 32 output
def sentence : Sentence language := equalClosure lhs rhs
end PA194Site31Sentence
