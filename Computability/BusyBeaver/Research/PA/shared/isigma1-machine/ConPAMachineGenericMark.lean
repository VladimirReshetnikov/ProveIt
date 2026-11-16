import ConPAMachineCompressedNormalization
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace ConPA.Machine.GenericMark
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine ConPA.Machine.Compressed

/-- All rows used by the mark algorithm, including its intermediate steps,
    parameterized by the candidate table and its dense control names. -/
structure Rows (T : Table) where
  control : Nat → Nat
  writeQ : Nat
  firstReturn : Nat
  backQ : Nat
  returnQ : Nat
  markEntry : findRow T (control 0) 0 = some ⟨control 0,0,0,true,writeQ⟩
  markWrite : findRow T writeQ 1 = some ⟨writeQ,1,0,false,firstReturn⟩
  markBack : findRow T firstReturn 0 = some ⟨firstReturn,0,0,false,firstReturn⟩
  skipRow : ∀ n, n < 8 → findRow T (control (n+1)) 0 = some ⟨control (n+1),0,0,true,control n⟩
  skipLoop : ∀ n, n < 8 → findRow T (control n) 1 = some ⟨control n,1,1,true,control n⟩
  backFirst : findRow T firstReturn 1 = some ⟨firstReturn,1,1,false,backQ⟩
  backLater : findRow T returnQ 1 = some ⟨returnQ,1,1,false,backQ⟩
  backLoop : findRow T backQ 1 = some ⟨backQ,1,1,false,backQ⟩
  backExit : findRow T backQ 0 = some ⟨backQ,0,0,false,returnQ⟩

def returnControl {T : Table} (S : Rows T) (n : Nat) : Nat :=
  if n = 0 then S.firstReturn else S.returnQ

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Table} (S : Rows T)
noncomputable def block (n r : V) : V := push false (bitPrefix true (n+1) r)
noncomputable def marked (n r : V) : V := push false (push false (bitPrefix true n r))
noncomputable def file (registers : List V) (tail : V) : V := registers.foldr block tail

theorem backEntry (n : Nat) :
    findRow T (returnControl S n) 1 = some ⟨returnControl S n,1,1,false,S.backQ⟩ := by
  by_cases hn : n = 0
  · simpa only [returnControl,hn,if_true] using S.backFirst
  · simpa only [returnControl,hn,if_false] using S.backLater

theorem delimiter (n l r : V) :
    Reach1 T (scanFrame true (S.control 0) l (block n r))
      (scanFrame false S.firstReturn (marked n r) l) := by
  have first := rightRow T (S.control 0) S.writeQ false false l (push true (bitPrefix true n r)) S.markEntry
  have second := leftRow T S.writeQ S.firstReturn true false (push false l) (bitPrefix true n r) S.markWrite
  have third := one (scanStep T false false false S.firstReturn S.firstReturn
      (push false (bitPrefix true n r)) l S.markBack)
  change Reach1 T (scanFrame false S.firstReturn (push false (bitPrefix true n r)) (push false l))
    (scanFrame false S.firstReturn (marked n r) l) at third
  have first' : Reach1 T (scanFrame true (S.control 0) l (block n r))
      (scanFrame true S.writeQ (push false l) (push true (bitPrefix true n r))) := by
    simpa only [block,bitPrefix_succ,push] using first
  exact positiveTrans first' (trans (reachable second) (reachable third))

theorem skipBlock (i : Nat) (hi : i < 8) (n l r : V) :
    Reach1 T (scanFrame true (S.control (i+1)) l (block n r))
      (scanFrame true (S.control i) (bitPrefix true (n+1) (push false l)) r) := by
  have first := rightRow T (S.control (i+1)) (S.control i) false false l
      (bitPrefix true (n+1) r) (S.skipRow i hi)
  exact positiveTrans first ⟨n+1, scan T true true true (S.control i) (n+1)
    (push false l) r (S.skipLoop i hi)⟩

theorem returnBlock (i : Nat) (n l r : V) :
    Reach1 T
      (scanFrame false (returnControl S i) r (bitPrefix true (n+1) (push false l)))
      (scanFrame false S.returnQ (block n r) l) := by
  have first := one (scanStep T false true true (returnControl S i) S.backQ
    r (bitPrefix true n (push false l)) (backEntry S i))
  change Reach1 T (scanFrame false (returnControl S i) r (push true
    (bitPrefix true n (push false l))))
    (scanFrame false S.backQ (push true r) (bitPrefix true n (push false l))) at first
  have middle := scan T false true true S.backQ n (push true r) (push false l) S.backLoop
  have last := one (scanStep T false false false S.backQ S.returnQ
    (bitPrefix true n (push true r)) l S.backExit)
  change Reach1 T (scanFrame false S.backQ (bitPrefix true n (push true r)) (push false l))
    (scanFrame false S.returnQ (push false (bitPrefix true n (push true r))) l) at last
  have first' : Reach1 T
      (scanFrame false (returnControl S i) r (bitPrefix true (n+1) (push false l)))
      (scanFrame false S.backQ (push true r) (bitPrefix true n (push false l))) := by
    simpa only [bitPrefix_succ,push] using first
  have onesCommute : bitPrefix true n (push true r) = bitPrefix true (n+1) r :=
    bitPrefix_push true n r
  have middleReach :
      Reach T (scanFrame false S.backQ (push true r) (bitPrefix true n (push false l)))
        (scanFrame false S.backQ (bitPrefix true n (push true r)) (push false l)) := ⟨n,middle⟩
  have last' : Reach1 T (scanFrame false S.backQ (bitPrefix true n (push true r)) (push false l))
      (scanFrame false S.returnQ (block n r) l) := by
    simpa only [block,onesCommute] using last
  exact positiveTrans first' (trans middleReach (reachable last'))

/-- A model-valued register-file mark, derived only from the supplied table rows. -/
theorem mark (previous : List V) (bound : previous.length < 9) (n l r : V) :
    Reach1 T (scanFrame true (S.control previous.length) l (file previous (block n r)))
      (scanFrame false (returnControl S previous.length) (file previous (marked n r)) l) := by
  induction previous generalizing l with
  | nil => simpa only [List.length_nil,file,List.foldr_nil,returnControl,if_true] using delimiter S n l r
  | cons a previous later =>
    have shorter : previous.length < 8 := by
      simp only [List.length_cons] at bound
      omega
    have first := skipBlock S previous.length shorter a l (file previous (block n r))
    have mid := later (by omega) (bitPrefix true (a+1) (push false l))
    have last := returnBlock S previous.length a l (file previous (marked n r))
    exact positiveTrans first (trans (reachable mid) (reachable last))

#print axioms mark
end models
end ConPA.Machine.GenericMark
