module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceUnpairRound
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def unpairDecodedStore (r x y : Fin 9) (xs w k : V) : V :=
  unpairStore r x y xs w (decodeLeft k) (decodeRight k)
noncomputable def unpairDecodedStoreGraph (r x y : Fin 9) : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “z xs w k. ∃ a b rs ts, !decodeGraph a b k ∧ !(replaceGraph r.val) rs xs w ∧
    !(replaceGraph x.val) ts rs a ∧ !(replaceGraph y.val) z ts b”
lemma unpairDecodedStore_graph (r x y : Fin 9) (z xs w k : V) :
    (unpairDecodedStoreGraph r x y).val.Evalb ![z,xs,w,k] ↔ z=unpairDecodedStore r x y xs w k := by
  simp [unpairDecodedStoreGraph,decode_graph,(replace_defined r.val).df,(replace_defined x.val).df,
    (replace_defined y.val).df,unpairDecodedStore,unpairStore]

lemma decodeLeft_step_zero (k : V) (hk : decodeLeft k=0) : decodeLeft (k+1)=decodeRight k+1 := by
  simp only [decodeLeft,decodeRight,decodeState_succ,advanceState]
  dsimp only [decodeLeft] at hk
  simp [hk]
lemma decodeRight_step_zero (k : V) (hk : decodeLeft k=0) : decodeRight (k+1)=0 := by
  simp only [decodeRight,decodeState_succ,advanceState]
  dsimp only [decodeLeft] at hk
  simp [hk]
lemma decodeLeft_step_nonzero (k : V) (hk : decodeLeft k≠0) : decodeLeft (k+1)=decodeLeft k-1 := by
  simp only [decodeLeft,decodeState_succ,advanceState]
  dsimp only [decodeLeft] at hk
  simp [hk]
lemma decodeRight_step_nonzero (k : V) (hk : decodeLeft k≠0) : decodeRight (k+1)=decodeRight k+1 := by
  simp only [decodeRight,decodeState_succ,advanceState]
  dsimp only [decodeLeft] at hk
  simp [hk]

theorem unpair_round_decode (r x y : Fin 9) (base : Nat) (hrx : r≠x) (hry : r≠y) (hxy : x≠y)
    (hbound : base+7<3812) (hb : UnpairLoopBound r x y base)
    (xs w k : V) (hv : ValidStore xs) :
    ∃ n cs,Trace n cs (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs (w+1) k))
      (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs w (k+1))) := by
  rcases zero_or_succ (decodeLeft k) with hk | ⟨a,ha⟩
  · have h := unpair_round_zero r x y base hrx hry hxy hbound hb xs w (decodeRight k) hv
    simpa only [unpairDecodedStore,decodeLeft_step_zero k hk,decodeRight_step_zero k hk,hk] using h
  · have hk : decodeLeft k≠0 := by rw [ha]; simp
    obtain ⟨cs,hc⟩ := unpair_round_succ r x y base hrx hry hxy hbound hb xs w a (decodeRight k) hv
    refine ⟨5,cs,?_⟩
    simpa only [unpairDecodedStore,decodeLeft_step_nonzero k hk,decodeRight_step_nonzero k hk,ha,add_sub_self] using hc
#print axioms unpairDecodedStore_graph
#print axioms unpair_round_decode
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

