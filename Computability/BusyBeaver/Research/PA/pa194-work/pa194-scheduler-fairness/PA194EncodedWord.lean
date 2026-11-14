import PA194CommandEquiv
import PA194DerivationCompiler
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace PA194EncodedWord
open M6.Source.Cantor PA196.Commands PA194CommandRun PA194FetchCommand PA194FetchSource

def encodeCommand : Command → Nat → Nat
  | .shift,t => pair 0 t
  | .mp x,t => pair 1 (pair x t)
  | .ax c x y,t => pair (c+2) (pair y (pair x t))

theorem parse_encode (c : Command) (tail : Nat) : parse (encodeCommand c tail) = ⟨c,tail⟩ := by
  cases c <;> simp [encodeCommand,parse,decode_pair]

def encodeWord : List Command → Nat → Nat
  | [],tail => tail
  | c::cs,tail => encodeCommand c (encodeWord cs tail)+1

theorem advance_encoded (n tail : Nat) (c : Command) (cs : List Command) (s : Store) :
    PA194CommandRun.advance ⟨n,encodeWord (c::cs) tail,s⟩ =
      (PA194CommandTransfer.step c s).map (fun out => ⟨n,encodeWord cs tail,out⟩) := by
  simp only [PA194CommandRun.advance,encodeWord,FetchDispatch.seed,FetchDispatch.nextN,Nat.add_eq_zero_iff,
    Nat.reduceEqDiff,and_false,ite_false,Nat.add_sub_cancel,parse_encode]
  cases PA194CommandTransfer.step c s <;> rfl

theorem word_halts_scheduler (cs : List Command) (tail n : Nat) (s : Store)
    (h : PA194Words.run cs s = none) :
    PA194CommandEquiv.Halts ⟨n,encodeWord cs tail,s⟩ := by
  induction cs generalizing s with
  | nil => simp [PA194Words.run] at h
  | cons c cs ih =>
    cases hs : PA194CommandTransfer.step c s with
    | none =>
      exact ⟨0,⟨n,encodeWord (c::cs) tail,s⟩,rfl,by simpa [advance_encoded,hs]⟩
    | some out =>
      simp only [PA194Words.run,PA194Words.step,hs,Option.bind_some] at h
      obtain ⟨k,final,hk,hfinal⟩ := ih out h
      refine ⟨k+1,final,?_,hfinal⟩
      simp only [PA194CommandRun.run,advance_encoded,hs,Option.map_some,Option.bind_some]
      exact hk

theorem derivation_halts_scheduler (p : PA194DerivationCompiler.Derivation 1)
    (tail n : Nat) (s : Store) :
    PA194CommandEquiv.Halts ⟨n,encodeWord (PA194DerivationCompiler.haltWord p) tail,s⟩ :=
  word_halts_scheduler _ tail n s (PA194DerivationCompiler.haltWord_universal p s)

#print axioms parse_encode
#print axioms word_halts_scheduler
#print axioms derivation_halts_scheduler
end PA194EncodedWord
