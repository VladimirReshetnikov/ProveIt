import DiophantineConsistency.ArithmeticCommandWordPerm222

/-! The actual permuted enumerator fetch in arbitrary internal arithmetic.
An exhausted list fetches the next raw candidate; a nonempty shifted pointer
first subtracts one. The parser bound then proves strict progress within a
candidate, independently of the working registers. No scheduler is proved. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandFetchPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandWordPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- Cantor-code the actual pair (raw command, next candidate). -/
noncomputable def fetchValue (pl np : V) : V :=
  if pl=0 then cantor np (np+1) else cantor (pl-1) np

def fetchDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out pl np. (pl = 0 ∧ !ArithmeticCantor.pairDef out np (np+1)) ∨
    (pl ≠ 0 ∧ ∃ raw, !subDef raw pl 1 ∧ !ArithmeticCantor.pairDef out raw np)”

instance fetch_defined : 𝚺₁-Function₂[V] fetchValue via fetchDef := .mk fun e => by
  classical
  by_cases hp : e 1=0 <;> simp [fetchDef, fetchValue, hp]

instance fetch_definable : 𝚺₁-Function₂[V] fetchValue := fetch_defined.to_definable

theorem fetch_total (pl np : V) : ∃! out, fetchDef.val.Evalb ![out,pl,np] := by simp

@[simp] theorem fetch_new (np : V) : fetchValue 0 np=cantor np (np+1) := by
  simp [fetchValue]
@[simp] theorem fetch_continuation (raw np : V) :
    fetchValue (raw+1) np=cantor raw np := by simp [fetchValue]

@[simp] theorem raw_new (np : V) : first (fetchValue 0 np)=np := by simp
@[simp] theorem next_new (np : V) : second (fetchValue 0 np)=np+1 := by simp
@[simp] theorem raw_continuation (raw np : V) :
    first (fetchValue (raw+1) np)=raw := by simp
@[simp] theorem next_continuation (raw np : V) :
    second (fetchValue (raw+1) np)=np := by simp

lemma pred_add_one (pl : V) (hp : pl≠0) : pl-1+1=pl := by
  exact tsub_add_cancel_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hp))

/-- Reading any raw command from a nonempty shifted pointer strictly lowers
the residual pointer. Raw candidate zero is still executed when pl=1. -/
theorem continuation_progress (pl np : V) (hp : pl≠0) :
    tailValue (first (fetchValue pl np))+1 ≤ pl := by
  simp only [fetchValue, hp, if_false, first_cantor]
  have h := _root_.add_le_add (tail_le (pl-1)) (le_refl (1 : V))
  simpa only [pred_add_one pl hp] using h

theorem new_candidate_bound (np : V) : tailValue (first (fetchValue 0 np))≤np := by
  simpa using tail_le np

/-- All actual states, including arbitrary dirty list and candidate fields. -/
theorem fetch_nat (s : EnumPerm.St) :
    fetchValue s.pl s.np=Code254.P (EnumPerm.fetch s).1 (EnumPerm.fetch s).2 := by
  rcases s with ⟨pl,np,t,ws,d,h⟩
  cases pl <;> simp [fetchValue, EnumPerm.fetch, cantor_nat]

theorem raw_nat (s : EnumPerm.St) :
    first (fetchValue s.pl s.np)=(EnumPerm.fetch s).1 := by
  rw [fetch_nat, ← cantor_nat, first_cantor]

theorem next_nat (s : EnumPerm.St) :
    second (fetchValue s.pl s.np)=(EnumPerm.fetch s).2 := by
  rw [fetch_nat, ← cantor_nat, second_cantor]

end DiophantineConsistency.ArithmeticCommandFetchPerm222
