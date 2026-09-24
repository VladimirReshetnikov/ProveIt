import Diophantine.Paper1980.TuringSim100
import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Computability.RE
import Mathlib.Tactic.DeriveFintype

/-!
# Recursively enumerable sets are halting sets of finite machines on binary input

`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`, opening: *"For every recursively
enumerable set E of positive integers, choose a Turing machine accepting precisely the usual
finite binary expansions of the members of E."*

This is assembled from Mathlib's verified compilers, with no new axiom: a recursively
enumerable predicate has a `ToPartrec.Code` whose evaluation on `[x]` terminates exactly on its
members (`Code.exists_code`); `PartrecToTM2` runs such a code on a four-stack machine;
`TM2to1` and `TM1to0` compile it to a single-tape `TM0` machine; and the finitely many
reachable states of that machine (`tr_supports` at each stage) form a finite state type
(`finite_machine`).  The input tape is Mathlib's stack encoding of `[x]`: one marker cell
followed by the binary digits of `x`, most significant first (`trInit_trList`).
-/

namespace Jones1980

open Turing

deriving instance Fintype for Turing.PartrecToTM2.K'

namespace TMUniv

/-! ### Restricting a machine to its reachable states -/

/-- A `TM0` machine supported on a finite set of states is equivalent, for termination, to a
machine on the finite type of those states. -/
theorem finite_machine {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ)
    {F : Finset Λ} (ss : TM0.Supports M ↑F) :
    ∃ (Λs : Type) (_ : Inhabited Λs) (_ : Fintype Λs) (M' : TM0.Machine Γ Λs),
      ∀ l, (TM0.eval M' l).Dom ↔ (TM0.eval M l).Dom := by
  classical
  letI inst : Inhabited {q // q ∈ F} := ⟨⟨default, ss.1⟩⟩
  let M' : TM0.Machine Γ {q // q ∈ F} := fun q a =>
    (M q.1 a).bind fun p => if h : p.1 ∈ F then some (⟨p.1, h⟩, p.2) else none
  refine ⟨{q // q ∈ F}, inst, inferInstance, M', fun l => ?_⟩
  let tr : TM0.Cfg Γ {q // q ∈ F} → TM0.Cfg Γ Λ → Prop := fun c' c =>
    c'.q.1 = c.q ∧ c'.Tape = c.Tape
  have H : StateTransition.Respects (TM0.step M') (TM0.step M) tr := by
    rintro ⟨q', T'⟩ ⟨q, T⟩ ⟨hq, hT⟩
    simp only at hq hT
    subst hq hT
    cases hM : M q'.1 T'.head with
    | none =>
      have e1 : TM0.step M' ⟨q', T'⟩ = none := by
        simp [TM0.step, M', hM]
      have e2 : TM0.step M ⟨q'.1, T'⟩ = none := by
        simp [TM0.step, hM]
      rw [e1]
      exact e2
    | some p =>
      obtain ⟨q2, st⟩ := p
      have hF : q2 ∈ F := ss.2 (by rw [hM]; exact Option.mem_def.2 rfl) q'.2
      cases st with
      | move d =>
        have e1 : TM0.step M' ⟨q', T'⟩ = some ⟨⟨q2, hF⟩, T'.move d⟩ := by
          simp [TM0.step, M', hM, hF]
        rw [e1]
        exact ⟨⟨q2, T'.move d⟩, ⟨rfl, rfl⟩, Relation.TransGen.single (by simp [TM0.step, hM])⟩
      | write a =>
        have e1 : TM0.step M' ⟨q', T'⟩ = some ⟨⟨q2, hF⟩, T'.write a⟩ := by
          simp [TM0.step, M', hM, hF]
        rw [e1]
        exact ⟨⟨q2, T'.write a⟩, ⟨rfl, rfl⟩, Relation.TransGen.single (by simp [TM0.step, hM])⟩
  have hinit : tr (TM0.init l) (TM0.init l) := ⟨rfl, rfl⟩
  show (StateTransition.eval (TM0.step M') (TM0.init l)).Dom ↔
    (StateTransition.eval (TM0.step M) (TM0.init l)).Dom
  exact (StateTransition.tr_eval_dom H hinit).symm

/-! ### Mathlib's binary encoding of the input -/

open PartrecToTM2

theorem nat_bit_eq (x : ℕ) : x = Nat.bit (decide (x % 2 = 1)) (x / 2) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [show decide (x % 2 = 1) = false by simp [h]]; unfold Nat.bit; simp; omega
  · rw [show decide (x % 2 = 1) = true by simp [h]]; unfold Nat.bit; simp; omega

/-- `trNat` lists the binary digits, least significant first. -/
theorem trNat_eq (x : ℕ) :
    trNat x = (TMStack.lsbBits x).map (fun b => cond b Γ'.bit1 Γ'.bit0) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : x = 0
    · subst hx; rw [trNat_zero, TMStack.lsbBits, dif_pos rfl]; rfl
    · rw [TMStack.lsbBits, dif_neg hx, List.map_cons, ← ih (x / 2) (by omega)]
      unfold trNat
      rw [← Num.ofNat'_eq, ← Num.ofNat'_eq, nat_bit_eq x, Num.ofNat'_bit]
      have hdiv : (Nat.bit (decide (x % 2 = 1)) (x / 2)) / 2 = x / 2 := by
        rw [← nat_bit_eq x]
      rw [hdiv]
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · have hpos : x / 2 ≠ 0 := by omega
        have hb : decide (Nat.bit (decide (x % 2 = 1)) (x / 2) % 2 = 1) = false := by
          rw [← nat_bit_eq x]; simp [h]
        rw [hb, show decide (x % 2 = 1) = false by simp [h]]
        simp only [cond_false]
        rcases hn : Num.ofNat' (x / 2) with _ | p
        · exfalso
          have h2 := congrArg (fun m : Num => (m : ℕ))
            ((Num.ofNat'_eq (x / 2)).symm.trans hn)
          simp only [Num.to_of_nat] at h2
          exact hpos h2
        · rfl
      · have hb : decide (Nat.bit (decide (x % 2 = 1)) (x / 2) % 2 = 1) = true := by
          rw [← nat_bit_eq x]; simp [h]
        rw [hb, show decide (x % 2 = 1) = true by simp [h]]
        simp only [cond_true]
        rcases Num.ofNat' (x / 2) with _ | p <;> rfl

/-- The stack symbol of the input stack, as a cell of the `TM2to1` tape. -/
def cellOf (a : Γ') : TM2to1.Γ' K' (fun _ => Γ') :=
  (false, Function.update (fun _ => none) K'.main (some a))

/-- The bottom cell of the input stack. -/
def preCell : TM2to1.Γ' K' (fun _ => Γ') := (true, (cellOf Γ'.cons).2)

theorem trInit_trList (x : ℕ) :
    TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList [x])
      = [preCell] ++
        (TMStack.lsbBits x).reverse.map (fun b => cellOf (cond b Γ'.bit1 Γ'.bit0)) := by
  unfold TM2to1.trInit
  simp only [trList, List.append_nil, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.map_cons, List.headI_cons, List.tail_cons,
    trNat_eq, List.map_reverse, List.map_map]
  rfl

/-! ### The chain -/

/-- **Every recursively enumerable set is the halting set of a finite `TM0` machine** on a
fixed prefix followed by the binary digits of the input. -/
theorem re_tm0 {S : Set ℕ} (hS : REPred S) :
    ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Fintype Γ) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine Γ Λ) (enc : Bool → Γ) (pre : List Γ),
      ∀ x, x ∈ S ↔ (TM0.eval M (pre ++ (TMStack.lsbBits x).reverse.map enc)).Dom := by
  classical
  -- a code for the semidecision
  let f : ℕ →. ℕ := fun n => (Part.assert (n ∈ S) fun _ => Part.some ()).map fun _ => 0
  have hf : Partrec f := Partrec.map hS (Computable.const (0 : ℕ)).to₂
  have hf' : Nat.Partrec' fun v : List.Vector ℕ 1 => f v.head := Nat.Partrec'.part_iff₁.2 hf
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code hf'
  have hmem : ∀ x, x ∈ S ↔ (c.eval [x]).Dom := by
    intro x
    have := hc ⟨[x], rfl⟩
    simp only at this
    rw [this]
    show x ∈ S ↔ (Part.assert (x ∈ S) fun _ => Part.some ()).Dom
    exact ⟨fun h => ⟨h, trivial⟩, fun ⟨h, _⟩ => h⟩
  -- the four-stack machine, started at the code
  letI instΛ : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have h2 : ∀ x, (TM2.eval tr K'.main (trList [x])).Dom ↔ (c.eval [x]).Dom := by
    intro x
    have hinit : TM2.init K'.main (trList [x]) = init c [x] := by
      unfold TM2.init init
      congr 1
      funext k
      cases k <;> rfl
    unfold TM2.eval
    rw [hinit, tr_eval]
    simp
  have ss2 : TM2.Supports tr (codeSupp c Cont'.halt) := tr_supports c Cont'.halt
  -- to one tape
  have h1 : ∀ x, (TM1.eval (TM2to1.tr tr) (TM2to1.trInit K'.main (trList [x]))).Dom ↔
      (c.eval [x]).Dom := fun x => (TM2to1.tr_eval_dom tr K'.main (trList [x])).trans (h2 x)
  have ss1 := TM2to1.tr_supports tr ss2
  -- to `TM0`
  have ss0 := TM1to0.tr_supports (TM2to1.tr tr) ss1
  obtain ⟨Λs, iΛ, fΛ, M', hM'⟩ := finite_machine (TM1to0.tr (TM2to1.tr tr)) ss0
  refine ⟨TM2to1.Γ' K' (fun _ => Γ'), Λs, inferInstance, inferInstance, iΛ, fΛ, M',
    fun b => cellOf (cond b Γ'.bit1 Γ'.bit0), [preCell], fun x => ?_⟩
  rw [← trInit_trList, hM', TM1to0.tr_eval, h1, hmem]

end TMUniv

end Jones1980
