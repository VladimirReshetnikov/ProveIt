import BusyBeaver.ZFC.FramedWindow

/-! Checked finite decoder products. Local blocks restore arbitrary full tapes.
Structural coverage is computed separately from primitive runtime contracts. -/
namespace SetTheory.BusyBeaver.ZFC.DecoderCertificate
open FramedWindow

structure Block where
  entry : Nat
  exit : Nat
  word : List Bool
  steps : Nat
  deriving DecidableEq, Repr, Inhabited

def cells (word : List Bool) : Cells :=
  word.zipIdx.map (fun (b,i) => ((i : Int) - (word.length - 1 : Nat), b))

def blockCheck (M : Table) (b : Block) : Bool :=
  decide (0 < b.steps ∧ 0 < b.word.length) &&
    check M b.steps b.entry 0 (cells b.word) b.exit 1

theorem block_sound (M : Table) (b : Block) (hb : blockCheck M b = true)
    (a : Int) (t : Tape)
    (hm : overlay (cells b.word) (fun i => t (i+a)) = (fun i => t (i+a))) :
    0 < b.steps ∧
    run (fullStep M) b.steps ⟨b.entry,a,t⟩ = some ⟨b.exit,a+1,t⟩ := by
  have hh : (0 < b.steps ∧ 0 < b.word.length) ∧
      check M b.steps b.entry 0 (cells b.word) b.exit 1 = true := by
    simpa [blockCheck, Bool.and_eq_true] using hb
  exact ⟨hh.1.1, arbitrary_tape_at M b.steps b.entry (cells b.word) b.exit hh.2 a t hm⟩

inductive Node where
  | leaf (op arg : Nat)
  | fork (left right : Nat)
  deriving DecidableEq, Repr
inductive Edge where
  | internal (target block : Nat)
  | primitive (node : Nat) (action : Action)
  deriving DecidableEq, Repr
structure Role where
  node : Nat
  state : Nat
  suffix : List Bool
  zero : Edge
  one : Edge
  deriving DecidableEq, Repr

def tail2 (l : List Bool) : List Bool := l.drop (l.length - 2)

def edgeCheck (M : Table) (nodes : Array Node) (roles : Array Role)
    (blocks : Array Block) (r : Role) (bit : Bool) : Bool := Id.run do
  let some (.fork l u) := nodes[r.node]? | return false
  let child := if bit then u else l
  if !(child < r.node) then return false
  let e := if bit then r.one else r.zero
  match e with
  | .primitive n a =>
    let some (.leaf _ _) := nodes[child]? | return false
    return decide (child = n ∧ M r.state bit = some a)
  | .internal k j =>
    let some (.fork _ _) := nodes[child]? | return false
    let some s := roles[k]? | return false
    let some b := blocks[j]? | return false
    let w := r.suffix ++ [bit]
    return decide (s.node = child ∧ s.suffix = tail2 w ∧ b.entry = r.state ∧
      b.exit = s.state ∧ b.word.length ≤ w.length ∧
      b.word = w.drop (w.length - b.word.length))

def roleCheck (M : Table) (nodes : Array Node) (roles : Array Role)
    (blocks : Array Block) (r : Role) : Bool :=
  decide (0 < r.suffix.length ∧ r.suffix.length ≤ 2) &&
    edgeCheck M nodes roles blocks r false && edgeCheck M nodes roles blocks r true

def structuralCheck (M : Table) (nodes : Array Node) (roles : Array Role)
    (blocks : Array Block) (root : Nat) : Bool :=
  match roles[0]? with
  | none => false
  | some r => decide (r.node = root ∧ r.state = 84 ∧ r.suffix = [true]) &&
      roles.toList.all (roleCheck M nodes roles blocks)

theorem all_blocks_sound (M : Table) (bs : List Block)
    (hc : bs.all (blockCheck M) = true) (b : Block) (hb : b ∈ bs)
    (a : Int) (t : Tape)
    (hm : overlay (cells b.word) (fun i => t (i+a)) = (fun i => t (i+a))) :
    0 < b.steps ∧
    run (fullStep M) b.steps ⟨b.entry,a,t⟩ = some ⟨b.exit,a+1,t⟩ := by
  exact block_sound M b ((List.all_eq_true.mp hc) b hb) a t hm

/-- A chain records the local word facts at each translated block boundary.
It makes no assumptions about the tape outside those finite windows. -/
inductive Chain (bs : List Block) (t : Tape) : Nat → Int → Nat → Int → Nat → Prop
  | done (q : Nat) (a : Int) : Chain bs t q a q a 0
  | more (b : Block) (a : Int) (q' : Nat) (a' : Int) (n : Nat)
      (member : b ∈ bs)
      (window : overlay (cells b.word) (fun i => t (i+a)) = (fun i => t (i+a)))
      (tail : Chain bs t b.exit (a+1) q' a' n) :
      Chain bs t b.entry a q' a' (b.steps+n)

theorem chain_sound (M : Table) (bs : List Block)
    (hc : bs.all (blockCheck M) = true) (t : Tape)
    {q q' : Nat} {a a' : Int} {n : Nat}
    (h : Chain bs t q a q' a' n) :
    run (fullStep M) n ⟨q,a,t⟩ = some ⟨q',a',t⟩ := by
  induction h with
  | done => rfl
  | more b a q' a' n hb hw _ ih =>
    rw [run_add, (all_blocks_sound M bs hc b hb a t hw).2]
    exact ih

#print axioms block_sound
#print axioms all_blocks_sound
#print axioms chain_sound
end SetTheory.BusyBeaver.ZFC.DecoderCertificate
