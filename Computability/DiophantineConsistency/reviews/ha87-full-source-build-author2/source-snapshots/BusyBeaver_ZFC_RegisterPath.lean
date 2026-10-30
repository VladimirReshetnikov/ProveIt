import Init

/-!
The public Wade register machine's path semantics.

This is an attributed Lean port of `ZF/m254/coq/tm/RM.v`, lines 16–110,
in Jeff's busy-beaver verification, commit
297ab8df7e5de329605c3875b4934643b371a5e3 (also unchanged in mira-emmy's
PR20 head 0d544f2a2e3c18f12278441a74b7879f31cbe856). Wade supplied the
TMBuilder framework; Mira-Cult designed the benchmark and Jeff supplied
the verification. This port does not relicense the upstream snapshot.

Paths are MSB first, with implicit trailing zero bits. Crucially, after a
leaf at depth d is found, the old path is both zero extended and truncated
to exactly d bits before path arithmetic. Break and continue are actual
small steps. `none` can mean a halt leaf or exhausted decoder fuel; `Halts`
therefore requires reaching a literal halt leaf, as in the source.

The finite-list register executor below has proved agreement with the
unbounded `Nat → Nat` register semantics. Its writes zero extend the
list when necessary. This is a computational certificate interface, not
a binary Turing machine simulation or a structured-program semantics.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterPath

inductive Edge where
  | node (n : Nat)
  | inc (r : Nat)
  | decnz (r : Nat)
  | brk (k : Nat)
  | cont (k : Nat)
  | halt
  deriving DecidableEq, Repr

structure Program where
  nodes : Nat → Edge × Edge
  root : Nat
  nnodes : Nat

abbrev Registers := Nat → Nat

def update (R : Registers) (r v : Nat) : Registers :=
  fun i => if i = r then v else R i

def bit (P : List Bool) (i : Nat) : Bool := P[i]?.getD false

/-- The fuel and consumed-depth conventions are exactly those of `RM.walk`. -/
def walk (p : Program) : Nat → Nat → List Bool → Nat → Option (Edge × Nat)
  | 0, _, _, _ => none
  | fuel + 1, n, P, i =>
      let cell := p.nodes n
      let e := if bit P i then cell.2 else cell.1
      match e with
      | .node n' => walk p fuel n' P (i + 1)
      | _ => some (e, i + 1)

def incRev : List Bool → List Bool
  | [] => []
  | false :: P => true :: P
  | true :: P => false :: incRev P

def incPath (P : List Bool) : List Bool := (incRev P.reverse).reverse

def stripRev (b : Bool) : Nat → List Bool → List Bool
  | 0, P => P
  | _ + 1, [] => []
  | k + 1, x :: P => if x = b then stripRev b k P else stripRev b (k + 1) P
termination_by structural _ P => P

def stripPath (b : Bool) (k : Nat) (P : List Bool) : List Bool :=
  (stripRev b k P.reverse).reverse

def breakPath (k : Nat) (P : List Bool) : List Bool := incPath (stripPath false k P)

def continuePath (k : Nat) (P : List Bool) : List Bool := stripPath true k P

structure Configuration where
  path : List Bool
  registers : Registers

def consume (P : List Bool) (d : Nat) : List Bool :=
  (P ++ List.replicate d false).take d

def execute (e : Edge) (P : List Bool) (R : Registers) : Option Configuration :=
  match e with
  | .node _ | .halt => none
  | .inc r => some ⟨incPath P, update R r (R r + 1)⟩
  | .decnz r =>
      match R r with
      | 0 => some ⟨breakPath 1 P, R⟩
      | v + 1 => some ⟨incPath P, update R r v⟩
  | .brk k => some ⟨breakPath k P, R⟩
  | .cont k => some ⟨continuePath k P, R⟩

def step (p : Program) (c : Configuration) : Option Configuration :=
  match walk p (p.nnodes + 1) p.root c.path 0 with
  | none => none
  | some (e, d) => execute e (consume c.path d) c.registers

def run (p : Program) : Nat → Configuration → Option Configuration
  | 0, c => some c
  | n + 1, c =>
      match step p c with
      | none => none
      | some c' => run p n c'

def AtHalt (p : Program) (c : Configuration) : Prop :=
  ∃ d, walk p (p.nnodes + 1) p.root c.path 0 = some (.halt, d)

def Halts (p : Program) (c : Configuration) : Prop :=
  ∃ n c', run p n c = some c' ∧ AtHalt p c'

/-! ## Finite register certificates -/

def readRegisters : List Nat → Nat → Nat
  | [], _ => 0
  | v :: _, 0 => v
  | _ :: R, i + 1 => readRegisters R i

def writeRegisters (R : List Nat) : Nat → Nat → List Nat
  | 0, v => v :: R.tail
  | i + 1, v => R.headD 0 :: writeRegisters R.tail i v

theorem read_writeRegisters (R : List Nat) (i v j : Nat) :
    readRegisters (writeRegisters R i v) j =
      if j = i then v else readRegisters R j := by
  induction i generalizing R j <;> cases R <;> cases j <;> simp [writeRegisters, readRegisters, *]

theorem read_writeRegisters_eq (R : List Nat) (i v : Nat) :
    readRegisters (writeRegisters R i v) = update (readRegisters R) i v :=
  funext (read_writeRegisters R i v)

structure FiniteConfiguration where
  path : List Bool
  registers : List Nat
  deriving DecidableEq, Repr

def decode (c : FiniteConfiguration) : Configuration :=
  ⟨c.path, readRegisters c.registers⟩

def finiteExecute (e : Edge) (P : List Bool) (R : List Nat) : Option FiniteConfiguration :=
  match e with
  | .node _ | .halt => none
  | .inc r => some ⟨incPath P, writeRegisters R r (readRegisters R r + 1)⟩
  | .decnz r =>
      match readRegisters R r with
      | 0 => some ⟨breakPath 1 P, R⟩
      | v + 1 => some ⟨incPath P, writeRegisters R r v⟩
  | .brk k => some ⟨breakPath k P, R⟩
  | .cont k => some ⟨continuePath k P, R⟩

def finiteStep (p : Program) (c : FiniteConfiguration) : Option FiniteConfiguration :=
  match walk p (p.nnodes + 1) p.root c.path 0 with
  | none => none
  | some (e, d) => finiteExecute e (consume c.path d) c.registers

def finiteRun (p : Program) : Nat → FiniteConfiguration → Option FiniteConfiguration
  | 0, c => some c
  | n + 1, c =>
      match finiteStep p c with
      | none => none
      | some c' => finiteRun p n c'

theorem finiteExecute_sound (e : Edge) (P : List Bool) (R : List Nat) :
    execute e P (readRegisters R) = (finiteExecute e P R).map decode := by
  cases e with
  | node _ | brk _ | cont _ | halt => rfl
  | inc r => simp only [execute, finiteExecute, Option.map, decode, read_writeRegisters_eq]
  | decnz r =>
      cases h : readRegisters R r with
      | zero => simp only [execute, finiteExecute, h, Option.map, decode]
      | succ v => simp only [execute, finiteExecute, h, Option.map, decode, read_writeRegisters_eq]

theorem finiteStep_sound (p : Program) (c : FiniteConfiguration) :
    step p (decode c) = (finiteStep p c).map decode := by
  unfold step finiteStep decode
  cases h : walk p (p.nnodes + 1) p.root c.path 0 with
  | none => rfl
  | some ed => exact finiteExecute_sound ed.1 (consume c.path ed.2) c.registers

/-- Finite-list execution certifies the actual infinite-register path semantics. -/
theorem finiteRun_sound (p : Program) (n : Nat) (c : FiniteConfiguration) :
    run p n (decode c) = (finiteRun p n c).map decode := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [run, finiteRun, finiteStep_sound]
      cases h : finiteStep p c with
      | none => rfl
      | some c' => exact ih c'

end SetTheory.BusyBeaver.ZFC.RegisterPath
