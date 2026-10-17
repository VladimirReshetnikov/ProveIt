import BusyBeaver.ZFC.ArithmeticCommandAppend254

/-!
Finite numeric circuits for the actual Enum254 compiler's command blocks.
All graph formulae have order(out,a,b,c,u). Circuit syntax and each nips count
are external finite data; represented append handles the model-valued word
operands. No nonstandard recursion on circuit syntax is claimed here.

These are finite numeric word constructors. Internal command execution and
compiler-history validity transport remain separate obligations.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandAppend254
attribute [local irreducible] Code254.P CommandWord254.encode Enum254.pack Enum254.nips Enum254.discard
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

inductive Circuit where
  | input0 | input1 | input2 | input3 | zero | one
  | plus (left right : Circuit)
  | pair (left right : Circuit)
  | append (left right : Circuit)

noncomputable def Circuit.eval : Circuit → V → V → V → V → V
  | .input0, a, _, _, _ => a
  | .input1, _, b, _, _ => b
  | .input2, _, _, c, _ => c
  | .input3, _, _, _, u => u
  | .zero, _, _, _, _ => 0
  | .one, _, _, _, _ => 1
  | .plus x y, a, b, c, u => x.eval a b c u + y.eval a b c u
  | .pair x y, a, b, c, u => cantor (x.eval a b c u) (y.eval a b c u)
  | .append x y, a, b, c, u => appendValue (x.eval a b c u) (y.eval a b c u)

/-- Fixed parameter-free Sigma1 compilation. No output bound is used for
append's intermediate history, so rejected/shrinking output0 causes no bound
assumption. The only free formula variables are the output and four inputs. -/
def Circuit.graph : Circuit → 𝚺₁.Semisentence 5
  | .input0 => .mkSigma “out a b c u. out = a”
  | .input1 => .mkSigma “out a b c u. out = b”
  | .input2 => .mkSigma “out a b c u. out = c”
  | .input3 => .mkSigma “out a b c u. out = u”
  | .zero => .mkSigma “out a b c u. out = 0”
  | .one => .mkSigma “out a b c u. out = 1”
  | .plus x y => .mkSigma
      “out a b c u. ∃ l, ∃ r, !(graph x) l a b c u ∧
        !(graph y) r a b c u ∧ out = l + r”
  | .pair x y => .mkSigma
      “out a b c u. ∃ l, ∃ r, !(graph x) l a b c u ∧
        !(graph y) r a b c u ∧ !ArithmeticCantor.pairDef out l r”
  | .append x y => .mkSigma
      “out a b c u. ∃ l, ∃ r, !(graph x) l a b c u ∧
        !(graph y) r a b c u ∧ !ArithmeticCommandAppend254.appendDef out l r”

instance Circuit.defined (e : Circuit) : 𝚺₁-Function₄[V] e.eval via e.graph := by
  induction e with
  | input0 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | input1 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | input2 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | input3 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | zero => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | one => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | plus x y ihx ihy =>
    exact .mk fun v => by
      simp [Circuit.graph, Circuit.eval, ihx.iff, ihy.iff]
  | pair x y ihx ihy =>
    exact .mk fun v => by
      simp [Circuit.graph, Circuit.eval, ihx.iff, ihy.iff]
  | append x y ihx ihy =>
    exact .mk fun v => by
      simp [Circuit.graph, Circuit.eval, ihx.iff, ihy.iff]

namespace Circuit

def two : Circuit := .plus .one .one
def three : Circuit := .plus .one two

/-- Every cons includes the +1 shifted-word marker. Rest is already a shifted
word and may be empty0; no raw candidate is silently executed. -/
def consMp (x rest : Circuit) : Circuit := .plus (.pair .zero (.pair x rest)) .one
def consDrop (x rest : Circuit) : Circuit := .plus (.pair .one (.pair x rest)) .one
def consNip (x rest : Circuit) : Circuit := .plus (.pair two (.pair x rest)) .one
/-- Cmd.ax order is(c,x,y,u), with outer tag c+3. -/
def consAx (c x y u rest : Circuit) : Circuit :=
  .plus (.pair (.plus c three) (.pair x (.pair y (.pair u rest)))) .one

def mp (x : Circuit) := consMp x .zero
def drop (x : Circuit) := consDrop x .zero
def nip (x : Circuit) := consNip x .zero
def ax (c x y u : Circuit) := consAx c x y u .zero

/-- External finite repetition, never an unrepresented internal counter. -/
def nips : Nat → Circuit
  | 0 => .zero
  | k + 1 => consNip .zero (nips k)

def discard : Circuit := consMp .one (consAx .one .zero .zero .zero (nips 10))

def leaf (j : Nat) (a b c u : Circuit) : Circuit :=
  .append discard (consAx c a b u (.append (nips j) (consDrop .zero (nips (11-j)))))

def leaf1 := leaf 1 .input0 .input1 .zero .zero
def leaf2 := leaf 2 .input0 .input1 .input2 .zero
def leaf3 := leaf 3 .input0 .input1 .input2 .zero
def leaf4 := leaf 4 .input0 .input1 .input2 .zero
def leaf5 := leaf 5 .input0 .input1 .input2 .zero
def leaf6 := leaf 6 .input0 .input1 .zero .zero
def leaf7 := leaf 7 .input0 .input1 .input2 .zero
def leaf8 := leaf 8 .input0 .input1 .input2 .input3

def bundleLeaf (a b c : Circuit) : Circuit :=
  .append discard (consAx c a b .zero (nips 10))

def terminator : Circuit := consDrop .zero (consNip .zero (consNip .zero .zero))

def genBlock (i p : Circuit) : Circuit :=
  .append p (consDrop .zero (consNip .zero (consAx i i .zero .zero
    (.append (nips 9) terminator))))

def mpBlock (b pa pab : Circuit) : Circuit :=
  .append pa (consDrop .zero (.append pab
    (consNip .zero (consDrop .zero (consNip .zero (consMp b (consAx b .zero .zero .zero
      (.append (nips 10) terminator))))))))

@[simp] theorem eval_zero (a b c u : V) : zero.eval a b c u = 0 := rfl
@[simp] theorem eval_one (a b c u : V) : one.eval a b c u = 1 := rfl
@[simp] theorem eval_input0 (a b c u : V) : input0.eval a b c u = a := rfl
@[simp] theorem eval_input1 (a b c u : V) : input1.eval a b c u = b := rfl
@[simp] theorem eval_input2 (a b c u : V) : input2.eval a b c u = c := rfl
@[simp] theorem eval_input3 (a b c u : V) : input3.eval a b c u = u := rfl
@[simp] theorem eval_plus (x y : Circuit) (a b c u : V) :
    (plus x y).eval a b c u = x.eval a b c u + y.eval a b c u := rfl
@[simp] theorem eval_pair_nat (x y : Circuit) (a b c u : Nat) :
    (pair x y).eval a b c u = Code254.P (x.eval a b c u) (y.eval a b c u) :=
  cantor_nat _ _
@[simp] theorem eval_append_nat (x y : Circuit) (a b c u : Nat) :
    (append x y).eval a b c u = CommandWord254.append (x.eval a b c u) (y.eval a b c u) :=
  appendValue_nat _ _

@[simp] theorem eval_consMp (x rest : Circuit) (a b c u : Nat) :
    (consMp x rest).eval a b c u =
      Enum254.pack (.mp (x.eval a b c u)) (rest.eval a b c u) + 1 := by
  simp [consMp, Enum254.pack]
@[simp] theorem eval_consDrop (x rest : Circuit) (a b c u : Nat) :
    (consDrop x rest).eval a b c u =
      Enum254.pack (.drop (x.eval a b c u)) (rest.eval a b c u) + 1 := by
  simp [consDrop, Enum254.pack]
@[simp] theorem eval_consNip (x rest : Circuit) (a b c u : Nat) :
    (consNip x rest).eval a b c u =
      Enum254.pack (.nip (x.eval a b c u)) (rest.eval a b c u) + 1 := by
  simp [consNip, two, Enum254.pack]
@[simp] theorem eval_consAx (k x y z rest : Circuit) (a b c u : Nat) :
    (consAx k x y z rest).eval a b c u =
      Enum254.pack (.ax (k.eval a b c u) (x.eval a b c u) (y.eval a b c u) (z.eval a b c u))
        (rest.eval a b c u) + 1 := by
  simp [consAx, three, two, Enum254.pack]

/-- Orient only this cons equation toward the symbolic list, without unfolding
any enormous closed axiom code. -/
theorem packed_nil (cmd : Enum254.Cmd) :
    Enum254.pack cmd 0 + 1 = CommandWord254.encode [cmd] := by
  simp only [CommandWord254.encode]

theorem packed_encode (cmd : Enum254.Cmd) (rest : List Enum254.Cmd) :
    Enum254.pack cmd (CommandWord254.encode rest) + 1 =
      CommandWord254.encode (cmd :: rest) := by
  simp only [CommandWord254.encode]

@[simp] theorem eval_nips (k : Nat) (a b c u : Nat) :
    (nips k).eval a b c u = CommandWord254.encode (Enum254.nips k) := by
  induction k with
  | zero => simp only [nips, eval_zero, Enum254.nips, CommandWord254.encode]
  | succ k ih =>
      rw [nips, eval_consNip, ih, packed_encode]
      simp only [Enum254.nips, eval_zero]

@[simp] theorem eval_discard (a b c u : Nat) :
    discard.eval a b c u = CommandWord254.encode Enum254.discard := by
  simp only [discard, eval_consMp, eval_consAx, eval_nips, eval_zero, eval_one]
  rw [packed_encode, packed_encode]
  simp only [Enum254.discard, List.cons_append, List.nil_append]

@[simp] theorem eval_leaf (j : Nat) (x y z w : Circuit) (a b c u : Nat) :
    (leaf j x y z w).eval a b c u = CommandWord254.encode
      (Enum254.leaf j (x.eval a b c u) (y.eval a b c u) (z.eval a b c u) (w.eval a b c u)) := by
  simp only [leaf, eval_append_nat, eval_discard, eval_consAx, eval_consDrop, eval_nips, eval_zero]
  rw [packed_encode, CommandWord254.append_encode, packed_encode, CommandWord254.append_encode]
  rfl

@[simp] theorem eval_bundleLeaf (x y z : Circuit) (a b c u : Nat) :
    (bundleLeaf x y z).eval a b c u = CommandWord254.encode
      (Enum254.bundleLeaf (x.eval a b c u) (y.eval a b c u) (z.eval a b c u)) := by
  simp only [bundleLeaf, eval_append_nat, eval_discard, eval_consAx, eval_nips, eval_zero]
  rw [packed_encode, CommandWord254.append_encode]
  rfl

@[simp] theorem eval_terminator (a b c u : Nat) :
    terminator.eval a b c u = CommandWord254.encode [.drop 0, .nip 0, .nip 0] := by
  simp only [terminator, eval_consDrop, eval_consNip, eval_zero]
  rw [packed_nil, packed_encode, packed_encode]

/-- Block adapters accept symbolic encoded child words, not evaluated codes
for closed huge examples. Their execution contracts remain separate. -/
theorem eval_genBlock (i p : Circuit) (a b c u : Nat) (word : List Enum254.Cmd)
    (hp : p.eval a b c u = CommandWord254.encode word) :
    (genBlock i p).eval a b c u =
      CommandWord254.encode (Enum254.genBlock (i.eval a b c u) word) := by
  simp only [genBlock, eval_append_nat, eval_consDrop, eval_consNip, eval_consAx,
    eval_nips, eval_terminator, eval_zero, hp]
  rw [CommandWord254.append_encode, packed_encode, packed_encode, packed_encode,
    CommandWord254.append_encode]
  rfl

theorem eval_mpBlock (b pa pab : Circuit) (a d c u : Nat)
    (minor major : List Enum254.Cmd)
    (hp : pa.eval a d c u = CommandWord254.encode minor)
    (hq : pab.eval a d c u = CommandWord254.encode major) :
    (mpBlock b pa pab).eval a d c u =
      CommandWord254.encode (Enum254.mpBlock (b.eval a d c u) minor major) := by
  simp only [mpBlock, eval_append_nat, eval_consDrop, eval_consNip, eval_consMp,
    eval_consAx, eval_nips, eval_terminator, eval_zero, hp, hq]
  rw [CommandWord254.append_encode, packed_encode, packed_encode, packed_encode,
    packed_encode, packed_encode, CommandWord254.append_encode, packed_encode,
    CommandWord254.append_encode]
  rfl

end Circuit
end SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254
