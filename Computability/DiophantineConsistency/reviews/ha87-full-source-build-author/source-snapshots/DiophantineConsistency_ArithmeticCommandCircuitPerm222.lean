import DiophantineConsistency.ArithmeticCommandLeafPerm222

/-! Fixed finite numeric circuits for the actual C222 word encoding.
A circuit is external finite syntax; its four inputs and intermediates
range over an arbitrary internal IΣ1 model. Each circuit has a literal
parameter-free Σ1 graph. No recursion on an internal circuit code or
proof-to-word correctness theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandCircuitPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticCode254
open ArithmeticCommandAppendPerm222 ArithmeticCommandBlockPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

inductive Circuit where
  | input0 | input1 | input2 | input3 | zero | one
  | plus (left right : Circuit)
  | sub (left right : Circuit)
  | pair (left right : Circuit)
  | imp (left right : Circuit)
  | append (left right : Circuit)
  | load (value : Circuit)

noncomputable def Circuit.eval : Circuit → V → V → V → V → V
  | .input0, a, _, _, _ => a
  | .input1, _, b, _, _ => b
  | .input2, _, _, c, _ => c
  | .input3, _, _, _, u => u
  | .zero, _, _, _, _ => 0
  | .one, _, _, _, _ => 1
  | .plus x y, a,b,c,u => x.eval a b c u + y.eval a b c u
  | .sub x y, a,b,c,u => x.eval a b c u - y.eval a b c u
  | .pair x y, a,b,c,u => cantor (x.eval a b c u) (y.eval a b c u)
  | .imp x y, a,b,c,u => wim (x.eval a b c u) (y.eval a b c u)
  | .append x y, a,b,c,u => appendValue (x.eval a b c u) (y.eval a b c u)
  | .load x, a,b,c,u => Jword (x.eval a b c u)

def Circuit.graph : Circuit → 𝚺₁.Semisentence 5
  | .input0 => .mkSigma “out a b c u. out = a”
  | .input1 => .mkSigma “out a b c u. out = b”
  | .input2 => .mkSigma “out a b c u. out = c”
  | .input3 => .mkSigma “out a b c u. out = u”
  | .zero => .mkSigma “out a b c u. out = 0”
  | .one => .mkSigma “out a b c u. out = 1”
  | .plus x y => .mkSigma
      “out a b c u. ∃ l, ∃ r, !(graph x) l a b c u ∧
        !(graph y) r a b c u ∧ out = l+r”
  | .sub x y => .mkSigma
      “out a b c u. ∃ l, ∃ r, !(graph x) l a b c u ∧
        !(graph y) r a b c u ∧ !Arithmetic.subDef out l r”
  | .pair x y => .mkSigma
      “out a b c u. ∃ l, ∃ r, !(graph x) l a b c u ∧
        !(graph y) r a b c u ∧ !ArithmeticCantor.pairDef out l r”
  | .imp x y => .mkSigma
      “out a b c u. ∃ l, ∃ r, !(graph x) l a b c u ∧
        !(graph y) r a b c u ∧ !ArithmeticCode254.wimDef out l r”
  | .append x y => .mkSigma
      “out a b c u. ∃ l, ∃ r, !(graph x) l a b c u ∧
        !(graph y) r a b c u ∧ !ArithmeticCommandAppendPerm222.appendDef out l r”
  | .load x => .mkSigma
      “out a b c u. ∃ l, !(graph x) l a b c u ∧
        !ArithmeticCommandBlockPerm222.JwordDef out l”

instance Circuit.defined (e : Circuit) : 𝚺₁-Function₄[V] e.eval via e.graph := by
  induction e with
  | input0 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | input1 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | input2 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | input3 => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | zero => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | one => exact .mk fun v => by simp [Circuit.graph, Circuit.eval]
  | plus x y hx hy => exact .mk fun v => by simp [Circuit.graph,Circuit.eval,hx.iff,hy.iff]
  | sub x y hx hy => exact .mk fun v => by simp [Circuit.graph,Circuit.eval,hx.iff,hy.iff]
  | pair x y hx hy => exact .mk fun v => by simp [Circuit.graph,Circuit.eval,hx.iff,hy.iff]
  | imp x y hx hy => exact .mk fun v => by simp [Circuit.graph,Circuit.eval,hx.iff,hy.iff]
  | append x y hx hy => exact .mk fun v => by simp [Circuit.graph,Circuit.eval,hx.iff,hy.iff]
  | load x hx => exact .mk fun v => by simp [Circuit.graph,Circuit.eval,hx.iff]

namespace Circuit

def two : Circuit := .plus .one .one
def three : Circuit := .plus .one two
/-- Physical C222 words: no payload for NIP/DROP; AX packs y then x. -/
def consNip (rest : Circuit) : Circuit := .plus (.pair .zero rest) .one
def consDrop (rest : Circuit) : Circuit := .plus (.pair .one rest) .one
def consMp (x rest : Circuit) : Circuit := .plus (.pair two (.pair x rest)) .one
def consAx (c x y rest : Circuit) : Circuit :=
  .plus (.pair (.plus c three) (.pair y (.pair x rest))) .one

def nips : Nat → Circuit
  | 0 => .zero
  | k+1 => consNip (nips k)

def discard : Circuit := consMp .one (consAx .one .zero .zero (nips 10))
def terminator : Circuit := consDrop (consNip (consNip .zero))

def leaf (j : Nat) (a b c u : Circuit) : Circuit :=
  .append discard (.append (.load u)
    (consAx c (.sub a u) b (.append (nips j) (consDrop (nips (11-j))))))

theorem eval_consNip (rest : Circuit) (a b c u : V) :
    (consNip rest).eval a b c u = nipWord (rest.eval a b c u) := rfl
theorem eval_consDrop (rest : Circuit) (a b c u : V) :
    (consDrop rest).eval a b c u = dropWord (rest.eval a b c u) := rfl
theorem eval_consMp (x rest : Circuit) (a b c u : V) :
    (consMp x rest).eval a b c u = mpWord (x.eval a b c u) (rest.eval a b c u) := by
  simp only [consMp,eval,two,mpWord,one_add_one_eq_two]
theorem eval_consAx (k x y rest : Circuit) (a b c u : V) :
    (consAx k x y rest).eval a b c u =
      axWord (k.eval a b c u) (x.eval a b c u) (y.eval a b c u) (rest.eval a b c u) := by
  have h3 : (1 : V)+(1+1)=3 := by rw [one_add_one_eq_two,add_comm 1 2,two_add_one_eq_three]
  simp only [consAx,eval,three,two,axWord,h3]

theorem eval_nips (k : Nat) (a b c u : V) : (nips k).eval a b c u = nipsWord k := by
  induction k with
  | zero => rfl
  | succ k hk => rw [nips,eval_consNip,hk]; rfl

theorem eval_discard (a b c u : V) : discard.eval a b c u = discardWord := by
  rw [discard,eval_consMp,eval_consAx,eval_nips]
  rfl

theorem eval_terminator (a b c u : V) : terminator.eval a b c u = ArithmeticCommandLeafPerm222.terminatorWord := rfl

theorem eval_leaf (j : Nat) (x y z w : Circuit) (a b c u : V) :
    (leaf j x y z w).eval a b c u = ArithmeticCommandLeafPerm222.leafWord j
      (x.eval a b c u) (y.eval a b c u) (z.eval a b c u) (w.eval a b c u) := by
  simp only [leaf,eval,eval_discard,eval_consAx,eval_consDrop,eval_nips,
    ArithmeticCommandLeafPerm222.leafWord]

end Circuit
end DiophantineConsistency.ArithmeticCommandCircuitPerm222
