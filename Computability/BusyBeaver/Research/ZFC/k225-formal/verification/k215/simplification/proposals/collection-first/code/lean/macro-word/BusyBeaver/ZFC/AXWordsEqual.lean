import BusyBeaver.ZFC.L2AxiomsDom
import BusyBeaver.ZFC.AXReadCons

/-! Exact effect equality of the two maintained AX routines. The two physical
word-to-DAG checks are not identified; only their abstract register effects are.
This imports and uses the actual maintained definitions on both sides. -/
namespace SetTheory.BusyBeaver.ZFC.AXWordsEqual
open L2K GenericMacroWord

set_option maxRecDepth 4096

def toPerm : L2Dom.AXAtom → L2Perm.AXAtom
  | .par1 => .par1 | .par2 => .par2 | .par3 => .par3 | .push => .push
  | .cons => .cons | .wel => .wel | .wal => .wal | .weq => .weq
  | .wn => .wn | .wa => .wa | .wex => .wex | .readp2 => .readp2 | .readp1 => .readp1

def mapWord (word : List (L2Dom.AXAtom × Nat)) : List (L2Perm.AXAtom × Nat) :=
  word.map fun x => (toPerm x.1, x.2)

theorem effect_toPerm (a : L2Dom.AXAtom) (st : AS) :
    L2Dom.AXAtom.effect a st = L2Perm.AXAtom.effect (toPerm a) st := by
  cases a <;> rfl

theorem perm_eval (word : List (L2Perm.AXAtom × Nat)) (st : AS) :
    L2Perm.axWordEval word st = eval L2Perm.AXAtom.effect L2Perm.gateF word st := by
  induction word generalizing st with
  | nil => rfl
  | cons a rest ih => exact ih _

theorem dom_eval (word : List (L2Dom.AXAtom × Nat)) (st : AS) :
    L2Dom.axWordEval word st =
      eval L2Perm.AXAtom.effect L2Perm.gateF (mapWord word) st := by
  induction word generalizing st with
  | nil => rfl
  | cons a rest ih =>
      simp only [L2Dom.axWordEval, mapWord, List.map_cons, eval]
      rw [effect_toPerm]
      exact ih _

def pre : List (L2Perm.AXAtom × Nat) := L2Perm.axWord.take 6
def post : List (L2Perm.AXAtom × Nat) := L2Perm.axWord.drop 8

theorem perm_shape : L2Perm.axWord =
    pre ++ (.cons, 486) :: (.readp1, 474) :: post := rfl

/-- Erase routing labels before comparing the semantic words. -/
theorem dom_shape : (mapWord L2Dom.axWord).map Prod.fst =
    (pre ++ (.readp1, 486) :: (.cons, 474) :: post).map Prod.fst := rfl

/-- The complete AX effects agree for every abstract register record,
including records whose scratch registers are not clean. -/
theorem f236_eq (st : AS) : L2Perm.f236 st = L2Dom.f236 st := by
  unfold L2Perm.f236 L2Dom.f236
  rw [perm_eval, dom_eval, perm_shape]
  exact (AXReadCons.reordered_word pre post 486 474 st).symm.trans
    (eval_labels L2Perm.AXAtom.effect L2Perm.gateF _ _ dom_shape.symm st)

/-- The existing Dom effect specification is obtained from the Perm theorem.
This demonstrates a concrete replacement for the second symbolic evaluation. -/
theorem dom_ax_eval_from_perm (np t S c a h pl : Nat) :
    L2Dom.f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, EnumDom.gate (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) (h + (Cantor.ofNat pl).1) c,
        EnumDom.axStack (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) h (h + (Cantor.ofNat pl).1) c a
          t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  rw [← f236_eq]
  exact L2Perm.ax_eval np t S c a h pl

#print axioms f236_eq
#print axioms dom_ax_eval_from_perm
end SetTheory.BusyBeaver.ZFC.AXWordsEqual
