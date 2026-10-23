import BusyBeaver.ZFC.KZip

/-!
Exact concrete runs of a K-family table, for the blank-tape bootstrap (port of K230's `Boot230.v`).

`lstep` steps a list zipper `(q, l, r)` without renormalizing trailing blanks, through a balanced
lookup tree of the table (`TT.look`, logarithmic in the state number). `lblock F d` runs `2 ^ d`
steps. Both are sound for the zipper semantics of `KZip` (`lblock_sound`), so a chain of kernel
decisions `lblock F d s = some s'` proves a long run. The checkpoint data is untrusted.
-/

namespace SetTheory.BusyBeaver.ZFC.KBoot

open KZip

/-- A balanced transition tree: index bits are read least significant first. -/
inductive TT where
  | leaf (r0 r1 : Option (Bool × Bool × Nat))
  | node (even odd : TT)

def TT.look : TT → Nat → Bool → Option (Bool × Bool × Nat)
  | .leaf r0 r1, _, b => if b then r1 else r0
  | .node e o, q, b => if q % 2 = 0 then e.look (q / 2) b else o.look (q / 2) b

/-- The tree as a transition function on states below `256`. -/
def fastOf (t : TT) : TMN := fun q b => if q < 256 then t.look q b else none

abbrev LConf := Nat × List Bool × List Bool

def lconc (s : LConf) : Conf := zc s.1 s.2.1 s.2.2

def lstep (F : TMN) : LConf → Option LConf
  | (q, l, r) =>
      match F q (r.headD false) with
      | none => none
      | some (w, true, q') => some (q', w :: l, r.tail)
      | some (w, false, q') => some (q', l.tail, l.headD false :: w :: r.tail)

def lblock (F : TMN) : Nat → LConf → Option LConf
  | 0, s => lstep F s
  | d + 1, s =>
      match lblock F d s with
      | none => none
      | some s' => lblock F d s'

theorem lstep_sound {F M : TMN} (hF : ∀ q b, F q b = M q b) {s s' : LConf}
    (h : lstep F s = some s') : step M (lconc s) = some (lconc s') := by
  obtain ⟨q, l, r⟩ := s
  simp only [lstep, hF] at h
  simp only [lconc, step_zc]
  split at h
  · simp at h
  all_goals rename_i w q' hm; rw [hm]; simp only [Option.some.injEq] at h ⊢; subst h; rfl

theorem lblock_sound {F M : TMN} (hF : ∀ q b, F q b = M q b) :
    ∀ (d : Nat) {s s' : LConf}, lblock F d s = some s' → run M (2 ^ d) (lconc s) = some (lconc s')
  | 0, s, s', h => by simp [run, lstep_sound hF h]
  | d + 1, s, s', h => by
      simp only [lblock] at h
      cases h1 : lblock F d s with
      | none => simp [h1] at h
      | some s1 =>
          rw [h1] at h
          rw [Nat.pow_succ, Nat.mul_two, run_add, lblock_sound hF d h1]
          exact lblock_sound hF d h

theorem lblock_reach {F M : TMN} (hF : ∀ q b, F q b = M q b) {d : Nat} {s s' : LConf}
    (h : lblock F d s = some s') : Reach M (lconc s) (lconc s') :=
  ⟨_, lblock_sound hF d h⟩

end SetTheory.BusyBeaver.ZFC.KBoot
