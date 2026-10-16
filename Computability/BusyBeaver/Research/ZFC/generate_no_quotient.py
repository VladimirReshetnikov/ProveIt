"""Generate/check modular refinement colors for the narrow exact-step quotient theorem.

The Lean file independently checks every cached recurrence and final distinctness.
The generator is not trusted as a proof checker. No whole-machine minimality claim.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path
from audit_tm import parse_table
ROOT = Path(__file__).resolve().parents[4]
SOURCE = ROOT / "lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm"
OUTPUT = ROOT / "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NoQuotient254.lean"
SHA256 = "d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb"

HEADER = r'''import BusyBeaver.ZFC.StateReduction
import BusyBeaver.ZFC.Table254

/-!
A narrow obstruction to exact step-preserving state quotients of the literal
254-state benchmark. Cached modular colors are checked against every transition;
all final working-state colors differ. Hash collisions can only weaken this
method, never create an unsound distinction. No global machine minimality,
blank-tape-only reduction obstruction, or ZFC consistency endpoint is claimed.
-/
namespace SetTheory.BusyBeaver.ZFC.NoQuotient254

set_option maxRecDepth 20000
set_option maxHeartbeats 0

universe u v

def optionColor {Q : Type u} (color : Q → Nat) : Option Q → Nat
  | none => 0
  | some q => color q + 1

def actionColor {Q : Type u} (color : Q → Nat) (a : TypedAction Q) : Nat :=
  (((if a.write then 1 else 0) + 2 * (match a.move with | .left => 0 | .right => 1))
    * 65537 + optionColor color a.next) % 2147483647

def stateColor {Q : Type u} (machine : TypedMachine Q) (color : Q → Nat) (q : Q) : Nat :=
  (actionColor color (machine.transition q false) * 65537 +
    actionColor color (machine.transition q true)) % 2147483647

theorem optionColor_congr {Q : Type u} {R : Type v} {f : Q → R}
    {color : Q → Nat} (hc : ∀ q q', f q = f q' → color q = color q')
    {a b : Option Q} (hab : a.map f = b.map f) :
    optionColor color a = optionColor color b := by
  cases a with
  | none => cases b <;> simp_all [optionColor]
  | some q =>
      cases b with
      | none => simp at hab
      | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hab
          simp only [optionColor, hc q q' hab]

theorem actionColor_congr {Q : Type u} {R : Type v} {f : Q → R}
    {color : Q → Nat} (hc : ∀ q q', f q = f q' → color q = color q')
    {a b : TypedAction Q} (hab : mapAction f a = mapAction f b) :
    actionColor color a = actionColor color b := by
  have hw := congrArg TypedAction.write hab
  have hm := congrArg TypedAction.move hab
  have hn := congrArg TypedAction.next hab
  dsimp only [mapAction] at hw hm hn
  unfold actionColor
  rw [hw, hm, optionColor_congr hc hn]

theorem stateColor_congr {Q : Type u} {R : Type v} {f : Q → R}
    {original : TypedMachine Q} {reduced : TypedMachine R}
    (certificate : TransitionQuotient f original reduced)
    {color : Q → Nat} (hc : ∀ q q', f q = f q' → color q = color q')
    (q q' : Q) (h : f q = f q') :
    stateColor original color q = stateColor original color q' := by
  have ha : ∀ bit, mapAction f (original.transition q bit) =
      mapAction f (original.transition q' bit) := by
    intro bit
    rw [← certificate q bit, ← certificate q' bit, h]
  unfold stateColor
  rw [actionColor_congr hc (ha false), actionColor_congr hc (ha true)]

'''

FOOTER = r'''
def colorCache : List (List Nat) := [
  round0, round1, round2, round3, round4, round5, round6,
  round7, round8, round9, round10, round11, round12, round13]

def cachedColor (round : Nat) (q : Fin 254) : Nat :=
  (colorCache.getD round []).getD q.val 0

theorem cachedColor_zero (q : Fin 254) : cachedColor 0 q = 1 := by
  revert q
  decide

/-- Every cached entry is checked against the literal machine's two transitions. -/
theorem cachedColor_step : ∀ r : Fin 13, ∀ q : Fin 254,
    cachedColor (r.val + 1) q = stateColor typedMachine254 (cachedColor r.val) q := by
  decide

theorem finalRound_length : round13.length = 254 := by decide

theorem finalRound_nodup : round13.Nodup := by decide

theorem finalColor_injective : Function.Injective (cachedColor 13) := by
  intro q q' h
  apply Fin.ext
  change round13.getD q.val 0 = round13.getD q'.val 0 at h
  exact (List.getD_inj (by rw [finalRound_length]; exact q.isLt)
    (by rw [finalRound_length]; exact q'.isLt) finalRound_nodup).mp h

theorem cachedColor_congr {R : Type u} {f : Fin 254 → R}
    {reduced : TypedMachine R} (certificate : TransitionQuotient f typedMachine254 reduced) :
    ∀ n, n ≤ 13 → ∀ q q', f q = f q' → cachedColor n q = cachedColor n q' := by
  intro n
  induction n with
  | zero => intro _ q q' _; rw [cachedColor_zero, cachedColor_zero]
  | succ n ih =>
      intro hn q q' hf
      have hlt : n < 13 := by omega
      rw [cachedColor_step ⟨n, hlt⟩ q, cachedColor_step ⟨n, hlt⟩ q']
      exact stateColor_congr certificate (ih (by omega)) q q' hf

/-- Any exact one-step quotient of this table is injective on its 254 working states.
This does not exclude reductions using reachability, macros, or a different program. -/
theorem exactQuotient254_injective {R : Type u} {f : Fin 254 → R}
    {reduced : TypedMachine R} (certificate : TransitionQuotient f typedMachine254 reduced) :
    Function.Injective f := by
  intro q q' h
  exact finalColor_injective (cachedColor_congr certificate 13 (by decide) q q' h)

#print axioms cachedColor_step
#print axioms finalRound_nodup
#print axioms exactQuotient254_injective

end SetTheory.BusyBeaver.ZFC.NoQuotient254
'''


def generate(source: Path) -> str:
    raw = source.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SHA256:
        raise ValueError("table does not match the pinned machine hash")
    machine = parse_table(raw.decode())
    if machine.start != 0 or machine.halt != 254 or machine.states != list(range(254)):
        raise ValueError("unexpected machine labels")
    colors = [[1] * 254]
    for _ in range(13):
        previous = colors[-1]
        def action(q: int, bit: int) -> int:
            edge = machine.rows[q, bit]
            target = 0 if edge.target == 254 else previous[edge.target] + 1
            return ((edge.write + 2 * int(edge.move == 1)) * 65537 + target) % 2147483647
        colors.append([(action(q, 0) * 65537 + action(q, 1)) % 2147483647
                       for q in range(254)])
    if len(set(colors[-1])) != 254:
        raise ValueError("final colors are not pairwise distinct")
    declarations = []
    for number, row in enumerate(colors):
        lines = [", ".join(map(str, row[i:i+8])) for i in range(0, len(row), 8)]
        declarations.append(f"def round{number} : List Nat := [\n  " + ",\n  ".join(lines) + "]\n")
    return HEADER + "\n".join(declarations) + FOOTER


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=SOURCE)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = generate(args.source)
    if args.check:
        if args.output.read_text() != result:
            parser.error("generated refinement certificate differs")
        print("Checked 14 cached rows, including 13 transition-refinement rounds")
    else:
        args.output.write_text(result)
        print(f"Generated {args.output}")


if __name__ == "__main__":
    main()
