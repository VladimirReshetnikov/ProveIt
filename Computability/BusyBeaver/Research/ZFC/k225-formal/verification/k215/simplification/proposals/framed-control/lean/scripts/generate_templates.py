#!/usr/bin/env python3
"""Emit finite Lean replay certificates; generation itself is not proof evidence."""
from pathlib import Path
import argparse, hashlib, json

def boolean(value):
    if value not in (False, True, 0, 1):
        raise ValueError(value)
    return 'true' if value else 'false'

def seg(value):
    if value[0] == 'b':
        return f'.bit {boolean(value[1])}'
    if value[0] == 'r':
        return f'.run {boolean(value[1])} {int(value[2])} {int(value[3])}'
    if value[0] == 'x':
        if value[1] == 'none':
            return '.box (.plain .none)'
        if value[1] in ('inc', 'dec'):
            return f'.box (.plain (.{value[1]} {int(value[2])}))'
        if value[1] == 'mark':
            return f'.box (.mark {int(value[2])})'
    raise ValueError(value)

def segs(values):
    return '[' + ', '.join(seg(v) for v in values) + ']'

def conf(value):
    q, onl, left, right = value
    return f'({int(q)}, {boolean(onl)}, {segs(left)}, {segs(right)})'

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).parent/'lean/FramedTemplates.lean')
    args = parser.parse_args()
    raw = args.input.read_bytes()
    data = json.loads(raw)
    templates = data['templates_data']
    source = '''import LeftFrame
import BusyBeaver.ZFC.KTable215

/-!
Finite local replay data for the maintained K215 table. Every reduction below
is checked by Lean's kernel using decide; no external/native decision oracle.
The source-program binding is supplied separately by caller certificates.
-/
namespace SetTheory.BusyBeaver.ZFC.KFramedTemplates
open KZip KRuntimeCore KLeftFrame KTableCore

structure LocalTemplate where
  steps : Nat
  start : SConf
  returnState : Nat
  right : List Seg
  deriving DecidableEq, Repr, Inhabited

def checked (t : LocalTemplate) : Bool :=
  decide (runLocal tm215 none t.steps t.start =
    some ((t.returnState, true, [], t.right), true))

'''
    source += f'-- Input SHA-256: {hashlib.sha256(raw).hexdigest()}\n'
    for i, item in enumerate(templates):
        q, onl, left, right = item['pre_home']
        if not onl or left:
            raise ValueError('A template must end at a return state on the empty local left list')
        source += f'def template{i:02d} : LocalTemplate :=\n  ⟨{int(item["steps"])}, {conf(item["start"])}, {int(q)}, {segs(right)}⟩\n\n'
    source += 'def templates : List LocalTemplate :=\n  [' + ', '.join(f'template{i:02d}' for i in range(len(templates))) + ']\n\n'
    source += f'theorem template_count : templates.length = {len(templates)} := rfl\n\n'
    source += '''set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem all_checked : templates.all checked = true := by decide

theorem checked_of_mem {t : LocalTemplate} (ht : t ∈ templates) : checked t = true :=
  (List.all_eq_true.mp all_checked) t ht

theorem replay_of_checked {t : LocalTemplate} (h : checked t = true) :
    runLocal tm215 none t.steps t.start =
      some ((t.returnState, true, [], t.right), true) :=
  of_decide_eq_true h

theorem replay_of_mem {t : LocalTemplate} (ht : t ∈ templates) :
    runLocal tm215 none t.steps t.start =
      some ((t.returnState, true, [], t.right), true) :=
  replay_of_checked (checked_of_mem ht)

theorem template_sound {t : LocalTemplate} (ht : t ∈ templates)
    (B : BoxLemmas tm215) (hb : KHome.Boundary tm215)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) (P : List Bool)
    (hword : wordEnd tm215 t.returnState (P.reverse ++ [true]) = some 2) :
    Reach1 tm215
      (conc n vs (addLeft ((P.reverse.map Seg.bit) ++ [.bit true]) t.start))
      (zc 84 [true] (P ++ flat n vs t.right)) :=
  runLocal_home_word B hb n hv P (wordEnd_sound hword) (replay_of_mem ht)

#print axioms all_checked
#print axioms replay_of_mem
#print axioms template_sound

end SetTheory.BusyBeaver.ZFC.KFramedTemplates
'''
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source)
    print(json.dumps(dict(input=str(args.input), output=str(args.output), templates=len(templates),
        symbolic_steps=sum(t['steps'] for t in templates), source_bytes=len(source.encode()),
        input_sha256=hashlib.sha256(raw).hexdigest())))

if __name__ == '__main__':
    main()
