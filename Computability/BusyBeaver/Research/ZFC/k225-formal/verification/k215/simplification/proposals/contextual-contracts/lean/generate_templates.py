#!/usr/bin/env python3
"""Emit data only; Lean's kernel checks every resulting local execution.

The input is the repository's FORMAL_TEMPLATES.json, with maintained labels.
The generator is not part of the trusted proof boundary.
"""
import argparse
import hashlib
import json
from pathlib import Path

def boolean(b):
    if b not in (True, False, 0, 1):
        raise ValueError(b)
    return 'true' if b else 'false'

def seg(x):
    if x[0] == 'b':
        return '.bit ' + boolean(x[1])
    if x[0] == 'r':
        return f'.run {boolean(x[1])} {x[2]} {x[3]}'
    if x == ['x', 'none', 0]:
        return '.box (.plain .none)'
    raise ValueError(x)

def segs(xs):
    return '[' + ', '.join(seg(x) for x in xs) + ']'

def conf(s):
    return f'({s[0]}, {boolean(s[1])}, {segs(s[2])}, {segs(s[3])})'

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('input',type=Path)
    ap.add_argument('--output',type=Path,default=Path('BusyBeaver/ZFC/KLeftFrame215.lean'))
    a=ap.parse_args()
    raw=a.input.read_bytes()
    data=json.loads(raw)
    ts=data['templates_data']
    assert len(ts)==35
    lines=['import BusyBeaver.ZFC.KLeftFrame',
           'import BusyBeaver.ZFC.KTable215', '',
           '/-! Generated from the existing formal-label template data.',
           f'Input SHA-256: {hashlib.sha256(raw).hexdigest()}',
           'Every local replay is checked by ordinary `decide` below.',
           'The input generator and JSON are not trusted. -/', '',
           'namespace SetTheory.BusyBeaver.ZFC.KLeftFrame215',
           'open KZip KRuntimeCore KLeftFrame KTableCore', '',
           'set_option maxRecDepth 100000',
           'set_option maxHeartbeats 0', '',
           'structure Template where',
           '  start : SConf',
           '  steps : Nat',
           '  right : List Seg', '',
           'def templates : List Template := [']
    for i,t in enumerate(ts):
        assert t['id']==i
        end=t['pre_home']
        assert end[:3]==[2,True,[]]
        assert t['steps']==len(t['trace'])
        lines.append(f'  -- Template {i}: {t["key"][3]} {t["key"][4]}, suffix {t["key"][2]}.')
        lines.append(f'  ⟨{conf(t["start"])}, {t["steps"]}, {segs(end[3])}⟩'+(',' if i<34 else ']'))
    lines.extend(['',
        'def checked (t : Template) : Bool :=',
        '  decide (runLocal tm215 none t.steps t.start = some (2, true, [], t.right))', '',
        'theorem template_count : templates.length = 35 := by decide', '',
        'theorem all_checked : templates.all checked = true := by decide', '',
        '/-- Each literal template applies to every symbolic left frame. -/',
        'theorem template_reach (B : BoxLemmas tm215) {t : Template}',
        '    (ht : t ∈ templates) (F : List Seg) (n : Nat) {vs : List Nat}',
        '    (hv : Valid none vs) :',
        '    Reach tm215 (conc n vs (addLeft F t.start))',
        '      (conc n vs (addLeft F (2, true, [], t.right))) := by',
        '  have hc := of_decide_eq_true (List.all_eq_true.mp all_checked t ht)',
        '  exact runLocal_sound B n hv F t.steps t.start _ hc', '',
        '/-- A whole-tape contract for every caller prefix accepted by Home.',
        'The existing engine contracts provide B, rows and hb at the endpoint. -/',
        'theorem template_home (B : BoxLemmas tm215) (rows : KHome.Rows tm215)',
        '    (hb : KHome.Boundary tm215) {t : Template} (ht : t ∈ templates)',
        '    (P : List Bool) {k : Nat}',
        '    (hp : KHome.scanBound 0 (P.reverse.map Seg.bit) = some k)',
        '    (n : Nat) {vs : List Nat} (hv : Valid none vs) :',
        '    Reach1 tm215 (conc n vs (addLeft (P.reverse.map Seg.bit ++ [.bit true]) t.start))',
        '      (zc 84 [true] (P ++ flat n vs t.right)) := by',
        '  have hc := of_decide_eq_true (List.all_eq_true.mp all_checked t ht)',
        '  exact local_home B rows hb hc P hp n hv', '',
        '#print axioms all_checked',
        '#print axioms template_reach',
        '#print axioms template_home', '',
        'end SetTheory.BusyBeaver.ZFC.KLeftFrame215',''])
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text('\n'.join(lines))
    print(json.dumps({'templates':len(ts),'local_steps':sum(t['steps'] for t in ts),
        'max_steps':max(t['steps'] for t in ts),'input_sha256':hashlib.sha256(raw).hexdigest(),
        'output_sha256':hashlib.sha256(a.output.read_bytes()).hexdigest()},indent=2))

if __name__=='__main__':main()
