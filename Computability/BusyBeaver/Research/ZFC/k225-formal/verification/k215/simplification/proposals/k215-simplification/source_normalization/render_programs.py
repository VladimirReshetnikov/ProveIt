#!/usr/bin/env python3
"""Split the original 487-node WF check into low-memory kernel batches.
The exact programs, height/escape tables and wfCheck222 statement are unchanged.
"""
from pathlib import Path
if not __debug__:
    raise SystemExit('Run this generator without Python -O; its validation uses assertions.')

BASE=Path(__file__).resolve().parent
OUT=BASE/'normalized_lean'

def main():
    p=(BASE/'upstream/KSource215Data.lean').read_text()
    p=p[:p.index('/-- The 215\'s decoder tree')]
    p=p.replace('import BusyBeaver.ZFC.RMOffsetBisim','import BusyBeaver.ZFC.RMBisim').replace('open RegisterPath RMBisim RMOffsetBisim','open RegisterPath RMBisim')
    hs=p.index('/-!');he=p.index('-/',hs)+2
    p=p[:hs]+'''/-!
Exact K215 programs and the unchanged structured-program well-formedness claim.
The 487-node Boolean WF condition is checked in sixteen small kernel batches
to bound peak memory. Programs and metric tables are copied from pinned commit
b6c7087477e51c017003bd729e712c8969733223. This module contains no source-bisimulation
certificate; shared decoder trees and the normalized certificate are separate.
-/'''+p[he:]
    start=p.index('theorem wfCheck222 :');end=p.index('theorem wf222 :')
    pred='RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0)'
    s=''
    for i,a in enumerate(range(0,487,32)):
        size=min(32,487-a)
        s+=f'private theorem wf_part{i} : ∀ n : Fin {size},\n    {pred} ({a} + n.val) = true := by decide +kernel\n\n'
    s+=f'private theorem wf_nodes (n : Nat) (hn : n < 487) : {pred} n = true := by\n'
    for i,a in enumerate(range(0,487,32)):
        size=min(32,487-a)
        if a+size<487:s+=f'  by_cases h{i} : n < {a+size}\n  · '
        else:s+='  '
        s+=f'have he : {a} + (n - {a}) = n := by omega\n'
        indent='    ' if a+size<487 else '  '
        s+=indent+f'have h := wf_part{i} ⟨n - {a}, by omega⟩\n'+indent+'simpa only [he] using h\n'
    s+='\ntheorem wfCheck222 :\n    RMEquiv.wfCheck DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0)\n      (fun n => tC.getD n 0) = true := by\n'
    s+='  unfold RMEquiv.wfCheck\n  rw [Bool.and_eq_true]\n  constructor\n  · decide +kernel\n  · rw [List.all_eq_true]\n    intro n hn\n    exact wf_nodes n (List.mem_range.mp hn)\n\n'
    p=p[:start]+s+p[end:]+'\nend SetTheory.BusyBeaver.ZFC.KSource215\n'
    (OUT/'KSource215Programs.lean').write_text(p)
    print(len(p.encode()))

if __name__=='__main__':main()
