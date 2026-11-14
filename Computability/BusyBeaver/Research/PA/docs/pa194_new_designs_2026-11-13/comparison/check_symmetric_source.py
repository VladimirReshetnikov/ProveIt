#!/usr/bin/env python3
"""Check the literal source premises of the symmetric Shift lemma.

The universal mathematical lemma is proved in symmetric_guard_review.tex.
This finite checker binds that lemma to the two complete instruction maps;
it does not claim to be a general-purpose proof-assistant kernel.
"""
import argparse
import hashlib
import json
from pathlib import Path


def targets(ins):
    return ins[2:] if ins[0] in ("inc", "dec") else ins[1:] if ins[0] == "jump" else []


def check(old_path, new_path):
    old_bytes, new_bytes = old_path.read_bytes(), new_path.read_bytes()
    old, new = json.loads(old_bytes), json.loads(new_bytes)
    if len(old) != 3649 or len(new) != 3646:
        raise ValueError("Unexpected source sizes")
    guard = [["dec",5,4,1], ["dec",6,3,2], ["jump",0], ["jump",5],
             ["dec",6,10,5], ["dec",5,7,6], ["jump",5],
             ["dec",6,9,8], ["jump",5], ["jump",11], ["halt"]]
    prefix = [["dec",1,3640,3639], ["jump",3638],
              ["dec",5,3644,3641], ["inc",1,3642],
              ["inc",6,3643], ["jump",3640]]
    old_tail = [["dec",6,3647,3645], ["inc",5,3646], ["jump",3644],
                ["inc",6,3648], ["jump",0]]
    new_tail = [["inc",5,3645], ["jump",0]]
    if old[:3644] != new[:3644] or old[:11] != guard:
        raise ValueError("The preserved prefix or comparator differs")
    if old[3638:3644] != prefix or old[3644:] != old_tail or new[3644:] != new_tail:
        raise ValueError("The compared Shift tails differ from the proved templates")
    incoming = [(i, t) for i, op in enumerate(old[:3638]) for t in targets(op) if t >= 3638]
    if incoming != [(48,3638)]:
        raise ValueError("Unexpected external entry into the modified Shift block")
    for code in (old,new):
        if any(t < 0 or t >= len(code) for op in code for t in targets(op)):
            raise ValueError("Invalid source successor")
    return {
        "status":"PASS",
        "old_source_sites":len(old),"new_source_sites":len(new),
        "old_instructions_sha256":hashlib.sha256(old_bytes).hexdigest(),
        "new_instructions_sha256":hashlib.sha256(new_bytes).hexdigest(),
        "guard_source_sites":list(range(11)),
        "guard_registers":{"H":5,"X":6},
        "same_prefix_sites":3644,
        "only_external_entry_to_modified_block":[48,3638],
        "guard_exit":"pc=10 and H=X=0 iff entry H=X; otherwise pc=11 and H=X=0",
        "guard_other_registers":"unchanged",
        "guard_durations_to_first_exit":{"H=X=a":"3*a+2","H=a>X=b":"2*a+b+4","H=a<X=b":"3*b+2"},
        "shift_entry_scope":"arbitrary natural T=t,H=h,X=x; every other register arbitrary",
        "common_prefix_exit":"T=h,H=0,X=k=h+x",
        "old_guard_input":"(H,X)=(k,1)",
        "new_guard_input":"(H,X)=(1,k)",
        "shift_exit":"same pc in {10,11} and exactly the same full register vector",
        "old_minus_new_source_steps":{"k=0":0,"k=1":4,"k>=2":"2*k+4"},
        "proof_scope":"Finite syntactic binding of the explicit induction argument in symmetric_guard_review.tex; no general-purpose kernel claim."
    }


def main():
    p=argparse.ArgumentParser()
    p.add_argument("old",type=Path);p.add_argument("new",type=Path)
    p.add_argument("--output",type=Path)
    a=p.parse_args();r=check(a.old,a.new);s=json.dumps(r,indent=2)+"\n"
    if a.output:a.output.write_text(s)
    print(s,end="")


if __name__=="__main__":main()
