#!/usr/bin/env python3
"""Instantiate the four existing unary-register proofs on the new literal table.

Only module/machine names, finite state type and named state constants change.
Each constant is relocated by its explicitly recorded original proof label.
Lean must check all resulting literal transition equalities and proofs afresh.
The generator is not a proof of any table transfer. --check performs no writes.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[4]
LEAN=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
PARTS=('RegisterBoxes','RegisterMark','RegisterIncrement','RegisterDecrement')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    data=json.loads((ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-permutation252/renumbering.json').read_text())
    mapping={old:new for new,old in enumerate(data['canonical_to_old'])}
    assert mapping[64]==0 and mapping[96]==94 and len(mapping)==252
    for name in PARTS:
        source=LEAN/(name+'253.lean');original=source.read_text()
        lines=original.splitlines(keepends=True);replacements=0
        for i,line in enumerate(lines):
            if re.search(r'⟨\d+, by decide⟩',line):
                match=re.search(r'⟨(\d+), by decide⟩.*-- old(\d+)',line)
                if match is None:raise ValueError(f'Unlabelled concrete finite constant: {source}:{i+1}')
                new=mapping[int(match[2])]
                lines[i]=line.replace(f'⟨{match[1]}, by decide⟩',f'⟨{new}, by decide⟩')
                replacements+=1
        assert replacements=={'RegisterBoxes':6,'RegisterMark':12,'RegisterIncrement':6,'RegisterDecrement':4}[name]
        text=''.join(lines)
        text=text.replace('BusyBeaver.ZFC.Table253','BusyBeaver.ZFC.TablePerm252')
        for part in PARTS:text=text.replace(part+'253',part+'Perm252')
        text=text.replace('machine253','machinePerm252').replace('Fin 253','Fin 252').replace('Config 253','Config 252')
        text=text.replace('actual public253','actual permutation252').replace('actual253 boxes','actual permutation252 boxes')
        text=text.replace('literal compact253 table','literal compact252 table')
        # Preserve original attribution while making this new instantiation explicit.
        text=text.replace('/-!\n',f'/-!\nInstantiated from {name}253.lean for the new permutation252 table.\n'
          f'Source SHA256: {hashlib.sha256(original.encode()).hexdigest()}.\n'
          'The proof bodies are retained; all named states are independently relocated\n'
          'using their original labels. Every row theorem must be checked on the new table.\n\n',1)
        target=LEAN/(name+'Perm252.lean')
        if args.check:
            assert target.read_text()==text,target
        else:target.write_text(text)
        print(('MATCH' if args.check else 'WROTE'),target.relative_to(ROOT),replacements,'named states')


if __name__=='__main__':main()
