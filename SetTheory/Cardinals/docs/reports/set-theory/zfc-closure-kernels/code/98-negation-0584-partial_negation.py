#!/usr/bin/env python3
"""Generate finite, explicitly located subsets of direct-negation contraction.

Every proposed replacement is LNPQMVQPW -> LMPW. The separate constructor
proof supplies its scratch-zero premise. This script only checks exact edits.
"""
import argparse
import json
from pathlib import Path

OLD = 'LNPQMVQPW'
NEW = 'LMPW'


def main():
    p = argparse.ArgumentParser()
    p.add_argument('variants', type=Path)
    p.add_argument('output', type=Path)
    a = p.parse_args()
    original = json.loads(a.variants.read_text())['variants'][0]
    word = original['old_fine_AX']
    positions = original['positions']
    assert positions == [i for i in range(len(word)) if word.startswith(OLD, i)]
    n = len(positions)
    selected = {tuple(): 'control', tuple(range(n)): 'all'}
    for i in range(n):
        selected[(i,)] = f'single_{i}'
        selected[tuple(j for j in range(n) if j!=i)] = f'all_except_{i}'
    for k in range(1,n):
        selected[tuple(range(k))] = f'prefix_{k}'
        selected[tuple(range(k,n))] = f'suffix_{k}'
    for width in (1,2,4,8,12):
        groups = {}
        for j,i in enumerate(positions):
            key = (word[max(0,i-width):i],word[i+len(OLD):i+len(OLD)+width])
            groups.setdefault(key,[]).append(j)
        for group in groups.values():
            selected.setdefault(tuple(group),f'context_{width}_'+'_'.join(map(str,group)))
    variants = []
    for k,(selection,name) in enumerate(selected.items()):
        text = word
        for j in sorted(selection,reverse=True):
            i=positions[j]
            assert text[i:i+len(OLD)] == OLD
            text=text[:i]+NEW+text[i+len(OLD):]
        variants.append(dict(mask=3000+k,name=name,fine_AX=text,
                             original_positions=[positions[j] for j in selection],
                             contractions=len(selection),
                             proof_status='REQUIRES_SEPARATE_SCRATCH_ZERO_CONSTRUCTOR_THEOREM'))
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(dict(variants=variants),indent=2)+'\n')
    print(json.dumps(dict(variants=len(variants),original_length=len(word),negations=n)))


if __name__=='__main__':
    main()
