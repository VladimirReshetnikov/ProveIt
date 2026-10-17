#!/usr/bin/env python3
"""Finite row-use controls for transporting the generic Box.v lemmas.

The universal argument is the source proof in Box.v. This independent sparse
simulation checks its four exact excursion contracts on nonzero spare tails
and verifies that every executed transition agrees in the old and new tables.
"""
import argparse
import hashlib
import json
from pathlib import Path


def table(path):
    result = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t = line.split()
            result[int(q),int(b)] = (int(w),d,int(t))
    return result


def file_ones(vs, marked=None):
    ones = set()
    cursor = 0
    for r,v in enumerate(vs):
        ones.update(range(cursor+1,cursor+v+2))
        if marked == r:
            ones.remove(cursor+1)
        cursor += v+2
    return ones


def check(root):
    old = table(root/'vendor/busy-beaver/ZF/m254/machine/zfc_254.tm')
    newpath = root/'machines/runtime252-old-labels.tm'
    new = table(newpath)
    skips = [60,44,31,56,38,40,28,64,69]
    used = set()
    cases = 0
    steps_total = 0
    longest = 0
    for r in range(9):
        for pattern in range(3):
            vs = [0 if pattern==0 else (i+pattern)%4 for i in range(9)] + [2,0,1,3]
            for kind in ('mark','inc','dec0','decp'):
                vals = [0] if kind=='dec0' else [1,2,5] if kind=='decp' else [0,1,3]
                for value in vals:
                    before = list(vs); before[r] = value
                    left = {-2,-4} if pattern%2 else {-1,-3}
                    after = list(before)
                    if kind=='mark':
                        q = skips[r]; outq = 2 if r==0 else 6
                        ones = file_ones(before) | left
                        target = file_ones(after,r) | left
                    else:
                        q = 73 if kind=='inc' else 43
                        outq = 48 if kind=='inc' else 3 if kind=='dec0' else 63 if r==0 else 48
                        ones = file_ones(before,r) | left
                        if kind=='inc': after[r] += 1
                        elif kind=='decp': after[r] -= 1; after.append(0)
                        target = file_ones(after) | left
                    h = 0; steps = 0
                    while not (steps and q==outq and h==-1 and ones==target):
                        assert steps < 100000,(kind,r,value,'fuel')
                        key = (q,int(h in ones))
                        assert key in new and new[key]==old[key],(kind,r,value,'changed row reached',key)
                        used.add(key)
                        w,d,q = old[key]
                        if w: ones.add(h)
                        else: ones.discard(h)
                        h += 1 if d=='R' else -1
                        steps += 1
                    cases += 1; steps_total += steps; longest = max(longest,steps)
    return {'scope':'finite sparse controls supplementing generic Box.v source proof',
            'cases':cases,'literal_steps':steps_total,'longest_excursion':longest,
            'all_contracts_exact':True,'all_executed_rows_unchanged':True,
            'new_old_label_table_sha256':hashlib.sha256(newpath.read_bytes()).hexdigest(),
            'used_transition_keys':[list(x) for x in sorted(used)],
            'changed_or_deleted_keys':[[3,0],[5,0],[5,1],[8,0],[8,1]]}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('package',type=Path)
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('box_transport_check.json'))
    a = p.parse_args(); result = check(a.package)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='used_transition_keys'},indent=2))


if __name__=='__main__': main()
