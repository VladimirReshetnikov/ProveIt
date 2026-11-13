#!/usr/bin/env python3
"""Bind the Lean table and checkpoints to the two rejected archive machines."""
from hashlib import sha256
from pathlib import Path
import re
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[6]
ARCHIVE = REPO / 'docs/incoming/conpa_tm_comparison_and_reduction_search.zip'
PINS = {
    'REJECTED_shift_layout.tm': 'db5cd7df1475e4c2edf43f856493e211ed116a7a998eaada741515840424736b',
    'REJECTED_combined_layout.tm': 'd3a049def261732d1c1aa99a48de63c00a1241f02b629b2ae45d445bba6c9527',
}
ARCHIVE_SHA = '46cd1a5f57f6c04f9a0379fa8dc042120bc6ae0329c370ca5d4a3d35907b5d48'


def need(ok, why):
    if not ok:
        raise ValueError(why)


def read_table(data):
    table = {}
    for line in data.decode('ascii').splitlines():
        q, bit, write, direction, dest = line.split()
        q, bit, write, dest = map(int, (q, bit, write, dest))
        need(q in range(196) and bit in (0,1) and write in (0,1) and
             direction in ('L','R') and dest in range(197) and
             (q,bit) not in table, 'invalid row')
        table[q,bit] = (write, 1 if direction == 'R' else 0, dest)
    need(set(table) == {(q,b) for q in range(196) for b in (0,1)}, 'row census')
    return table


def main():
    need(sha256(ARCHIVE.read_bytes()).hexdigest() == ARCHIVE_SHA, 'archive digest')
    tables = []
    with ZipFile(ARCHIVE) as archive:
        for name, digest in PINS.items():
            data = archive.read('conpa_tm_comparison_and_reduction_search/rejected/' + name)
            need(sha256(data).hexdigest() == digest, 'member digest: ' + name)
            tables.append(read_table(data))
    old, changed = tables
    need([(key,old[key],changed[key]) for key in sorted(old) if old[key] != changed[key]] ==
         [((115,1),(1,1,86),(1,1,108))], 'tables differ outside the stated row')
    source = (HERE / 'Cert/Common.lean').read_text()
    text = source.split('def rows : Array (Nat × Nat × Nat) := #[\n',1)[1].split('\n]',1)[0]
    encoded = [tuple(map(int, x)) for x in re.findall(r'\((\d+),(\d+),(\d+)\)',text)]
    need(encoded == [old[q,b] for q in range(196) for b in (0,1)],
         'Lean table differs from archive')
    segments = []
    pattern = re.compile(r'^theorem seg(\d+) : safeRun (\d+) \((\d+),(\d+),(\d+)\) = some \((\d+),(\d+),(\d+)\) := by decide$',re.M)
    for path in sorted((HERE / 'Cert').glob('Batch*.lean')):
        segments.extend((int(i), int(n), tuple(map(int,(q,l,r))), tuple(map(int,(Q,L,R))))
                        for i,n,q,l,r,Q,L,R in pattern.findall(path.read_text()))
    segments.sort()
    need(len(segments) == 171 and [x[0] for x in segments] == list(range(171)),
         'checkpoint census')
    state, steps = (0,0,0), 0
    before = None
    for _, length, start, end in segments:
        need(start == state and length in range(1,257), 'checkpoint start')
        for _ in range(length):
            q,left,right = state
            need(q != 196, 'halt before reported final step')
            bit = right % 2
            need((q,bit) != (115,1), 'changed row was visited')
            w,d,q = old[q,bit]
            state = (q, 2*left+w, right//2) if d else (
                q, left//2, 4*(right//2)+2*w+left%2)
            steps += 1
            if steps == 43562:
                before = state
        need(state == end, 'checkpoint end')
    need(steps == 43563 and state[0] == 196, 'halt witness')
    before_source = (HERE / 'Cert/Before.lean').read_text()
    before_tuple = ','.join(map(str, before))
    need('some (' + before_tuple + ') := by decide' in before_source and
         before[0] == 63, 'penultimate checkpoint')
    print('Archive hashes, both exact tables, 171 checkpoints, first halt at 43563, and avoided row: OK')


if __name__ == '__main__':
    main()
