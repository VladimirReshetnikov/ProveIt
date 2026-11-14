#!/usr/bin/env python3
"""Compare the complete blank startup and its canonical whole-tape frame."""
import argparse
import hashlib
import json
from pathlib import Path
from check_runtime import need, read, sha

def execute(table, n=48140):
    q = head = 0; ones = set(); visited = set(); digest = hashlib.sha256()
    for step in range(n):
        need(q != 254, 'Premature halt')
        bit = int(head in ones); w, d, z = table[q, bit]
        digest.update(f'{step} {q} {head} {bit} {w} {d} {z}\n'.encode()); visited.add((q, bit))
        ones.add(head) if w else ones.discard(head); q = z; head += d
    return (q, head, ones), digest.hexdigest(), visited

def verify(parent, machine, sites, output):
    old, _ = read(parent, 209); new, _ = read(machine, 208)
    a, ha, va = execute(old); b, hb, vb = execute(new)
    need(a == b and ha == hb, 'Blank startup changed')
    need(a[:2] == (84, -2), 'Unexpected dispatcher or head')
    source = json.loads(Path(sites).read_text()); address = source[136][0]
    need(address == '001100110101010', 'Startup source address changed')
    registers = [1, 0, 13, 0, 0, 1, 0, 0, 1]; physical = [0]*9
    for i, j in enumerate((6, 2, 0, 4, 3, 7, 8, 5, 1)): physical[j] = registers[i]
    expected = {-3, 54} | {-2+i for i, bit in enumerate(address) if bit == '1'}; position = 55
    for value in physical + [1]*43:
        expected.update(range(position+1, position+value+2)); position += value+2
    need(a[2] == expected and len(expected) == 120, 'Whole canonical frame mismatch')
    delta = {k for k in old.keys() | new.keys() if old.get(k) != new.get(k)}
    need(not va & delta, 'Startup visits a modified transition')
    result = dict(status='EXACT_BLANK_STARTUP_PASS', steps=48140, state=84, head=-2,
                  header=54, header_distance=56, source_ordinal=136, source_address=address,
                  logical_registers=registers, spares=[1]*43, one_cells=sorted(expected),
                  zero_exterior=True, entire_trace_equal=True, trace_sha256=ha,
                  changed_rows=sorted(delta), changed_row_visits=0,
                  parent_sha256=sha(parent), native_sha256=sha(machine))
    Path(output).write_text(json.dumps(result, indent=2)+'\n'); return result

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('parent', 'machine', 'sites', 'output'): p.add_argument('--'+name, type=Path, required=True)
    a=p.parse_args();r=verify(a.parent,a.machine,a.sites,a.output)
    print(json.dumps({k:v for k,v in r.items() if k not in ('one_cells', 'spares')},indent=2))
