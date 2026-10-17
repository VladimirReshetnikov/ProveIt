"""Build an exact blank initializer and the 315-state clean-runtime control.

The five-state preprocessor is Marxen--Buntrock's published machine. The
adapter is new here. No source theorem is inferred for the frozen runtime.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREPROCESSOR_STEPS = 47_176_870
HANDOFF_STEPS = 47_189_196
LEFT_MARKER, HEADER = -45, 12_243
GAP = HEADER - LEFT_MARKER - 1


def build_adapter(registers=9):
    """Return named total transitions. All registers initially have value zero."""
    if type(registers) is not int or registers < 1:
        raise ValueError('positive register-block count required')
    table = {}

    def put(q, b, w, d, target):
        if (q, b) in table:
            raise ValueError('duplicate transition')
        table[q, b] = (w, d, target)

    # Published Marxen orientation; H is redirected to aux instead of halting.
    source = [((1,'L','B'),(1,'R','C')),
              ((1,'L','C'),(1,'L','B')),
              ((1,'L','D'),(0,'R','E')),
              ((1,'R','A'),(1,'R','D')),
              ((1,'L','aux'),(0,'R','A'))]
    for q, row in zip('ABCDE', source):
        for b, action in enumerate(row):
            put(q, b, *action)
    for b in (0, 1):
        put('aux', b, 1, 'R', 'header')
        put('header', b, 1, 'R', 'print:0')
    for j in range(2*registers):
        last = j == 2*registers-1
        for b in (0, 1):
            put(f'print:{j}', b, j % 2, 'L' if last else 'R',
                'back' if last else f'print:{j+1}')
    # Return across (01)^registers; the first adjacent pair is aux/header.
    put('back', 0, 0, 'L', 'back')
    put('back', 1, 1, 'L', 'back1')
    put('back1', 0, 0, 'L', 'back')
    put('back1', 1, 0, 'L', 'erase')
    # Erase periodic work tape; its sole remaining adjacent pair is at left.
    put('erase', 0, 0, 'L', 'erase')
    put('erase', 1, 0, 'L', 'erase1')
    put('erase1', 0, 0, 'L', 'erase')
    put('erase1', 1, 1, 'R', 'ENTRY')
    return table


def numeric(table, entry='A'):
    names = [entry] + sorted({q for q, _ in table} - {entry})
    labels = {q:i for i,q in enumerate(names)}
    labels['halt'] = len(names)
    expected = {(q,b) for q in names for b in (0,1)}
    if set(table) != expected:
        raise ValueError('table not total')
    lines = ['#! start 0']
    for q in names:
        for b in (0,1):
            w,d,target = table[q,b]
            if w not in (0,1) or d not in ('L','R') or target not in labels:
                raise ValueError('invalid action')
            lines.append(f'{labels[q]} {b} {w} {d} {labels[target]}')
    return ('\n'.join(lines)+'\n').encode(), labels


def build(runtime_path, output):
    runtime_bytes = runtime_path.read_bytes()
    runtime = json.loads(runtime_bytes)
    if runtime['runtime_states'] != 286 or runtime['minimum_gap'] > GAP:
        raise ValueError('unexpected runtime contract')
    adapter = build_adapter()
    if len(adapter) != 58:
        raise ValueError('unexpected initializer size')
    renamed = {(f'init:{q}',b):(w,d,runtime['entry'] if target=='ENTRY'
                else f'init:{target}') for (q,b),(w,d,target) in adapter.items()}
    for q,b,w,d,target in runtime['rows']:
        if (q,b) in renamed:
            raise ValueError('runtime/initializer name collision')
        renamed[q,b] = w,d,target
    data, labels = numeric(renamed, 'init:A')
    if len(data.splitlines()) != 631 or labels['halt'] != 315:
        raise ValueError('incorrect full-machine count')
    # Exact all-row preservation is stronger than merely equal state counts.
    for q,b,w,d,target in runtime['rows']:
        if renamed[q,b] != (w,d,target):
            raise ValueError('runtime transition changed')
    output.mkdir(parents=True, exist_ok=True)
    (output/'bb5_initializer_control_315.tm').write_bytes(data)
    standalone={(q,b):(w,d,'halt' if target=='ENTRY' else target)
                for (q,b),(w,d,target) in adapter.items()}
    init_data, _ = numeric(standalone)
    (output/'bb5_initializer_29.tm').write_bytes(init_data)
    ones=[LEFT_MARKER, HEADER]+[HEADER+2*j for j in range(1,10)]
    meta = dict(working_states=315, binary_rows=630, initializer_states=29,
                runtime_states=286, start=0, halt=315,
                runtime_entry=labels[runtime['entry']],
                exact_handoff_steps=HANDOFF_STEPS, head=LEFT_MARKER+1,
                left_marker=LEFT_MARKER, header=HEADER, gap=GAP,
                expected_ones=ones, initial_registers=[0]*9,
                runtime_rows_preserved=572,
                runtime_file_sha256=hashlib.sha256(runtime_bytes).hexdigest(),
                machine_sha256=hashlib.sha256(data).hexdigest(),
                initializer_sha256=hashlib.sha256(init_data).hexdigest(),
                full_runtime_simulation_proved=False,
                new_con_zfc_machine_record=False,
                preprocessor_source='https://www.turbotm.de/~heiner/BB/simmbL5_1-m.html')
    (output/'initializer_metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
    (output/'initializer_labels.json').write_text(json.dumps(labels,indent=2)+'\n')
    return meta


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--runtime',type=Path,default=HERE/'runtime_286.json')
    p.add_argument('--output',type=Path,default=HERE/'output')
    a=p.parse_args()
    print(json.dumps(build(a.runtime,a.output),indent=2))
