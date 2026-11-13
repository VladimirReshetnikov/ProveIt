#!/usr/bin/env python3
"""Independent finite sanity controls for the local fold screen."""
from pathlib import Path
import importlib.util
import itertools

script = Path(__file__).with_name('scan_local_folds.py')
spec = importlib.util.spec_from_file_location('scan_local_folds', script)
fold = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fold)
table,_ = fold.read_table(fold.DEFAULT_TABLE)
contexts = fold.incoming_contexts(table)

# Generate all 196 × 32 fixed five-cell starting tapes, on a zero background,
# and take two literal steps. Each observed second-step window must occur in
# the predecessor-based overapproximation, even for arbitrary starting states.
for start in range(fold.STATES):
    for bits in itertools.product(range(2),repeat=5):
        tape = dict(zip(fold.WINDOW,bits)); state = start; head = 0
        for step in range(2):
            if state == fold.STATES: break
            value = tape.get(head,0)
            write,direction,state = table[state,value]
            tape[head] = write; head += direction
            if state == fold.STATES: break
            window = {i:tape.get(head+i,0) for i in fold.WINDOW}
            if step == 1 and window not in contexts[state,window[0]]:
                raise RuntimeError(f'Lost reachable window from {start}: {window}')

# Independent closure check: every abstract transition, including both choices
# for the newly exposed cell, stays in the recorded set or reaches halt.
blank,_,_ = fold.blank_window_contexts(table)
initial = {i:0 for i in fold.WINDOW}
if initial not in blank[0,0]: raise RuntimeError('Blank seed missing')
for (q,read),windows in blank.items():
    for window in windows:
        write,direction,target = table[q,read]
        after = dict(window); after[0] = write
        if target == fold.STATES: continue
        for fresh in (0,1):
            shifted = {i:after.get(i+direction,fresh) for i in fold.WINDOW}
            if shifted not in blank[target,shifted[0]]:
                raise RuntimeError('Blank-window set is not closed')
        if window not in contexts[q,read]:
            raise RuntimeError('Blank closure not contained in history overapproximation')

# Synthetic duplicate rows provide a positive one-step bisimulation/fold
# control. This table is not asserted to be the original hashed PA196 table.
synthetic = dict(table)
synthetic[1,0] = synthetic[2,0]; synthetic[1,1] = synthetic[2,1]
classes,_ = fold.partition_and_reachability(synthetic)
if not any(1 in c and 2 in c for c in classes):
    raise RuntimeError('Bisimulation failed the duplicate-state control')
synthetic_contexts = fold.incoming_contexts(synthetic)
for b in (0,1):
    for tape in synthetic_contexts[1,b]:
        if fold.reaches_one_step(synthetic,1,2,None,None,1,b,tape) != 1:
            raise RuntimeError('Local check failed the duplicate-state control')
print('PASS: two-step window, blank closure, and synthetic duplicate-state controls')

# Positive control from the submitted U208 construction: remap its sparse
# native labels to dense labels and check its published 211 -> 172 fold.
import hashlib
from zipfile import ZipFile
archive = Path(__file__).resolve().parents[6] / 'docs/incoming/U208_ConPA_2026-10-29.zip'
member = 'U208_ConPA_2026-10-29/baseline/u209.native.tm'
with ZipFile(archive) as package:
    data = package.read(member)
if hashlib.sha256(data).hexdigest() != 'd0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16':
    raise RuntimeError('U209 parent hash mismatch')
rows = []
for line in data.decode('ascii').splitlines():
    if not line.strip() or line.startswith('#'): continue
    q,b,w,d,t = line.split()
    rows.append((int(q),int(b),int(w),d,int(t)))
labels = sorted({q for q,b,w,d,t in rows})
if len(labels) != 209 or {t for q,b,w,d,t in rows} - set(labels) != {254}:
    raise RuntimeError('Unexpected U209 native control states')
dense = {q:i for i,q in enumerate(labels)}; dense[254] = 209
upstream = {(dense[q],b):(w,1 if d=='R' else -1,dense[t])
            for q,b,w,d,t in rows}
if len(upstream) != 418 or dense[0] != 0:
    raise RuntimeError('Unexpected U209 table domain')
fold.STATES = 209
ucontexts,_,_ = fold.blank_window_contexts(upstream,2)
drop,keep,helper = (dense[q] for q in (211,172,217))
lengths = set()
for q in (drop,keep):
    for b in (0,1):
        for window in ucontexts[q,b]:
            length = fold.reaches_one_step(upstream,drop,keep,0,(0,-1,helper),q,b,window)
            if length is None:
                raise RuntimeError('Known U209 to U208 fold did not validate')
            lengths.add(length)
if lengths != {1,3,7}:
    raise RuntimeError(f'Unexpected known fold block lengths: {lengths}')
print('PASS: archived U209 to U208 fold, block lengths 1/3/7')
