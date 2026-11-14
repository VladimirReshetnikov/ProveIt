#!/usr/bin/env python3
"""Reconstruct and verify the alternative 195-state scanner-eight PA machine.

Python 3 standard library, without -O. Run from any working directory.
The default replays both complete quantified symbolic contract families.
--quick omits those two runtime replays and explicitly reports that omission.
This is an executable mathematical certificate, not a proof-assistant theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'reference_pa195'))
import build_verify as v
c = v.c
SHA256 = 'df6ec639713c4ae7bb3656e59c833dd55ca6336a46bea8327eca639341b34662'


def canon(x):
    return json.loads(json.dumps(x))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick', action='store_true')
    args = ap.parse_args()
    v.need(__debug__ and not sys.flags.optimize, 'Run without Python -O')
    baseline = HERE.parent / 'reference_pa195'
    for name, digest in json.loads((baseline / 'vendor_hashes.json').read_text()).items():
        v.need(hashlib.sha256((baseline / name).read_bytes()).hexdigest() == digest,
               'vendored input hash: ' + name)
    t = c.read_grammar(HERE / 'grammar.json')
    raw, nodes, shapes = c.build(t)
    v.need(len(raw) == 404 and len(shapes) == 68, 'unextended raw census')
    v.need(raw[34, 0] == (0, False, 75) and (1999, 0) not in raw,
           'scanner extension precondition')
    raw[34, 0] = (0, False, 1999)
    raw[1999, 0] = (0, False, 75)
    raw[1999, 1] = (1, False, 2)
    v.need(raw == v.table(HERE / 'unfolded203.native.tm'), 'raw table reconstruction')
    folds = json.loads((HERE / 'folds.json').read_text())
    v.need(len(folds) == 8, 'fold count')
    folded, aliases = v.quotient(raw, folds)
    v.need(folded == v.table(HERE / 'pa195_scanner8.native.tm'), 'native reconstruction')
    cert = v.quotient_certificate(raw, folded, folds, aliases)
    v.need(canon(cert) == json.loads((HERE / 'local_fold_certificate.json').read_text()),
           'local certificate reconstruction')
    labels = json.loads((HERE / 'labels.json').read_text())
    v.need(len(labels) == 196 and len(set(labels)) == 196 and
           labels[0] == 74 and labels[-1] == 254, 'dense labels')
    dense = v.table(HERE / 'pa195_scanner8.tm')
    v.need(set(dense) == {(q, b) for q in range(195) for b in (0, 1)},
           'complete binary transition domain')
    v.need({(labels[q], b): (w, d, labels[n]) for (q, b), (w, d, n) in dense.items()}
           == folded, 'dense/native conjugacy')
    v.need(hashlib.sha256((HERE / 'pa195_scanner8.tm').read_bytes()).hexdigest()
           == SHA256, 'dense transition table hash')
    reached, todo = {0}, [0]
    for q in todo:
        for b in (0, 1):
            nxt = dense[q, b][2]
            v.need(0 <= nxt <= 195, 'transition target outside domain')
            if nxt < 195 and nxt not in reached:
                reached.add(nxt)
                todo.append(nxt)
    v.need(reached == set(range(195)), 'unreachable advertised working state')
    sites, cfg, contracts = c.source(t)
    binding = v.source_binding(t, sites, cfg)
    emitter = v.emitter(t)
    expected_source = [{'ordinal': i, 'path': ''.join(map(str, p)), 'op': op,
                        'arg': a, 'instruction': cfg[i]}
                       for i, (p, op, a) in enumerate(sites)]
    v.need(canon(expected_source) == json.loads((HERE / 'source.json').read_text()),
           'source record reconstruction')
    old, _ = c.machine()
    v.need(all(folded[q, b] == old[q, b] for q in c.BOXSTATES for b in (0, 1)),
           'changed opaque register-block lemma row')
    used = {(q, b) for q in c.BOXSTATES for b in (0, 1)}
    def observe(s):
        q, onleft, left, right = s
        if onleft or not right:
            return
        seg = right[0]
        if seg[0] == 'b' or (seg[0] == 'r' and (seg[2] > 0 or seg[3] > 0)):
            used.add((q, seg[1]))
        elif seg[0] == 'x':
            used.add((q, 0))
    result = {'working_states': 195, 'binary_rows': 390, 'start': 0, 'halt': 195,
              'graph_reachable_working_states': len(reached),
              'raw_states': 203, 'reader_states': len(shapes), 'folds': len(folds),
              'local_cases': cert['local_cases'], 'local_durations': cert['durations'],
              'source': binding, 'emitter': emitter, 'literal_sha256': SHA256,
              'full_runtime_replayed': not args.quick, 'new_kernel_checked_theorem': False}
    if not args.quick:
        for name, rows in [('raw_runtime', raw), ('folded_runtime', folded)]:
            check = c.validate(rows, contracts,
                               observe=observe if name == 'folded_runtime' else None)
            v.need(check['ok'], name + ' failed')
            result[name] = check
    q, head, ones = 0, 0, set()
    for tick in range(59164):
        bit = int(head in ones)
        used.add((labels[q], bit))
        w, d, q = dense[q, bit]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    want = {head - 1, head}
    pos = head + 48
    want.add(pos)
    pos += 1
    for reg in physical:
        pos += 1
        want.update(range(pos, pos + reg + 1))
        pos += reg + 1
    v.need(labels[q] == 84 and head == -2 and ones == want, 'exact blank startup')
    startup = {'literal_steps': 59164, 'native_state': labels[q], 'absolute_head': head,
               'header_gap': 48, 'physical_register_file': physical,
               'complete_one_positions': sorted(ones), 'outside_tape_all_zero': True}
    v.need(startup == json.loads((HERE / 'startup_certificate.json').read_text()),
           'startup certificate reconstruction')
    result['startup_literal_steps'] = 59164
    if not args.quick:
        result['unused_rows'] = sorted(set(folded) - used)
        v.need(not result['unused_rows'], 'coverage census differs')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
