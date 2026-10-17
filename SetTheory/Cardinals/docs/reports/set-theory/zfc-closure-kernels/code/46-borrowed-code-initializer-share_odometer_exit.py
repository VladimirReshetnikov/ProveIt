"""Share the odometer's final left scan with the unchanged Mira/Wade engine.

The dispatcher-return technique follows source34 of ProveIt's batch152;
the odometer itself is new in this package. Exact expected actions are
checked rather than inferred from state names.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True

from exact_state_quotient import encode, minimize, parse, verify


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--controls', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    inputs = json.loads((args.controls/'integration_results.json').read_text())
    records = []
    for old in inputs:
        source_path = args.controls/old['table_file']
        data = source_path.read_bytes()
        assert hashlib.sha256(data).hexdigest() == old['table_sha256']
        source = parse(data)
        stem = source_path.stem
        source_labels = json.loads((args.controls/(stem+'-labels.json')).read_text())
        reverse = {q: name for name, q in source_labels.items()}
        named = {(reverse[q], b): (w, d, reverse[t])
                 for (q, b), (w, d, t) in source.items()}
        assert named['o:exit_scan', 0] == (0, 'L', 'o:exit_scan')
        assert named['o:exit_scan', 1] == (1, 'R', 'd:0')
        assert named['e:2', 0] == (0, 'L', 'e:2')
        assert named['e:2', 1] == (1, 'L', 'e:4')
        chain = [4, 6, 9, 13, 19, 29, 41, 58, 74]
        for j, q in enumerate(chain):
            target = f'e:{chain[j+1]}' if j+1 < len(chain) else 'e:84'
            assert named[f'e:{q}', 0] == (0, 'L', target)
        assert named['e:84', 0] == (0, 'R', 'e:84')
        assert named['e:84', 1] == (1, 'R', 'd:0')
        assert all(q.startswith('o:') for (q, b), (w, d, t) in named.items()
                   if t == 'o:exit_scan')
        shared = {(q, b): (w, d, 'e:2' if t == 'o:exit_scan' else t)
                  for (q, b), (w, d, t) in named.items() if q != 'o:exit_scan'}
        # Every runtime row remains equal by label, including all targets.
        assert {k: v for k, v in shared.items() if not k[0].startswith('o:')} == {
            k: v for k, v in named.items() if not k[0].startswith('o:')}
        start = old['initializer']['start']
        states = {q for q, b in shared}
        order = [start] + sorted(states-{start})
        labels = {q: j for j, q in enumerate(order)} | {'halt': len(order)}
        table = {(labels[q], b): (w, d, labels[t]) for (q, b), (w, d, t) in shared.items()}
        assert len(table) == 2*len(states) and len(states)+1 == old['working_states']
        contract = dict(old['initializer'])
        contract['initializer_states'] -= 1
        contract['blank_steps'] += 20
        contract['shared_exit'] = True
        contract['shared_exit_engine_labels'] = ['e:2']+[f'e:{q}' for q in chain]+['e:84']
        q, h, tape = 0, 0, set()
        for steps in range(contract['blank_steps']+1):
            if q == labels['d:0']:
                break
            w, d, q = table[q, int(h in tape)]
            if w:
                tape.add(h)
            else:
                tape.discard(h)
            h += 1 if d == 'R' else -1
        expected = old['initializer_literal_replay']
        assert q == labels['d:0'] and steps == contract['blank_steps']
        assert h == expected['head'] and tape == set(expected['final_ones'])
        path = args.output/(stem+'-shared.tm')
        path.write_bytes(encode(table))
        quotient, cert = minimize(table)
        qp = args.output/(stem+'-shared-quotient.tm')
        qp.write_bytes(encode(quotient))
        cp = args.output/(stem+'-shared-quotient.json')
        cp.write_text(json.dumps(cert, indent=2)+'\n')
        verify(parse(path.read_bytes()), parse(qp.read_bytes()), cert)
        rev = {q: name for name, q in labels.items()}
        result = dict(input_table=old['table_file'], input_table_sha256=old['table_sha256'],
            proveit_pin=old['proveit_pin'], upstream_pin=old['upstream_pin'],
            initializer=contract, raw_states=len(states), quotient_states=len(quotient)//2,
            raw_root_state=labels['d:0'], quotient_root_state=cert['state_map'][labels['d:0']],
            raw_table=path.name, raw_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            quotient_table=qp.name, quotient_sha256=hashlib.sha256(qp.read_bytes()).hexdigest(),
            quotient_certificate=cp.name,
            quotient_classes=[[rev[x] for x in group] for group in cert['nontrivial_classes']],
            blank_run=dict(passed=True, steps=steps, head=h, final_ones=sorted(tape),
                           whole_tape_sha256=expected['whole_tape_sha256']),
            all_runtime_rows_unchanged=True,
            inherited_affine_cases=old['symbolic_site_checks']['cases_passed'],
            affine_checker_reexecuted=False,
            affine_scope='Same runtime by exact label equality and same gap as checked input',
            kernel_checked=False, new_consistency_bound_claimed=False)
        records.append(result)
        print(stem, len(states), '->', len(quotient)//2, 'steps', steps)
    (args.output/'shared_results.json').write_text(json.dumps(records, indent=2)+'\n')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('assertions must be enabled')
    main()
