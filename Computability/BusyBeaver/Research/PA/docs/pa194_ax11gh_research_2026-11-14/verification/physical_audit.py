# Adapted from the updated incoming AX11H packet at pinned ProveIt revision.
# Changes are paths, candidate manifest and the two exact source/outcome counts.
#!/usr/bin/env python3
"""Finite closure/duration audit for the AX11GH/AX11GHS literal certificates.

This supplements verification/independent/check.py: it checks all recorded affine
durations and all nonhalting endpoint addresses against the independently
resolved instruction graph.  It is not a replacement for literal replay.

Run from an unpacked bundle with:
  python3 physical_ipra_audit.py --bundle PATH --output audit_receipt.json
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(bundle):
    assert __debug__ and not sys.flags.optimize, 'Run without -O.'
    reference = bundle / 'verification' / 'independent' / 'reference'
    sys.path.insert(0, str(reference))
    import source_language as source
    import independent_runtime as runtime
    import symbolic_runtime as sym
    sym.HEADER_BASE = 48
    ops = {'inc': 'CI', 'dec': 'CD', 'breakTo': 'CB',
           'continueTo': 'CC', 'halt': 'CH'}
    result = []
    for name in ('PA194AX11GH', 'PA194AX11GHS'):
        folder = bundle / 'machines' / name
        recorded = bundle / 'verification' / 'independent' / 'recorded' / name
        nsites, noutcomes = (3671, 4778) if name == 'PA194AX11GH' else (3668, 4774)
        def local_path(p):
            return recorded / p.split('/', 1)[1] if p.startswith('independent/') else folder / p
        sites = json.loads((folder / 'sites.json').read_text())
        sites = [[''.join(map(str, p)) if isinstance(p, list) else p, op, a]
                 for p, op, a in sites]
        mapped = [[p, ops[op], a] for p, op, a in sites]
        source.tree(mapped)  # Full prefix tree, valid registers/control depths.
        graph, _ = source.graph_arithmetic(mapped)
        assert graph == source.graph_intervals(mapped)
        names = {'identity': 'jump', 'increment': 'inc',
                 'decrement': 'dec', 'halt': 'halt'}
        instructions = [[names[e[0]]] + e[1:] + targets
                        for e, targets in graph]
        assert instructions == json.loads((folder / 'instructions.json').read_text())
        contracts = json.loads((recorded / 'contracts.json').read_text())
        receipt = json.loads((recorded / 'receipt.json').read_text())
        assert receipt['status'] == 'PASS'
        assert sha(folder / 'machine.native.tm') == receipt['native_sha256']
        assert sha(folder / 'machine.tm') == receipt['dense_sha256']
        assert sha(recorded / 'contracts.json') == receipt['contracts_sha256']
        native = runtime.table(folder / 'machine.native.tm')
        controls = {q for q, b in native}
        assert len(controls) == 194
        assert set(native) == {(q, b) for q in controls for b in (0, 1)}
        assert {target for w, d, target in native.values()} - controls == {254}
        mapping = {int(k): v for k, v in
                   json.loads((reference / 'legacy_mapping.json').read_text()).items()}
        for q in controls | {254}:
            mapping.setdefault(q, q + 10000)
        assert len({mapping[q] for q in controls | {254}}) == 195
        assert mapping[84] == 96 and mapping[254] == 254
        table = {(mapping[q], b): (w, d, mapping[target])
                 for (q, b), (w, d, target) in native.items()}
        lemmas, blocks = sym.prove_blocks(table)
        assert len(lemmas) == 4
        assert json.loads(json.dumps(blocks)) == json.loads(
            (recorded / 'list_lemmas.json').read_text())
        required = [(i, positive) for i, (_, op, _) in enumerate(mapped)
                    for positive in ([False, True] if op == 'CD' else [False])]
        assert [(c['site'], c['positive']) for c in contracts] == required
        assert len(sites) == nsites and len(contracts) == noutcomes
        minimum = None
        maximum = [0] * 13
        overflow_counts = Counter()
        endpoint_checks = 0
        halt_checks = 0
        for c in contracts:
            duration, motion = c['duration'], c['motion']
            assert len(duration) == len(motion) == 13
            assert all(type(a) is int and a >= 0 for a in duration)
            assert duration[0] >= 3
            minimum = duration[0] if minimum is None else min(minimum, duration[0])
            maximum = [max(a, b) for a, b in zip(maximum, duration)]
            i, positive = c['site'], c['positive']
            pc, op, arg = mapped[i]
            effect, targets = graph[i]
            overflow = 0
            if op == 'CH':
                assert not positive and effect == ['halt'] and not targets
                assert duration == [3] + [0] * 12
                halt_checks += 1
                continue
            if op == 'CI' or (op == 'CD' and positive):
                successor, overflow = runtime.inc(pc)
            elif op in ('CD', 'CB'):
                successor, overflow = runtime.inc(runtime.strip(
                    pc, '0', arg if op == 'CB' else 1))
            elif op == 'CC':
                successor = runtime.strip(pc, '1', arg)
            else:
                raise AssertionError(op)
            j = targets[int(positive)] if op == 'CD' else targets[0]
            target_pc = mapped[j][0]
            assert len(successor) <= 48 and len(target_pc) <= 48
            assert successor + '0' * (48 - len(successor)) == (
                target_pc + '0' * (48 - len(target_pc)))
            assert overflow == 0 and motion == [0] * 13
            overflow_counts[overflow] += 1
            endpoint_checks += 1
        assert endpoint_checks == noutcomes - 1 and halt_checks == 1
        assert sum(c['symbolic_steps'] for c in contracts) == receipt['symbolic_steps']
        assert max(c['symbolic_steps'] for c in contracts) == receipt['maximum_symbolic_steps']
        paths = ['machine.native.tm', 'machine.tm', 'sites.json', 'instructions.json',
                 'independent/contracts.json', 'independent/list_lemmas.json',
                 'independent/receipt.json']
        result.append(dict(
            name=name, status='PASS',
            opcounts=dict(Counter(op for _, op, _ in sites)),
            sites=len(sites), outcomes=len(contracts),
            max_path_depth=max(len(p) for p, _, _ in sites),
            nonhalting_endpoint_checks=endpoint_checks, halting_outcome_checks=halt_checks,
            overflow_counts=dict(overflow_counts),
            all_nonhalt_target_padding_matches=True,
            minimum_duration_constant=minimum,
            max_duration_coefficients=maximum,
            symbolic_steps=receipt['symbolic_steps'],
            maximum_symbolic_steps=receipt['maximum_symbolic_steps'],
            generic_block_derivations_replayed=4,
            hashes={p: sha(local_path(p)) for p in paths}))
    refs = ['independent/check.py', 'independent/reference/symbolic_runtime.py',
            'independent/reference/independent_runtime.py', 'independent/reference/source_language.py',
            'independent/reference/legacy_mapping.json']
    return dict(status='PASS', audit='physical/source frame closure and affine durations',
                note='Run verification/independent/check.py separately for full literal certificate replay.',
                verification_hashes={p: sha(bundle / 'verification' / p) for p in refs},
                machines=result)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', required=True, type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    answer = json.dumps(check(args.bundle.resolve()), indent=2) + '\n'
    if args.output:
        args.output.write_text(answer)
    print(answer)
