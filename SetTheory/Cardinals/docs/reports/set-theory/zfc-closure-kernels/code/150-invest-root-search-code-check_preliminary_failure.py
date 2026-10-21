#!/usr/bin/env python3
"""Reproduce why the preliminary 166-into-12 fold cannot inherit the runtime proof."""
from pathlib import Path
import argparse, hashlib, json, sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check_joint_fold as tables


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--packet-root', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    root, out = a.packet_root.resolve(), a.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    sys.path.insert(0, str(root / 'core217/vendor'))
    import independent_runtime as r

    source = root / 'baseline218/sites218.json'
    sites = json.loads(source.read_text())
    site = sites[3126]
    require(site[1:] == ['CI', 3], 'expected CI3 at source site 3126')
    mp = {int(q): int(z) for q, z in json.loads(
        (root / 'core217/vendor/legacy_mapping.json').read_text()).items()}
    mp.update({301: 1301, 302: 1302})
    inverse = {z: q for q, z in mp.items()}

    def load(path):
        native, start = tables.read(path)
        return {(mp[q], b): (w, d, mp[z])
                for (q, b), (w, d, z) in native.items()}

    def describe(conf):
        q, h, ones = conf
        return {'native_state': inverse[q], 'head': h, 'ones': sorted(ones)}

    candidate = HERE.parent / 'data/rejected-166-into-12.native.tm'
    baseline = load(root / 'baseline218/k218.native.tm')
    changed = load(candidate)
    registers, spares, gap = [0] * 9, [0], 0
    expected = r.expected(site, registers, spares, gap)
    actual_old, steps_old, trace_old = r.run(
        baseline, site[0], registers, spares, gap, trace=True)
    actual_new, steps_new, trace_new = r.run(
        changed, site[0], registers, spares, gap, trace=True)
    require(actual_old == expected[0], 'baseline positive control')
    require(actual_new != expected[0], 'expected concrete fold failure')
    ones = r.frame(site[0], registers, spares, gap)
    dispatcher_visits = []
    for tick, q, h, b, w, d, z in trace_old:
        if q == 96:
            dispatcher_visits.append({'step': tick, 'head': h,
                                     'clean': r.clean_dispatch(q, h, ones)})
        if w:
            ones.add(h)
        else:
            ones.discard(h)
    dispatcher_visits.append({'step': steps_old, 'head': actual_old[1],
                             'clean': r.clean_dispatch(*actual_old)})
    result = {
        'status': 'CONCRETE_RUNTIME_COUNTEREXAMPLE',
        'scope': 'Valid complete primitive frame; this is not a blank-tape behavior claim.',
        'candidate_sha256': hashlib.sha256(candidate.read_bytes()).hexdigest(),
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'site_index': 3126, 'site': site, 'registers': registers,
        'spares': spares, 'gap': gap,
        'baseline_passed': True, 'baseline_steps': steps_old,
        'baseline_dispatcher_visits': dispatcher_visits,
        'candidate_steps': steps_new,
        'candidate_actual': describe(actual_new),
        'expected': describe(expected[0]),
        'expected_logical': expected[1],
        'trace_file': 'preliminary-counterexample-trace.json',
        'lesson': 'A visit to dispatcher state 84 can be intermediate. Context generation must continue until the complete clean-frame predicate holds.'}
    (out / result['trace_file']).write_text(json.dumps([
        [tick, inverse[q], h, b, w, d, inverse[z]]
        for tick, q, h, b, w, d, z in trace_new], indent=2) + '\n')
    (out / 'preliminary-failure.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'site_index', 'site',
        'baseline_steps', 'baseline_dispatcher_visits', 'candidate_steps')}, indent=2))


if __name__ == '__main__':
    main()
