#!/usr/bin/env python3
"""Check the append-zero engine experiment and its failed blank seed.

Default: replay the exact 78-step ray and inspect saved runtime case order.
--runtime: additionally rederive all arbitrary-natural append-zero contracts.
This is NOT an accepted blank consistency machine.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, sys, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'runtime/runtime'))
import symbolic_runtime as s

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    assert __debug__ and not sys.flags.optimize, 'Run without -O'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runtime', action='store_true')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    base = ROOT / 'baseline/k215.native.tm'
    src = ROOT / 'baseline/sites215.json'
    assert digest(base) == '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
    assert digest(src) == '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
    old = s.r.table(base)
    assert old[198, 0] == (1, -1, 40)
    old[198, 0] = (0, -1, 40)
    native = HERE / 'candidate.native.tm'
    T = s.r.table(native)
    assert old == T
    saved = json.loads((HERE / 'startup.json').read_text())
    q, h, ones = 0, 0, set()
    assert len(saved['trace']) == 78
    for state, head, bit, w, d, z in saved['trace']:
        assert (q, h, int(h in ones)) == (state, head, bit)
        assert T[q, bit] == (w, d, z)
        if w: ones.add(h)
        else: ones.discard(h)
        q, h = z, h+d
    assert (q, h, ones) == (35, 4, {-3, -2, 2})
    assert T[35, 0] == (1, 1, 35) and h > max(ones)
    sites = json.loads(src.read_text())
    with gzip.open(HERE / 'runtime_cases.json.gz', 'rt') as f:
        cases = json.load(f)
    order = [(i, p) for i, site in enumerate(sites)
             for p in ((False, True) if site[1] == 'CD' else (False,))]
    assert [(c['site_index'], c['positive']) for c in cases] == order
    assert len(cases) == 6176
    assert all(c['duration'][0] > 0 and all(v >= 0 for v in c['duration']) for c in cases)
    result = dict(status='FINITE_BINDING_RAY_AND_RECEIPT_PASS',
                  consistency_candidate=False, native_sha256=digest(native),
                  source_sha256=digest(src), blank_ray_steps=78,
                  blank_ray_state=35, blank_ray_head=4,
                  saved_runtime_cases=len(cases), runtime_rederived=False)
    if args.runtime:
        m = {int(k): int(v) for k, v in json.loads(
            (ROOT / 'runtime/inputs/legacy_mapping.json').read_text()).items()}
        for state in {q for q, _ in T} | {254}:
            if state not in m: m[state] = state + 1000
        assert len({m[q] for q in {q for q, _ in T} | {254}}) == 216
        L = {(m[q], b): (w, d, m[z]) for (q, b), (w, d, z) in T.items()}
        started = time.monotonic()
        lemmas, blocks = s.prove_blocks(L)
        fresh = []
        for i, positive in order:
            item = s.case(L, lemmas, sites[i], positive, append=0)
            item.pop('trace')
            item['rows'] = sorted(item['rows'])
            fresh.append(dict(site_index=i, positive=positive, **item))
        assert fresh == cases
        result.update(status='APPEND_ZERO_RUNTIME_PASS_BLANK_SEED_REJECTED',
                      runtime_rederived=True, runtime_seconds=time.monotonic()-started,
                      symbolic_rules=sum(c['symbolic_steps'] for c in fresh),
                      blocks=blocks)
        (args.output / 'runtime_cases.json').write_text(json.dumps(fresh)+'\n')
    (args.output / 'verification.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
