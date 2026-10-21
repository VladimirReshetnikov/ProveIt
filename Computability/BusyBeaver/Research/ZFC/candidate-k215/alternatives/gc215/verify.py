#!/usr/bin/env python3
"""Offline GC215 replay, using Python 3 standard library only.

Default: literal reconstruction, source/CFG audit, decoder-merge proof, complete
blank trace, dense renaming, logical certificates, corpus comparison, and saved
runtime metadata. --runtime freshly rederives all 6,151 universal cases.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
import time

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not run Python with -O.')
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'checks'))
import tm


def run_check(name, *args):
    result = subprocess.run([sys.executable, '-B', str(ROOT / 'checks' / name),
                             *map(str, args)], capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'{name} failed:\n{result.stdout}\n{result.stderr}')
    print(f'PASS {name}', flush=True)


def reconstruct(work):
    r = json.loads((ROOT / 'source/table_recipe.json').read_text())
    basepath = ROOT / r['baseline']
    assert tm.digest(basepath) == r['baseline_sha256']
    base = tm.read_table(basepath.read_bytes())
    parent = dict(base)
    for q, b, w, d, z in r['parent_changes']:
        parent[q, b] = (w, d, z)
    raw = tm.table_bytes(parent)
    assert raw == (ROOT / r['parent']).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == r['parent_sha256']
    keep, delete = r['merge']['keep'], r['merge']['delete']
    candidate = {(q, b): (w, d, keep if z == delete else z)
                 for (q, b), (w, d, z) in parent.items() if q != delete}
    q, b, w, d, z = r['merge']['patch']; candidate[q, b] = (w, d, z)
    raw = tm.table_bytes(candidate)
    assert raw == (ROOT / r['candidate']).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == r['candidate_sha256']
    result = {'status': 'EXACT_RECONSTRUCTION_PASS',
              'parent_states': len(parent) // 2,
              'candidate_states': len(candidate) // 2,
              'changed_retained_rows_from_ST215': sum(
                  k in base and candidate[k] != base[k] for k in candidate),
              'deleted_native_labels_from_ST215': sorted({q for q, b in base} - {q for q, b in candidate}),
              'added_native_labels_from_ST215': sorted({q for q, b in candidate} - {q for q, b in base})}
    (work / 'reconstruction.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def manifest():
    data = json.loads((ROOT / 'MANIFEST.json').read_text())
    for item in data['files']:
        p = ROOT / item['path']
        assert p.is_file() and p.stat().st_size == item['bytes'], item['path']
        assert tm.digest(p) == item['sha256'], item['path']
    return {'status': 'PASS', 'files': len(data['files'])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runtime', action='store_true')
    parser.add_argument('--work', type=Path)
    parser.add_argument('--no-manifest', action='store_true', help='Development only')
    args = parser.parse_args()
    work = args.work.resolve() if args.work else Path(tempfile.mkdtemp(prefix='gc215-replay-'))
    work.mkdir(parents=True, exist_ok=True)
    start = time.monotonic(); result = {'runtime_requested': args.runtime}
    if not args.no_manifest:
        result['manifest'] = manifest()
    result['reconstruction'] = reconstruct(work)
    run_check('render_dense_table.py')
    run_check('check_source.py', ROOT / 'reference/st215.sites.json',
              ROOT / 'source/gc215.sites.json', work / 'source')
    run_check('check_decoder_merge.py', '--parent', ROOT / 'reference/gc216.native.tm',
              '--table', ROOT / 'machine/gc215.native.tm', '--out', work / 'merge')
    assert (work / 'merge/GC215.tm').read_bytes() == (ROOT / 'machine/gc215.tm').read_bytes()
    assert (work / 'merge/native-to-dense.json').read_bytes() == (ROOT / 'machine/native-to-dense.json').read_bytes()
    run_check('check_startup.py', ROOT / 'machine/gc215.native.tm',
              ROOT / 'source/gc215.sites.json', work / 'startup')
    for name in ('bootstrap.json', 'AX-prefix.json', 'blank-delta.jsonl.gz'):
        assert (work / 'startup' / name).read_bytes() == (ROOT / 'evidence' / name).read_bytes()
    run_check('check_startup_independent.py', '--native', ROOT / 'machine/gc215.native.tm',
              '--dense', ROOT / 'machine/gc215.tm', '--source', ROOT / 'source/gc215.sites.json',
              '--evidence', ROOT / 'evidence', '--output', work / 'startup-independent.json')
    import check_fixed_certificate as fixed
    logical = fixed.verify(fixed.read_json(ROOT / 'reference/dominated_rho8_full_certificate.json'), True)[0]
    assert logical['proof_nodes'] == 3728 and logical['term_table_nodes'] == 5160
    result['inherited_dominated_certificate'] = {'proof_nodes': 3728, 'status': 'PASS'}
    run_check('check_quantifier_padding.py', ROOT / 'research/quantifier_padding_certificate.json')
    run_check('check_quantifier_independent.py', ROOT / 'research/quantifier_padding_certificate.json',
              '--out', work / 'quantifier_independent.json')
    run_check('check_strict_fragment.py', ROOT / 'research/strict_fragment_certificate.json',
              work / 'strict_fragment.json')
    run_check('check_orientation_certificate.py', '--certificate',
              ROOT / 'reference/dominated_rho8_full_certificate.json', '--output', work / 'orientation.json')
    run_check('../research/sources/audit_costs.py', '--output', work / 'research_costs.json')
    run_check('check_fused_transfer.py')
    run_check('check_engine_route.py', '--table', ROOT / 'machine/gc215.native.tm',
              '--out', work / 'engine-route')
    assert (work / 'engine-route/engine-route.native.tm').read_bytes() == (ROOT / 'research/engine-route.native.tm').read_bytes()
    run_check('check_novelty.py', '--table', ROOT / 'machine/gc215.native.tm',
              '--corpus', ROOT / 'reference/corpus', '--provenance', ROOT / 'reference/corpus_provenance.json', '--output', work / 'novelty.json')
    import check_runtime
    result['runtime_metadata'] = check_runtime.audit(ROOT, work)
    if args.runtime:
        result['runtime_fresh'] = check_runtime.run(ROOT, work)
    result.update(status='FULL_REPLAY_PASS' if args.runtime else 'FINITE_REPLAY_PASS',
                  seconds=time.monotonic() - start,
                  scope='Ordinary mathematical verification; no new Lean/Rocq or internal PA endpoint.')
    (work / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'work': str(work),
                      'seconds': result['seconds'], 'runtime_requested': args.runtime}, indent=2))


if __name__ == '__main__':
    main()
