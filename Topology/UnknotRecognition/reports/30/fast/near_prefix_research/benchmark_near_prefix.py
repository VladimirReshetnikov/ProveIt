"""A/A-controlled audit of exact SLP LCS with a bounded suffix deficit."""
import argparse
from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
from time import perf_counter, process_time
from types import ModuleType
from unittest.mock import patch

BASELINE = '8a95834940cf77cdab1b39571ffc102ca8b6bede'
BASELINE_PATH = 'Topology/UnknotRecognition/fast/fastunknot/compressed_lcs.py'
BASELINE_SHA256 = '85061dbf63f3d0af417b5819a0d67d026b70412560d36bbea1fc3faebfdbc412'


def load_baseline_source(fast, baseline_source=None):
    """Load the exact frozen source, with a hash-checked archive fallback."""
    if baseline_source is not None:
        path = baseline_source.resolve()
        raw, origin = path.read_bytes(), str(path)
    else:
        try:
            raw = subprocess.check_output(['git', 'show', f'{BASELINE}:{BASELINE_PATH}'],
                                          cwd=fast, stderr=subprocess.PIPE)
            origin = f'git:{BASELINE}:{BASELINE_PATH}'
        except (OSError, subprocess.CalledProcessError):
            path = Path(__file__).resolve().with_name('baseline_compressed_lcs.py')
            try:
                raw, origin = path.read_bytes(), str(path)
            except OSError as fallback_error:
                raise FileNotFoundError(
                    'Pinned git snapshot and sibling baseline_compressed_lcs.py are unavailable; '
                    'supply --baseline-source pointing to the archived source') from fallback_error
    actual = hashlib.sha256(raw).hexdigest()
    if actual != BASELINE_SHA256:
        raise ValueError(f'Baseline source hash mismatch: expected {BASELINE_SHA256}, got {actual}')
    return raw.decode('utf-8'), origin


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--baseline-source', type=Path,
                        help='Use this exact frozen LCS source instead of git; its SHA-256 is checked')
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--kernels-only', action='store_true')
    parser.add_argument('--queries-only', action='store_true')
    args = parser.parse_args()
    fast = args.fast_dir.resolve()
    sys.path.insert(0, str(fast))
    from benchmark_compressed_words import cases
    from fastunknot import Diagram, recognize, compressed_lcs
    from fastunknot.compressed_words import WordArena, CompressedLimit

    source, baseline_origin = load_baseline_source(fast, args.baseline_source)
    module = ModuleType('fastunknot.archived_near_prefix_lcs')
    module.__package__ = 'fastunknot'
    exec(compile(source, f'{BASELINE}:{BASELINE_PATH}', 'exec'), module.__dict__)
    old, current = module.CommonSubstring, compressed_lcs.CommonSubstring

    class GenericDiagonals(current):
        """Same exact diagonal reduction, with general LCE primitives."""
        def near_prefix(self, x, y, prefix, limit, max_alignments=32):
            a = self.arena
            nx, ny = a.lengths[x], a.lengths[y]
            dx, dy = nx-prefix, ny-prefix
            count = dx+dy-1
            if count > max_alignments or prefix < count-1 or min(dx, dy) < 1:
                return None
            cut, best = dx-1, (prefix, 0, 0)
            a.stats['lcs_generic_diagonal_queries'] = a.stats.get('lcs_generic_diagonal_queries', 0)+1
            for delta in range(1-dx, dy):
                a.tick()
                other = cut+delta
                before = self.suffix(a.slice(x, 0, cut), a.slice(y, 0, other))
                after = a.lcp(a.slice(x, cut, nx), a.slice(y, other, ny))
                if before+after > best[0]:
                    best = min(before+after, limit), cut-before, other-before
                    if best[0] == limit:
                        break
            return best

    @contextmanager
    def environment(arm):
        cls = current if arm == 'full' else GenericDiagonals if arm == 'generic-diagonals' else old
        with patch.object(compressed_lcs, 'CommonSubstring', cls):
            yield cls

    def build(family, bits):
        a, n = WordArena(max_work=2000000), 2**bits
        p = a.power(a.from_word([1, 2]), n)
        if family == 'positive-shift':
            return a, a.concat(p, a.letter(3)), a.concat(p, a.from_word([1, 2, 3])), 2*n+1
        if family == 'interior-control':
            half = a.power(a.from_word([1, 2]), n//2)
            x = a.concat(a.concat(a.letter(3), half), a.concat(half, a.letter(2)))
            y = a.concat(a.concat(a.letter(2), half), a.concat(half, a.letter(3)))
            return a, x, y, 2*n
        tail = a.from_word([1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3])
        if family == 'large-deficit-control':
            tail = a.power(tail, 3)
        x = a.concat(p, a.concat(a.letter(3), tail))
        y = a.concat(p, a.concat(a.letter(1), tail))
        return a, x, y, 2*n

    data = dict(complete=False, python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, baseline_lcs_sha256=hashlib.sha256(source.encode()).hexdigest(),
        baseline_source=baseline_origin,
        benchmark_driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        current_lcs_sha256=hashlib.sha256((fast/'fastunknot/compressed_lcs.py').read_bytes()).hexdigest(),
        seed=3103, measured_rounds=args.rounds, excluded_warmups=1, max_alignments=32,
        kernel_max_work=2000000, max_nodes=100000, group_max_work=20000000,
        group_seconds=15, global_seconds=18,
        comparison='Archived LCS class, identical A/A control, generic-LCE diagonal ablation, new cycle-automaton diagonals',
        query_scope='Fresh PD construction, full recognition, independent certificate replay; digest outside clock',
        kernel_scope='Complete grammar construction and exact uncapped LCS; known analytic answer checked outside clock',
        limited_scope='Supplied string operations; no claim of faster completed unknot recognition',
        censoring='LIMIT is an incomplete query, never a negative result or completed-time denominator',
        rows=[], kernels=[])
    try:
        import regina
        data['regina'] = regina.versionString()
    except ImportError:
        data['regina'] = None
    rng = random.Random(data['seed'])

    def save():
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(data, indent=2)+'\n')

    if not args.kernels_only:
        for name, diagram in cases():
            samples = []
            for repetition in range(args.rounds+1):
                order, measurements = ['baseline', 'control', 'full'], {}
                rng.shuffle(order)
                for arm in order:
                    with environment(arm):
                        start, cpu = perf_counter(), process_time()
                        result = recognize(Diagram.from_pd(diagram.pd), use_group=True,
                            group_compressed_search=True, group_relators=True,
                            group_seconds=15, group_max_work=20000000, seconds=18, max_objects=50000)
                        elapsed, cpu_elapsed = perf_counter()-start, process_time()-cpu
                    group = result.evidence.get('group', {})
                    measurements[arm] = dict(seconds=elapsed, cpu_seconds=cpu_elapsed,
                        status=result.status, method=result.method, search_stats=group.get('search_stats'),
                        certificate_sha256=hashlib.sha256(json.dumps(group.get('certificate'),
                            sort_keys=True).encode()).hexdigest())
                    assert result.status == 'UNKNOT', (name, arm, result.status)
                assert len({m['certificate_sha256'] for m in measurements.values()}) == 1
                if repetition:
                    samples.append(dict(order=order, measurements=measurements))
            row = dict(name=name, pd=diagram.pd, samples=samples,
                median_seconds={arm: median(s['measurements'][arm]['seconds'] for s in samples)
                    for arm in ('baseline', 'control', 'full')})
            data['rows'].append(row)
            save()
            print('query', name, row['median_seconds'], flush=True)

    if not args.queries_only:
        for family in ('equal-bigrams', 'positive-shift', 'large-deficit-control', 'interior-control'):
            for bits in (8, 32, 100, 500):
                samples = []
                arms = (['baseline', 'control', 'generic-diagonals', 'full']
                    if family in ('equal-bigrams', 'positive-shift') else ['baseline', 'control', 'full'])
                for repetition in range(args.rounds+1):
                    order, measurements = list(arms), {}
                    rng.shuffle(order)
                    for arm in order:
                        with environment(arm) as factory:
                            start, cpu = perf_counter(), process_time()
                            a, x, y, expected = build(family, bits)
                            try:
                                answer = factory(a).longest(x, y)
                                status, reason = 'COMPLETE', None
                            except CompressedLimit as exc:
                                answer, status, reason = None, 'LIMIT', str(exc)
                            elapsed, cpu_elapsed = perf_counter()-start, process_time()-cpu
                        if answer is not None:
                            assert answer[0] == expected, (family, bits, arm, answer, expected)
                            assert 0 <= answer[1] <= a.lengths[x]-answer[0]
                            assert 0 <= answer[2] <= a.lengths[y]-answer[0]
                        measurements[arm] = dict(seconds=elapsed, cpu_seconds=cpu_elapsed,
                            status=status, reason=reason, answer=answer,
                            nodes=len(a.rules)-1, stats=a.stats.copy())
                    if repetition:
                        samples.append(dict(order=order, measurements=measurements))
                row = dict(family=family, bits=bits, samples=samples,
                    median_seconds={arm: median(s['measurements'][arm]['seconds'] for s in samples) for arm in arms})
                data['kernels'].append(row)
                save()
                print('kernel', family, bits, {arm: (measurements[arm]['status'], row['median_seconds'][arm])
                    for arm in arms}, flush=True)
    data['complete'] = True
    save()


if __name__ == '__main__':
    main()
