"""Bounded literal new-rule evaluation of the frozen universal source.

The old stored trace is an independent valid-state comparison, not execution.
No universal eager template array or source-boundary shortcut is used.
"""
import argparse
from dataclasses import asdict
from hashlib import sha256
import json
from pathlib import Path
import random
import resource
import time
import sparse_parallel as sparse

HERE = Path(__file__).resolve().parent
SOURCE_SHA = 'fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'
TRACE_SHA = '6f8c9aa889a62c577a8c988120a48393b32480a7750e2fd49a860c8727c00e1f'


def check(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def forbidden(*args, **kwargs):
    raise RuntimeError('Ordered/eager execution was called by the new evaluator')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=HERE)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    begin = time.perf_counter()
    raw = (HERE/'universal-source.json').read_bytes()
    check(sha256(raw).hexdigest() == SOURCE_SHA, 'Universal source hash mismatch')
    source_bytes = len(raw)
    data = json.loads(raw)
    del raw
    # Deliberately disable old execution and eager compilation before startup.
    sparse._metadata.LazySource.step = forbidden
    sparse._metadata.apply_gate = forbidden
    sparse._ref.compile_source = forbidden
    sparse._ref.Gate.apply = forbidden
    sparse._ref.Gate._apply = forbidden
    sparse._ref.CompiledSource.step = forbidden
    began_compile = time.perf_counter()
    a = sparse.SparseParallelCompiler(data)
    compile_seconds = time.perf_counter()-began_compile
    del data
    c = a.metadata
    check((c.m,c.p,c.a,c.J,c.factors) ==
          (122622,66066,75495,0,269291358255), 'Universal ledger mismatch')
    check(a.radius == 91711698, 'Universal new radius mismatch')
    x = a.encode('START',1,0)
    check(sorted(x) == [-20380381,0,1019018,1019019,20380380], 'Loader mismatch')
    reference_bytes = (HERE/'frozen-ordered-startup-trace.json').read_bytes()
    check(sha256(reference_bytes).hexdigest() == TRACE_SHA, 'Old reference trace hash mismatch')
    reference = json.loads(reference_bytes)
    trail = []
    began_steps = time.perf_counter()
    for step in range(128):
        y, trace = a.step(x, verify=True, trace=True)
        check(a.step(y,inverse=True,verify=True) == x, ('startup inverse',step))
        check(len(y) == 5, 'Startup mass changed')
        check(sorted(x) == reference[step]['input'] and
              sorted(y) == reference[step]['output'], ('valid-state old trace',step))
        if step < 3:
            target = ('h0000B0T1','p00001R0T1','p00001R0T2')[step]
            check(y == a.encode(target,1,0), ('direct startup',step))
        check(sum(t.prospective_queries for t in trace.blocks) <= len(x),
              'Prospective query bound exceeded')
        trail.append(dict(step=step,input=sorted(x),output=sorted(y),trace=asdict(trace)))
        x = y
    startup_seconds = time.perf_counter()-began_steps
    rng = random.Random(202610031229)
    malformed = []
    began_malformed = time.perf_counter()
    for trial in range(128):
        index = rng.randrange(c.factors)
        gate = a.gate_at(index)
        label = rng.randrange(2)
        shift = -(1<<2048) if trial == 0 else rng.randrange(-100000000,100000001)
        x = frozenset(shift+v for v in gate.shapes[label])
        for _ in range(rng.randrange(5)):
            x = x|{shift+rng.randrange(-2*c.Z,2*c.Z+1)}
        inverse = bool(trial%2)
        y, trace = a.step(x,inverse=inverse,verify=True,trace=True)
        check(a.step(y,inverse=not inverse,verify=True) == x, ('malformed inverse',trial))
        check(len(y) == len(x), 'Malformed mass changed')
        check(sum(t.prospective_queries for t in trace.blocks) <= len(x),
              'Prospective query bound exceeded')
        malformed.append(dict(trial=trial,seed_template=index,input=sorted(x),
                              output=sorted(y),trace=asdict(trace)))
    alltraces = [t for row in trail+malformed for t in row['trace']['blocks']]
    receipt = dict(status='passed',source_bytes=source_bytes,source_sha256=SOURCE_SHA,
                   valid_state_reference_trace_sha256=TRACE_SHA,
                   metadata_sha256=sparse.METADATA_SHA256,
                   evaluator_sha256=sha256((HERE/'sparse_parallel.py').read_bytes()).hexdigest(),
                   ledger=a.ledger(),old_execution_traps_installed=True,
                   compile_seconds=compile_seconds,startup_steps=len(trail),
                   startup_seconds=startup_seconds,malformed_cases=len(malformed),
                   malformed_seconds=time.perf_counter()-began_malformed,
                   max_candidate_types=max(t['candidate_types'] for t in alltraces),
                   max_raw_keys=max(t['raw_keys'] for t in alltraces),
                   max_selected_keys=max(len(t['selected']) for t in alltraces),
                   max_prospective_queries=max(t['prospective_queries'] for t in alltraces),
                   total_seconds=time.perf_counter()-begin,
                   peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    suffix = '' if __debug__ else '-optimized'
    (args.output_dir/f'universal-receipt{suffix}.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (args.output_dir/f'universal-startup-trace{suffix}.json').write_text(json.dumps(trail,indent=2)+'\n')
    (args.output_dir/f'universal-malformed-trace{suffix}.json').write_text(json.dumps(malformed,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
