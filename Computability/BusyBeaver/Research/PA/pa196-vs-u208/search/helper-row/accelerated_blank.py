#!/usr/bin/env python3
"""Reproduce the first failed helper-fold block in a blank-start execution."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(argv, timeout=180):
    return subprocess.run(argv, check=True, text=True, capture_output=True,
                          timeout=timeout).stdout


def parse(output):
    lines = output.splitlines()
    need(len(lines) == 2 and lines[1].startswith('ones_runs'), 'bad simulation output')
    words = lines[0].split()
    if words[0] in ('limit', 'direct'):
        data = {'kind': words[0], 'steps': int(words[1])}
        rest = words[2:]
    else:
        data = {'kind': words[0]}
        rest = words[1:]
    need(len(rest) % 2 == 0, 'bad output fields')
    data.update({rest[i]: int(rest[i+1]) for i in range(0, len(rest), 2)})
    runs = []
    for item in lines[1].split()[1:]:
        lo, hi = map(int, item.split(':'))
        need(lo <= hi and (not runs or lo > runs[-1][1]+1), 'bad tape run')
        runs.append((lo, hi))
    return data, runs


def digest_runs(runs):
    return hashlib.sha256(json.dumps(runs, separators=(',', ':')).encode()).hexdigest()


def decode(runs, origin):
    ones = set()
    for lo, hi in runs:
        ones.update(range(lo+origin, hi+origin+1))
    return ones


def advance(rows, ones, state, head, count, candidate):
    ones = set(ones)
    for _ in range(count):
        need(state != 196, 'early halt during splice')
        read = int(head in ones)
        write, direction, dest = rows[state, read]
        if candidate and (state, read) == (184, 1):
            write, direction, dest = 1, -1, 75
        if candidate and dest == 45:
            dest = 160
        ones.discard(head)
        if write:
            ones.add(head)
        head += direction
        state = dest
    return state, head, ones


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    witness = load('source_witness', HERE/'source_witness.py')
    need(hashlib.sha256(witness.TABLE.read_bytes()).hexdigest() == witness.TABLE_HASH,
         'literal table hash mismatch')
    # Also validate the independent two-resolver exact source execution and its
    # reconstructed physical-frame endpoints before splicing in the blank trace.
    source_result = run([sys.executable, '-B', str(HERE/'source_actual_witness.py')])
    need(source_result == (HERE/'source-actual-witness-receipt.json').read_text(),
         'source-frame witness changed')
    rows = {}
    for line in witness.TABLE.read_text().splitlines():
        q, b, w, d, n = line.split()
        rows[int(q), int(b)] = int(w), (1 if d == 'R' else -1), int(n)
    rotations = load('rotations', witness.SOURCE/'scan_rotations.py')
    paths = list(rotations.leaf_occurrences(rotations.root))
    initial_file = [75,0,1,0,0,0,4,0,0] + [1]*10570
    expected_604 = witness.frame(paths[604][0], initial_file, 10466)
    expected_at_31 = advance(rows, expected_604, 75, 0, 31, False)
    need(expected_at_31[:2] == (184, 27), 'site frame entry changed')
    with tempfile.TemporaryDirectory(prefix='pa196-accelerated-') as tmp:
        temp = Path(tmp)
        binaries = {}
        for name in ('accelerated_blank', 'accelerated_blank_control', 'blank_direct_control'):
            binary = temp/name
            run(['g++', '-O3', '-std=c++17', '-Wall', '-Wextra', '-Werror',
                 str(HERE/(name+'.cpp')), '-o', str(binary)])
            binaries[name] = str(binary)
        control = run([binaries['accelerated_blank_control']])
        need(control == 'control_trials 10000 forced 480 pass\n', 'sweep controls failed')
        sim = binaries['accelerated_blank']
        direct = binaries['blank_direct_control']
        table = str(witness.TABLE)
        prefix, prefix_runs = parse(run([sim, table, '100000000']))
        orig, orig_runs = parse(run([direct, table, '100000000', 'original']))
        child, child_runs = parse(run([direct, table, str(prefix['child']), 'child']))
        need(prefix['kind'] == 'limit' and prefix['steps'] == 100000000 and
             prefix['child'] == 100016084 and prefix['q'] == orig['q'] == child['q'] == 51 and
             prefix['h'] == orig['h'] == child['h'] == 12732 and
             prefix_runs == orig_runs == child_runs, '100m full-tape control failed')
        billion, billion_runs = parse(run([sim, table, '1000000000']))
        billion_direct, billion_direct_runs = parse(run([direct, table, '1000000000', 'original']))
        need(billion['kind'] == 'limit' and billion['steps'] == 1000000000 and
             billion['q'] == billion_direct['q'] == 35 and
             billion['h'] == billion_direct['h'] == 4870 and
             billion_runs == billion_direct_runs, '1b original full-tape control failed')
        failure, failure_runs = parse(run([sim, table, '100000000000']))
    need(failure == {'kind':'failure','parent':1223335721,'child':1223363605,
                     'state':184,'head':25,'read':1,'mask':6,'visits45':6971,
                     'visits160':4,'visits184':1,'sweepsteps':992816606},
         f'failure summary mismatch: {failure}')
    # Simulator tape is relative to head; source frame's head is at 27.
    failure_ones = decode(failure_runs, 27)
    need(failure_ones == expected_at_31[2] and len(failure_ones) == 21244,
         'accelerated tape differs from exact source-frame replay')
    parent_file = [74,0,1,0,0,0,4,0,0] + [1]*10570
    candidate_file = [75,0,1,0,0,0,4,0,1] + [1]*10571
    parent_end = advance(rows, failure_ones, 184, 27, 84142-31, False)
    child_end = advance(rows, failure_ones, 184, 27, 147964-31, True)
    need(parent_end == (75,0,witness.frame(paths[605][0],parent_file,10467)),
         'original endpoint splice failed')
    need(child_end == (75,0,witness.frame(paths[615][0],candidate_file,10466)),
         'candidate endpoint splice failed')
    out = {'table_sha256':witness.TABLE_HASH, 'randomized_sweep_trials':10000,
           'forced_word_boundary_sweep_trials':480,
           'prefix_100m':prefix, 'prefix_100m_runs_sha256':digest_runs(prefix_runs),
           'prefix_1b':billion, 'prefix_1b_runs_sha256':digest_runs(billion_runs),
           'independent_direct_parent_and_child_100m_full_tape_match':True,
           'independent_direct_parent_1b_full_tape_match':True,
           'first_failed_block':failure, 'failure_ones':len(failure_ones),
           'failure_runs_sha256':digest_runs(failure_runs),
           'failure_full_tape_equals_source_site_604_after_31_steps':True,
           'source_frame_root_head_absolute':-2,
           'original_blank_to_site_605_steps':failure['parent']+84142-31,
           'candidate_blank_to_site_615_steps':failure['child']+147964-31,
           'projected_matching_before_failure':True,
           'failed_block_step_bound':512,
           'represented_parent_step_bound':100000000000}
    data = json.dumps(out, indent=2, sort_keys=True)+'\n'
    print(data, end='')
    if args.output:
        args.output.write_text(data)


if __name__ == '__main__':
    main()
