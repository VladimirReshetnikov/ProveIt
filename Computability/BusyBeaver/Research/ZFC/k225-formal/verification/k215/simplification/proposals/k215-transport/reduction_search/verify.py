#!/usr/bin/env python3
"""Audit pinned inputs, exercise positive/negative controls, optionally rerun searches.

No search failure in this package is a minimum-state theorem. The C++ program
is a finite discovery filter. Positive controls are independently checked with
the unchanged ProveIt universal common-endpoint checker.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import itertools
import json
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_table(path):
    start, table = None, {}
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line[9:])
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            need((int(q), int(b)) not in table, 'duplicate row')
            table[int(q), int(b)] = (int(w), 1 if d == 'R' else -1, int(z))
    states = {q for q, b in table}
    need(set(table) == {(q, b) for q in states for b in (0, 1)}, 'not total')
    need(start in states, 'missing start')
    need({z for w, d, z in table.values()} - states == {254}, 'halt convention')
    return table, start


def count_specifications(table):
    """Independent combinatorial count; no Turing-machine execution."""
    states = {q for q, b in table}
    inherited, free = 0, 0
    for keep, drop in itertools.permutations(states, 2):
        action_counts = []
        for bit in (0, 1):
            mapped = {(w, d, keep if z == drop else z)
                      for w, d, z in (table[keep, bit], table[drop, bit])}
            action_counts.append(len(mapped))
        inherited += action_counts[0] * action_counts[1]
        if (action_counts[0] == 1) != (action_counts[1] == 1):
            # Working states remaining plus the halt: still len(states) targets.
            free += 4 * len(states) - 2
    return inherited, free


def audit_inputs_and_records():
    manifest = json.loads((ROOT / 'inputs.json').read_text())
    need(manifest['commit'] == 'b6c7087477e51c017003bd729e712c8969733223',
         'unexpected repository pin')
    need(len(manifest['tables']) == 14, 'table inventory size')
    total = 0
    records = {}
    for item in manifest['tables']:
        path = ROOT / item['path']
        need(digest(path) == item['sha256'], 'table digest: ' + item['name'])
        table, start = load_table(path)
        need(len(table) == 430, 'not 215 states')
        inherited, free = count_specifications(table)
        for domain in ('all', 'blank'):
            key = item['name'] + '_' + domain
            report = json.loads((ROOT / 'results' / (key + '.json')).read_text())
            need(report['status'] == 'COMPLETE_BOUNDED_SEARCH', key)
            need(report['mode'] == 'inherited_or_one_common_action', key)
            need(report['initial_domain'] == ('all_tapes' if domain == 'all'
                                             else 'blank_window'), key)
            need((report['states'], report['radius'], report['fuel'],
                  report['ordered_pairs']) == (215, 7, 97, 46010), key)
            need(report['inherited_attempts'] == inherited, key)
            need(report['one_common_action_attempts'] == free, key)
            need(report['attempts'] == inherited + free, key)
            need(report['filter_survivors'] == 0, key)
            need(report['filter_rejected'] == report['attempts'], key)
            need(sum(report['reasons'].values()) == report['attempts'], key)
            total += report['attempts']
            records[key] = report
    for name in ('primary', 'marker'):
        for domain in ('all', 'blank'):
            key = name + '_' + domain + '_independent'
            report = json.loads((ROOT / 'results' / (key + '.json')).read_text())
            need(report['status'] == 'COMPLETE_BOUNDED_SEARCH', key)
            need(report['mode'] == 'independent_branches', key)
            need(report['initial_domain'] == ('all_tapes' if domain == 'all'
                                             else 'blank_window'), key)
            need(report['ordered_pairs'] == 46010, key)
            need(report['branch_attempts'] > 39_000_000, key)
            need(report['attempts'] == report['filter_survivors'] == 0, key)
            records[key] = report
    return manifest, records, total


def compile_cpp(work):
    compiler = shutil.which('g++') or shutil.which('c++')
    need(compiler is not None, 'C++17 compiler not found')
    binary = work / 'fold_search'
    completed = subprocess.run([compiler, '-std=c++17', '-O3', '-Wall',
                                '-Wextra', '-pedantic', str(ROOT / 'fold_search.cpp'),
                                '-o', str(binary)], capture_output=True, text=True)
    (work / 'build.log').write_text(completed.stdout + completed.stderr)
    need(completed.returncode == 0, 'C++ compilation failed; see build.log')
    return binary


def run_controls(work, binary):
    spec = importlib.util.spec_from_file_location(
        'independent_checker', ROOT / 'reference' / 'check_joint_fold.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    result = []
    for name in ('mergeable', 'incompatible'):
        original_path = ROOT / 'controls' / (name + '.tm')
        old, old_start = checker.read(original_path)
        for mode in ('inherited', 'independent'):
            prefix = work / (name + '_' + mode)
            proc = subprocess.run([str(binary), str(original_path), str(prefix),
                                   '3', '17', mode, 'all'],
                                  capture_output=True, text=True, check=True)
            prefix.with_suffix('.log').write_text(proc.stdout + proc.stderr)
            hits = [json.loads(line) for line in
                    prefix.with_suffix('.hits.jsonl').read_text().splitlines()]
            pair_hits = [h for h in hits if {h['keep'], h['drop']} == {1, 2}]
            need(bool(pair_hits) == (name == 'mergeable'), 'control fold outcome')
            # Independently rederive every surviving full-table diagram.
            for hit in hits:
                path = Path(str(prefix) + '.survivor-' + str(hit['id']) + '.tm')
                new, new_start = checker.read(path)
                proof = checker.check(old, new, old_start, new_start,
                                      hit['keep'], hit['drop'], 3, 17)
                need(proof['status'] == 'INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS',
                     'independent control failure')
            result.append({'control': name, 'mode': mode, 'survivors': len(hits),
                           'expected_pair_survivors': len(pair_hits),
                           'all_survivors_independently_checked': True})
    return result


def replay(work, binary, manifest, records, choice, selected, domain_choice):
    results = []
    for item in manifest['tables']:
        if selected and item['name'] not in selected:
            continue
        for domain in ('all', 'blank'):
            if domain_choice != 'both' and domain_choice != domain:
                continue
            modes = ['inherited']
            if choice == 'full' and item['name'] in ('primary', 'marker'):
                modes.append('independent')
            for mode in modes:
                key = item['name'] + '_' + domain
                if mode == 'independent':
                    key += '_independent'
                prefix = work / key
                proc = subprocess.run([str(binary), str(ROOT / item['path']),
                                       str(prefix), '7', '97', mode, domain],
                                      capture_output=True, text=True, check=True)
                prefix.with_suffix('.log').write_text(proc.stdout + proc.stderr)
                actual = json.loads(prefix.with_suffix('.json').read_text())
                expected = records[key]
                scientific = lambda r: {k: v for k, v in r.items() if k != 'seconds'}
                need(scientific(actual) == scientific(expected),
                     'replay differs: ' + key)
                results.append({'record': key, 'seconds': actual['seconds'],
                                'exact_nontiming_record_match': True})
    return results


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--replay', choices=('none', 'inherited', 'full'), default='none')
    ap.add_argument('--name', action='append', help='optional named input filter')
    ap.add_argument('--domain', choices=('all', 'blank', 'both'), default='both')
    ap.add_argument('--work', type=Path, help='fresh output directory')
    args = ap.parse_args()
    manifest, records, total = audit_inputs_and_records()
    if args.work:
        args.work.mkdir(parents=True, exist_ok=False)
        work = args.work.resolve()
        temporary = None
    else:
        temporary = tempfile.TemporaryDirectory(prefix='k215-fold-audit-')
        work = Path(temporary.name)
    try:
        binary = compile_cpp(work)
        controls = run_controls(work, binary)
        replays = [] if args.replay == 'none' else replay(
            work, binary, manifest, records, args.replay, set(args.name or []), args.domain)
        result = {'status': 'AUDIT_AND_CONTROLS_PASS', 'pinned_tables': 14,
                  'inherited_search_records': 28, 'inherited_specification_evaluations': total,
                  'independent_branch_search_records': 4,
                  'source_sha256': digest(ROOT / 'fold_search.cpp'),
                  'checker_sha256': digest(ROOT / 'reference' / 'check_joint_fold.py'),
                  'controls': controls, 'fresh_replays': replays,
                  'scope': 'Default audits stored negative-search receipts and freshly checks controls. '
                           'Only entries in fresh_replays were newly searched. No lower bound is claimed.'}
        (work / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result, indent=2))
    finally:
        if temporary is not None:
            temporary.cleanup()


if __name__ == '__main__':
    main()
