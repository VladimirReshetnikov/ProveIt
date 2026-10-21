#!/usr/bin/env python3
"""Audit packaged bytes, recorded proof evidence, and small finite checks.

This is NOT a fresh Lean/Coq kernel check, an authentication of historical
execution, a complete K215 endpoint rebuild, or a replay of the state searches.
The manifest excludes only itself; its files mapping uses SHA-256 and byte size.
No compiler, network access, third-party package, or package-local write is used.
"""
from pathlib import Path, PurePosixPath
import argparse
import collections
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
PIN = 'aa66d0a33f1f8237a348899eb8095b045a502832'
SCHEMA = 'k215-proof-refinements-manifest-v1'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


def member(base, name):
    path = PurePosixPath(name)
    need(bool(name) and not path.is_absolute() and '..' not in path.parts
         and str(path) == name and '\\' not in name, 'Unsafe relative path: ' + name)
    return base.joinpath(*path.parts)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check_hash(path, expected):
    need(isinstance(expected, str) and re.fullmatch('[0-9a-f]{64}', expected),
         'Malformed SHA-256 for ' + str(path))
    data = path.read_bytes()
    need(digest(data) == expected, 'SHA-256 mismatch: ' + str(path))
    return data


def manifest():
    data = read_json(ROOT / 'MANIFEST.json')
    need(data['schema'] == SCHEMA, 'Unexpected manifest schema')
    files = data['files']
    need(isinstance(files, dict) and 'MANIFEST.json' not in files,
         'Manifest must map every delivered file except itself')
    actual = set()
    for path in ROOT.rglob('*'):
        need(not path.is_symlink(), 'Individual symlinks are not allowed: ' + str(path))
        if path.is_file() and path != ROOT / 'MANIFEST.json':
            actual.add(path.relative_to(ROOT).as_posix())
    need(actual == set(files), 'Manifest inventory mismatch; missing=' +
         str(sorted(set(files) - actual)) + '; unlisted=' + str(sorted(actual - set(files))))
    for name, row in files.items():
        content = check_hash(member(ROOT, name), row['sha256'])
        need(type(row['bytes']) is int and len(content) == row['bytes'],
             'Byte-size mismatch: ' + name)
    print('PASS manifest: %d delivered files, exact hashes and sizes' % len(files))


def balanced():
    base = ROOT / 'balanced_normalized'
    receipt = read_json(base / 'verification/result.json')
    need(receipt['schema'] == 'balanced-normalized-k215-v1' and
         receipt['fresh'] is True and receipt['complete'] is True and
         receipt['compatibility_import'] is True, 'Unexpected balanced build status')
    need('version 8.18.0' in receipt['toolchain'], 'Unexpected recorded Coq version')
    check_hash(base / 'build.py', receipt['driver_sha256'])
    sources = {row['module']: row for row in receipt['sources']}
    need(len(sources) == len(receipt['sources']) == 17, 'Expected 17 balanced sources')
    for name, row in sources.items():
        actual = {'deps/K230/RMEquiv.v': 'deps/K230/RMEquiv.rocq91.v',
                  'deps/K215F/Source215.v': 'Source215.v'}.get(name, name)
        content = check_hash(member(base, actual), row['delivered_sha256'])
        if name == 'deps/K230/RMEquiv.v':
            needle = b'From K230 Require Import RM.'
            need(content.count(needle) == 1, 'Ambiguous RMEquiv compatibility import')
            content = content.replace(needle, needle + b'\nRequire Import Compat818.')
        need(digest(content) == row['compiled_sha256'], 'Compiled-source mismatch: ' + name)
    checks = receipt['checks']
    need(len(checks) == 17 and {row['name'] for row in checks} == set(sources),
         'Balanced compilation inventory mismatch')
    expected_closed = {'BalancedNormalized.v': 2, 'NormalizedTree215.v': 3,
                       'Source215Composed.v': 2, 'deps/K215F/Source215.v': 1,
                       'EndpointClient.v': 1}
    for row in checks:
        name = row['name']
        need(row['exit_code'] == 0 and row['argv'][-1] == name,
             'Unsuccessful/wrong balanced compilation: ' + name)
        log = check_hash(base / 'verification/logs' / (name.replace('/', '_') + '.log'),
                         row['log_sha256']).decode()
        need(log.count('Closed under the global context') == row['closed_reports'],
             'Balanced assumption count mismatch: ' + name)
        need('Error:' not in log and 'Axioms:' not in log, 'Unexpected balanced diagnostic')
        if name in expected_closed:
            need(row['closed_reports'] == expected_closed[name], 'Missing closed theorem report')
    audit = read_json(base / 'verification/recursive-audit.json')
    need(audit['exit_code'] == 0 and audit['argv'][-1] == 'EndpointClient'
         and '-silent' in audit['argv'] and 'coqchk' in Path(audit['argv'][0]).name,
         'Missing successful recursive concrete-client record')
    check_hash(base / 'verification/logs/recursive_EndpointClient.log', audit['log_sha256'])
    binding = read_json(base / 'current-binding.json')
    need(binding['commit'] == PIN and len(binding['checks']) == 4, 'Source binding pin mismatch')
    for row in binding['checks']:
        name = row['file']
        where = ('deps/K215F/' if name in ('Prog215.v', 'DagPerm.v') else 'upstream/') + name
        check_hash(member(base, where), row['sha256'])
    print('PASS balanced evidence: 17 source/log bindings, 9 new closed reports, recursive client receipt')


def decoder():
    base = ROOT / 'decoder_context'
    receipt = read_json(base / 'verification/fresh-build.json')
    need(receipt['status'] == 'PASS_FRESH_KERNEL' and 'version 4.32.0' in receipt['toolchain'],
         'Unexpected decoder receipt status/toolchain')
    expected = {'FramedWindow', 'DecoderCertificate', 'K215Decoder',
                'DecoderContext', 'K215Context', 'Audit'}
    need(len(receipt['modules']) == 6 and {r['name'] for r in receipt['modules']} == expected,
         'Decoder module inventory mismatch')
    need(set(receipt['all_sources_sha256']) == {n + '.lean' for n in expected},
         'Decoder source inventory mismatch')
    for row in receipt['modules']:
        name = row['name']
        need(row['returncode'] == 0 and row['warnings'] == 0, 'Failed/warning decoder record')
        check_hash(base / (name + '.lean'), row['source_sha256'])
        need(receipt['all_sources_sha256'][name + '.lean'] == row['source_sha256'],
             'Conflicting decoder source hashes')
        log = check_hash(base / 'verification' / (name + '.log'), row['log_sha256']).decode()
        reports = [line for line in log.splitlines() if 'axiom' in line]
        need(reports == row['axiom_reports'], 'Decoder assumption report mismatch: ' + name)
        need(not re.search(r'(?i)\b(?:warning|error):|sorryAx', log), 'Unexpected decoder diagnostic')
        for report in reports:
            if 'depends on axioms:' in report:
                names = report.split('[', 1)[1].split(']', 1)[0].split(', ')
                need(set(names) <= {'propext', 'Classical.choice', 'Quot.sound'},
                     'Unexpected Lean axiom: ' + report)
    audit_log = (base / 'verification/Audit.log').read_text()
    for name in ('missing_predecessor', 'wrong_predecessor', 'wrong_next_suffix',
                 'missing_target_role', 'primitive_as_source_parent'):
        need('rejects_' + name in audit_log, 'Missing malformed-control theorem report')
    inherited = read_json(base / 'verification/inheritance.json')
    need(inherited['repository_commit'] == PIN, 'Decoder inheritance pin mismatch')
    for name, sha in inherited['unchanged_inherited_sources'].items():
        check_hash(member(base, name), sha)
    print('PASS decoder evidence: six current source/log bindings and five malformed-control reports')


def selector_receipt(directory, expected_sources):
    base = ROOT / 'early_halt'
    receipt = read_json(base / directory / 'receipt.json')
    need(receipt['status'] == 'PASS_COMPILED_AND_KERNEL_RECHECKED', 'Selector receipt is not success')
    need(len(receipt['source_hashes']) == expected_sources, 'Selector source count mismatch')
    for name, sha in receipt['source_hashes'].items():
        check_hash(member(base, ('upstream/' if '/' in name else '') + name), sha)
    compiled = []
    recursive = 0
    for row in receipt['actions']:
        command = row['command']
        need(row['returncode'] == 0, 'Unsuccessful selector action in final receipt')
        log = check_hash(member(base / directory, row['log']), row['log_sha256']).decode()
        need('Error:' not in log and 'Axioms:' not in log, 'Unexpected selector diagnostic')
        if command[-1].endswith('.v'):
            compiled.append(command[-1])
            if '/' not in command[-1]:
                need(log.count('Closed under the global context') == 2,
                     'Missing selector closed-assumption reports')
        if 'coqchk' in Path(command[0]).name:
            recursive += 1
            need('-silent' in command, 'Unexpected selector recursive-check command')
            need(command[-1] == ('K215SelectorAdapter' if expected_sources == 11 else 'NativeSelection'),
                 'Wrong selector recursive-check target')
    need(len(compiled) == expected_sources and set(compiled) == set(receipt['source_hashes'])
         and recursive == 1, 'Selector compilation/recursive-check inventory mismatch')


def selectors():
    base = ROOT / 'early_halt'
    selector_receipt('verification', 2)
    selector_receipt('production-verification-final', 11)
    for row in read_json(base / 'upstream/provenance.json'):
        path = member(base, row['path'])
        if 'original_sha256' not in row:
            check_hash(path, row['sha256'])
            continue
        need(row['source_commit'] == PIN, 'Selector production source pin mismatch')
        original = check_hash(base / 'upstream/original-production' / path.name, row['original_sha256'])
        blob = b'blob ' + str(len(original)).encode() + b'\0' + original
        need(hashlib.sha1(blob).hexdigest() == row['git_blob_sha1'], 'Git blob mismatch: ' + path.name)
        compiled = check_hash(path, row['compiled_sha256'])
        transformed = original.replace(b'From Stdlib Require Import', b'From Coq Require Import')
        need(compiled == (original if row['compatibility_change'] == 'none' else transformed),
             'Unrecorded production compatibility change: ' + path.name)
    history = read_json(base / 'production-verification/receipt.json')
    need(history['status'] == 'FAIL' and any(r['returncode'] != 0 for r in history['actions']),
         'Historical failed attempt was relabelled as success')
    for row in history['actions']:
        check_hash(member(base / 'production-verification', row['log']), row['log_sha256'])
    print('PASS selector evidence: generic and 11-module production successes; failed attempt retained as history')


def searches():
    base = ROOT / 'search214'
    provenance = read_json(base / 'PROVENANCE.json')
    need(provenance['pin'] == PIN, 'Search provenance pin mismatch')
    for name, row in provenance['files'].items():
        check_hash(member(base, name), row['sha256'])
    cases = [('r41-fold-depth4', 'r41.native.tm', 4, 45, 200, 71380),
             ('r41-fold-depth8', 'r41.native.tm', 8, 97, 1000, 99760),
             ('shallow-fold-depth8', 'shallow.native.tm', 8, 97, 1000, 108360),
             ('gczc-fold-depth8', 'gc-zc.canonical.tm', 8, 97, 1000, 97180)]
    for label, table, depth, steps, nodes, count in cases:
        row = read_json(base / 'results' / (label + '.json'))
        need(row['status'] == 'BOUNDED_SEARCH_NO_SURVIVOR' and row['survivors'] == [],
             'Unexpected one-row search result')
        observed = (row['backward_context_depth'], row['maximum_literal_steps_per_block'],
                    row['maximum_symbolic_nodes_per_block'], row['specifications'])
        need(observed == (depth, steps, nodes, count) and row['working_states'] == 215,
             'One-row bounds/count mismatch: ' + label)
        need(count == len(row['eligible_pairs']) * 2 * 2 * 215, 'One-row specification arithmetic mismatch')
        check_hash(base / 'inputs' / table, row['table_sha256'])
        check_hash(base / 'code/context_search.py', row['script_sha256'])
    row = read_json(base / 'results/r41-blank-result.json')
    need(row['status'] == 'COMPLETE_BOUNDED_SEARCH' and row['hits'] == []
         and row['pending'] is None and row['stop'] is None, 'Incomplete/unexpected blank-window receipt')
    expected = {'attempted': 632584, 'completed_pairs': 46010, 'filter_rejected': 632584,
                'independent_incomplete': 0, 'independent_pass': 0, 'independent_rejected': 0,
                'inherited': 182992, 'one_common_action': 449592, 'started_pairs': 46010,
                'total_ordered_pairs': 46010}
    need(row['stats'] == expected and 215 * 214 == expected['total_ordered_pairs'],
         'Blank-window census mismatch')
    need(row['bounds'] == {'external_seconds': 120, 'fuel': 97, 'radius': 7, 'soft_seconds': 110}
         and row['seconds'] < 110 and row['domain_contexts'] == 967293, 'Blank-window bounds mismatch')
    need(row['inputs'] == read_json(base / 'results/r41-blank-inputs.json'), 'Blank search input receipts differ')
    by_origin = {r['source']: r['sha256'] for r in provenance['files'].values()}
    need(all(by_origin.get(name) == sha for name, sha in row['inputs'].items()),
         'Blank search inputs not bound to delivered provenance')
    rejection = base / 'results/r41-blank-rejections.jsonl.gz'
    check_hash(rejection, row['rejections_sha256'])
    counts, pairs = collections.Counter(), set()
    with gzip.open(rejection, 'rt') as stream:
        for index, line in enumerate(stream, 1):
            item = json.loads(line)
            need(item['id'] == index and item['stage'] == 'bounded_filter', 'Unexpected rejection record')
            counts[item['family']] += 1
            pairs.add((item['keep'], item['drop']))
    need(counts == {'inherited': 182992, 'one_common_action': 449592} and len(pairs) == 46010,
         'Compressed rejection census mismatch')
    print('PASS search records: five bounded runs, input/code hashes, and 632584 stored rejections; searches not rerun')


def finite_checks(temp_parent):
    env = os.environ.copy()
    env.pop('PYTHONOPTIMIZE', None)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    def run(script, arguments, work):
        result = subprocess.run([sys.executable, '-I', '-B', str(ROOT / script), *arguments],
                                cwd=work, env=env, text=True, capture_output=True, timeout=60)
        need(result.returncode == 0, 'Finite check failed: ' + script + '\n' + result.stderr)
        return json.loads(result.stdout, object_pairs_hook=unique_object)
    with tempfile.TemporaryDirectory(prefix='k215-packet-audit-', dir=temp_parent) as folder:
        work = Path(folder)
        measured = run('balanced_normalized/metrics.py', [], work)
        need(measured == read_json(ROOT / 'balanced_normalized/metrics.json'), 'Lookup metrics differ')
        out = work / 'context-audit.json'
        measured = run('decoder_context/audit_context.py', ['--out', str(out)], work)
        need(measured == read_json(out) == read_json(ROOT / 'decoder_context/verification/context-audit.json'),
             'Decoder finite context audit differs')
        measured = run('early_halt/check_numeric.py', [], work)
        need(measured == read_json(ROOT / 'early_halt/numeric-receipt.json'), 'Numeric selector cases differ')
    print('PASS fresh finite checks: lookup metrics, decoder contexts, 11502 numeric selector cases')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--temp-dir', type=Path, help='Parent for temporary finite-audit output; defaults to /dev/shm when available')
    args = parser.parse_args()
    temp_parent = args.temp_dir
    if temp_parent is None and Path('/dev/shm').is_dir() and os.access('/dev/shm', os.W_OK):
        temp_parent = Path('/dev/shm')
    print('Recorded-evidence audit and finite corroboration only; no fresh kernel check or state-search replay.')
    manifest()
    balanced()
    decoder()
    selectors()
    searches()
    finite_checks(temp_parent)
    print('PASS_PACKET_RECORDED_EVIDENCE_AND_FINITE_CHECKS')
    print('Historical/prototype logs are not success evidence. Omitted compiler objects/toolchains are not rehashed.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.SubprocessError) as error:
        print('FAIL_PACKET_AUDIT: ' + str(error), file=sys.stderr)
        sys.exit(1)
