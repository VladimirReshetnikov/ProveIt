#!/usr/bin/env python3
"""Offline reconstruction and fresh universal replay of the combined K222.

Python 3.10+ and the standard library suffice. The default pins and extracts the
parents, reconstructs the new all-natural numerical emitter, independently
checks its literal formulas, compiles the exact 222-state table, regenerates
and independently checks the 318-node logic certificate, and freshly proves
all 6,167 unbounded binary instruction cases plus exact blank startup.

Only four files are extracted from the nested K224 package. No default phase
reruns the entire ancestry. --replay-parents additionally runs the supplied
G223 quick replay and the supplied Seed223 default replay in separate output
directories. Neither mode builds a new Rocq/Lean endpoint or proves absolute
consistency. The inherited uniform mathematical calibrations are documented
in the report; finite instantiated certificates do not replace those proofs.

Every generated file goes to --output-dir, which must initially be empty and
outside this packet. Parent inputs and the delivered packet are never edited.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parent
PACKET = ROOT.parent
PARENT_NAME = 'K223_Construction_2026-10-20'
BASE_NAME = 'K224_Construction_2026-10-20'
ARCHIVES = {
    'G223_parent.zip': 'db9bfea47d5e97bb8d89641d4a027c5215398e8793864caaed6e81770dcdf39c',
    'Seed223_parent.zip': 'c20713d1cda1175ba9ef246e60bda5d193b5fe8fc431d9b9188c5f5b532c0f15',
}
BASE_SHA = 'cf5db8d08a34f5661ad1266226809ed1f0099fd38374c66d127e1e06519c6887'
BASE_FILES = {
    'portable/machine/results/sites.json':
        '309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878',
    'portable/machine/results/candidate224.k.tm':
        'f886dd8d11e9705c5315140f68d5ae2f26c80afb015e08074c7e3da1414fa37f',
    'portable/machine/reference/legacy_state_map.json':
        '8d77f4dcddc9966ba58b0cb8515d604334983e86b51580b546960b1e1d1a7151',
    'portable/vendor/K225_Construction_2026-10-19.zip':
        '75b58ce7b5840ef3a3158341f7cf1e601aab67d19ab147d96cf37d1186cb6cbc',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    result = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def write(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')


def relative(name):
    need(isinstance(name, str) and name and '\\' not in name
         and '\x00' not in name and ':' not in name, 'Unsafe path: ' + repr(name))
    value = PurePosixPath(name)
    need(not value.is_absolute()
         and all(part not in ('', '.', '..') for part in name.rstrip('/').split('/')),
         'Unsafe path: ' + name)
    return Path(*value.parts)


def manifest_check():
    manifest = read(ROOT / 'manifest.json')
    need(manifest.get('schema_version') == 1, 'Unknown portable manifest schema')
    expected, total = set(), 0
    for item in manifest['files']:
        name = item['path']
        need(name not in expected and name != 'manifest.json', 'Duplicate/self manifest entry')
        path = ROOT / relative(name)
        need(path.is_file() and not path.is_symlink() and ROOT in path.resolve().parents,
             'Missing, nonregular, or escaping manifest file: ' + name)
        for parent in path.parents:
            if parent == ROOT:
                break
            need(not parent.is_symlink(), 'Symlink in manifest path: ' + name)
        need(type(item['size']) is int and item['size'] >= 0,
             'Invalid manifest size: ' + name)
        need(path.stat().st_size == item['size'] and sha(path) == item['sha256'],
             'Manifest mismatch: ' + name)
        expected.add(name)
        total += item['size']
    actual = set()
    for path in ROOT.rglob('*'):
        need(not path.is_symlink(), 'Symlink in portable packet')
        if path.is_file() and path != ROOT / 'manifest.json':
            actual.add(path.relative_to(ROOT).as_posix())
    need(actual == expected, 'Portable manifest inventory differs')
    return {'status': 'EXACT_PORTABLE_MANIFEST_PASS', 'files': len(expected),
            'bytes': total, 'manifest_sha256': sha(ROOT / 'manifest.json')}


def extract(archive, destination, expected_sha, expected_root, selected=None):
    """Validate every ZIP name/type, then extract regular selected bytes once."""
    need(sha(archive) == expected_sha, 'Pinned archive differs: ' + str(archive))
    destination.mkdir()
    extracted, selected_seen = {}, set()
    with zipfile.ZipFile(archive) as packet:
        members = packet.infolist()
        seen = set()
        for item in members:
            rel = relative(item.filename)
            name = rel.as_posix()
            need(rel.parts[0] == expected_root, 'Unexpected archive root: ' + name)
            need(name not in seen, 'Duplicate ZIP member: ' + name)
            seen.add(name)
            kind = stat.S_IFMT((item.external_attr >> 16) & 0xffff)
            need(kind in (0, stat.S_IFREG, stat.S_IFDIR) and not item.flag_bits & 1,
                 'Nonregular or encrypted ZIP member: ' + name)
        for item in members:
            rel = relative(item.filename)
            if selected is not None:
                inner = Path(*rel.parts[1:]).as_posix()
                if inner not in selected or item.is_dir():
                    continue
                selected_seen.add(inner)
            target = destination / rel
            need(destination.resolve() in target.resolve().parents,
                 'Escaping ZIP target: ' + item.filename)
            if item.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with packet.open(item) as source, target.open('xb') as output:
                    shutil.copyfileobj(source, output)
                need(target.stat().st_size == item.file_size, 'Incomplete extracted ZIP member')
                extracted[rel.as_posix()] = sha(target)
        if selected is not None:
            need(selected_seen == set(selected), 'Requested nested files are missing')
            for name, pin in selected.items():
                need(sha(destination / expected_root / relative(name)) == pin,
                     'Nested input pin differs: ' + name)
    return {'status': 'PINNED_SAFE_EXTRACTION_PASS', 'archive_sha256': expected_sha,
            'archive_members_checked': len(members), 'files_extracted': len(extracted),
            'selected_files_only': selected is not None, 'file_hashes': extracted}


def snapshot(directory):
    result = {}
    for path in directory.rglob('*'):
        need(not path.is_symlink(), 'Symlink in extracted inputs')
        if path.is_file():
            result[path.relative_to(directory).as_posix()] = sha(path)
    return result


def compare(left, right, label):
    need(Path(left).read_bytes() == Path(right).read_bytes(),
         'Rebuilt bytes differ: ' + label)
    return {'sha256': sha(left), 'bytes': Path(left).stat().st_size}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--replay-parents', action='store_true',
                        help='Also run the supplied G223 quick and Seed223 default replays')
    args = parser.parse_args()
    need(sys.version_info >= (3, 10), 'Python 3.10+ is required')
    need(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),
         'Assertions must be enabled: omit -O/-OO and PYTHONOPTIMIZE')
    out = args.output_dir.resolve()
    need(out != PACKET and PACKET not in out.parents, 'Output must be outside the packet')
    need(not out.exists() or (out.is_dir() and not any(out.iterdir())),
         'Output directory must initially be empty')
    out.mkdir(parents=True, exist_ok=True)
    (out / 'logs').mkdir()
    (out / 'inputs').mkdir()
    (out / 'theory').mkdir()
    started = time.monotonic()
    result = {
        'schema_version': 1, 'status': 'IN_PROGRESS', 'phases': [],
        'python': sys.version, 'assertions_enabled': True,
        'fresh_final_runtime': True, 'additional_parent_replays': bool(args.replay_parents),
        'fresh_Rocq_or_Lean_build': False,
        'scope': {
            'source': 'Fresh exact numerical emitter, nine all-register macro contracts, '
                      'closed source rotation, and two complete guarded-CFG resolvers.',
            'formula_audit': 'Independent literal old/new ASTs and uniform native-decoder side conditions.',
            'compiler': 'Fresh exact 222-state table, every compound source-prefix binding, '
                        '49 unchanged instruction-engine states, and canonicalization.',
            'finite_logic': 'Fresh 318-node certificate and an independent proof-DAG replay. '
                            'The uniform parameterized proof is supplied separately in the report.',
            'runtime': 'Fresh induction for nine arbitrary natural registers, both decrement guards, '
                       'arbitrary natural gap and first spare, and arbitrary finite remaining spare list; '
                       'all 6167 cases and all 444 transition rows, plus exact blank startup.',
            'inherited_calibration': 'The seed calculus/ZFC equiconsistency, proof enumerator and '
                                    'upstream macro foundations remain the documented inherited '
                                    'mathematical dependencies. Default pins parents without replaying all ancestry.',
        },
    }
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env['PYTHONHASHSEED'] = '0'

    def save():
        result['seconds'] = time.monotonic() - started
        write(out / 'replay.json', result)

    def phase(name, action):
        print('[K222] ' + name, flush=True)
        entry = {'name': name, 'status': 'IN_PROGRESS'}
        result['phases'].append(entry)
        save()
        begun = time.monotonic()
        try:
            entry['result'] = action()
            entry['status'] = 'PASS'
            return entry['result']
        except Exception as error:
            entry.update(status='FAILED', error=repr(error))
            result['status'] = 'FAILED'
            raise
        finally:
            entry['seconds'] = time.monotonic() - begun
            save()

    def run(name, script, arguments, receipt=None, expected=None):
        log = out / 'logs' / (name + '.log')
        command = [sys.executable, '-B', str(script), *map(str, arguments)]
        with log.open('w', encoding='utf-8') as stream:
            completed = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT,
                                       cwd=out, env=env)
        need(completed.returncode == 0, 'Phase command failed; see ' + str(log))
        answer = {'returncode': completed.returncode, 'log': log.relative_to(out).as_posix()}
        if receipt is not None:
            data = read(receipt)
            if expected is not None:
                need(data.get('status') == expected, 'Unexpected receipt status: ' + str(receipt))
            answer.update(status=data.get('status'), receipt=receipt.relative_to(out).as_posix(),
                          receipt_sha256=sha(receipt))
        return answer

    try:
        phase('01_portable_manifest', manifest_check)
        phase('02_extract_G223', lambda: extract(
            ROOT / 'vendor/G223_parent.zip', out / 'inputs/G223',
            ARCHIVES['G223_parent.zip'], PARENT_NAME))
        phase('03_extract_Seed223', lambda: extract(
            ROOT / 'vendor/Seed223_parent.zip', out / 'inputs/Seed223',
            ARCHIVES['Seed223_parent.zip'], PARENT_NAME))
        g = out / 'inputs/G223' / PARENT_NAME
        seed = out / 'inputs/Seed223' / PARENT_NAME
        phase('04_extract_four_K224_inputs', lambda: extract(
            seed / 'portable/vendor' / (BASE_NAME + '.zip'), out / 'inputs/K224_minimal',
            BASE_SHA, BASE_NAME, BASE_FILES))
        base = out / 'inputs/K224_minimal' / BASE_NAME
        input_snapshot = snapshot(out / 'inputs')
        source = out / 'source'
        phase('05_rebuild_source_and_exact_emitter', lambda: run(
            'source', ROOT / 'verification/build_combined_source.py',
            ['--seed-root', seed, '--baseline224', base, '--output', source],
            source / 'source_emitter_receipt.json', 'EXACT_COMBINED_SOURCE_AND_ALL_NATURAL_EMITTER_PASS'))
        phase('06_independent_formulas_and_native_decoding', lambda: run(
            'literal_formulas', ROOT / 'theory/audit_composed_formula.py',
            [source / 'source_emitter_receipt.json', source / 'sites.json',
             out / 'theory/native_composition_audit.json'],
            out / 'theory/native_composition_audit.json',
            'INDEPENDENT_LITERAL_FORMULAS_AND_UNIFORM_DECODER_PASS'))
        built = out / 'machine'
        phase('07_compile_222', lambda: run(
            'compiler', ROOT / 'verification/construct222.py',
            ['--parent-table', g / 'portable/results/candidate223.k.tm',
             '--parent-sites', g / 'portable/results/sites.json',
             '--sites', source / 'sites.json', '--output', built],
            built / 'construction222.json', 'DETERMINISTIC_222_CONSTRUCTION_PASS'))

        def compare_construction():
            checks = {}
            for name in ('candidate222.tm', 'candidate222.k.tm', 'sites222.json',
                         'construction222.json', 'canonical_map.json',
                         'binary_delta222.json', 'decoder222.json'):
                checks[name] = compare(built / name, ROOT / 'machine' / name, name)
            for name in ('source_emitter_receipt.json', 'reference_sites.json'):
                checks[name] = compare(source / name, ROOT / 'machine' / name, name)
            return {'status': 'ALL_FROZEN_CONSTRUCTION_BYTES_IDENTICAL', 'files': checks}

        phase('08_frozen_construction_identity', compare_construction)
        proof = out / 'theory/seed_g_proofs.json'
        phase('09_regenerate_seed_G_logic_certificate', lambda: run(
            'logic_generator', ROOT / 'theory/compose_seed_certificate.py',
            [g / 'portable/theory/merged_euclidean_helper_proofs.json', proof]))
        phase('10_independent_finite_logic', lambda: run(
            'logic_checker', ROOT / 'theory/review_logic.py',
            [proof, '--output', out / 'theory/seed_g_proofs_review.json'],
            out / 'theory/seed_g_proofs_review.json', 'INDEPENDENT_FINITE_DAG_REPLAY_PASS'))

        def compare_logic():
            checked = read(out / 'theory/seed_g_proofs_review.json')
            need((checked['nodes'], checked['formulas'], checked['root_count']) == (318, 293, 36),
                 'Logic certificate census differs')
            return {'status': 'ALL_FROZEN_LOGIC_BYTES_IDENTICAL',
                    'proof': compare(proof, ROOT / 'theory/seed_g_proofs.json', 'logic proof'),
                    'review': compare(out / 'theory/seed_g_proofs_review.json',
                                      ROOT / 'theory/seed_g_proofs_review.json', 'logic review')}

        phase('11_frozen_logic_identity', compare_logic)
        runtime = out / 'runtime'
        phase('12_fresh_unbounded_runtime_6167_cases', lambda: run(
            'runtime', ROOT / 'verification/verify_candidate.py',
            ['--table', built / 'candidate222.k.tm', '--sites', source / 'sites.json',
             '--legacy-map', g / 'portable/vendor/legacy_state_map.json',
             '--engine-dir', g / 'portable/runtime', '--output', runtime],
            runtime / 'verification.json', 'UNIVERSAL_MATHEMATICAL_PASS'))

        def compare_runtime():
            fresh = read(runtime / 'verification.json')
            need(fresh['working_states'] == 222 and fresh['rows'] == 444
                 and fresh['cases'] == 6167 and fresh['all_rows_used'], 'Runtime coverage differs')
            need(fresh['startup']['steps'] == 409835
                 and fresh['startup']['status'] == 'EXACT_COMPLETE_BLANK_STARTUP_PASS',
                 'Blank startup receipt differs')
            frozen = read(ROOT / 'machine/runtime222.json')
            need({k: v for k, v in fresh.items() if k != 'seconds'} ==
                 {k: v for k, v in frozen.items() if k != 'seconds'},
                 'Fresh runtime semantic receipt differs from frozen receipt')
            return {'status': 'ALL_FRESH_RUNTIME_SUMMARIES_IDENTICAL',
                    'cases': compare(runtime / 'runtime_cases.json', ROOT / 'machine/runtime_cases.json',
                                     '6167 fresh symbolic cases'),
                    'canonical': compare(runtime / 'candidate222.tm', built / 'candidate222.tm',
                                         'independently canonicalized table'),
                    'symbolic_steps': fresh['symbolic_steps'], 'minimum_actual_steps': fresh['minimum_actual_steps'],
                    'blank_startup_steps': 409835, 'all_444_rows_used': True}

        phase('13_fresh_runtime_identity', compare_runtime)
        if args.replay_parents:
            greplay = out / 'G223_replay'
            phase('14_optional_G223_quick_replay', lambda: run(
                'parent_G223', g / 'portable/reproduce.py', ['--output-dir', greplay],
                greplay / 'replay.json', 'QUICK_REPLAY_PASS'))
            sreplay = out / 'Seed223_replay'
            phase('15_optional_Seed223_default_replay', lambda: run(
                'parent_Seed223', seed / 'portable/reproduce.py', ['--output-dir', sreplay],
                sreplay / 'replay.json', 'FULL_K223_REPLAY_PASS'))

        def input_integrity():
            need(snapshot(out / 'inputs') == input_snapshot, 'Extracted parent inputs changed during replay')
            return {'status': 'ALL_EXTRACTED_INPUT_BYTES_UNCHANGED', 'files': len(input_snapshot)}

        phase('16_extracted_input_integrity', input_integrity)
        phase('17_final_portable_manifest', manifest_check)
        result.update(
            status='FULL_K222_REPLAY_PASS', working_states=222, transition_rows=444,
            guarded_runtime_cases=6167, blank_startup_steps=409835,
            source_metrics=read(source / 'source_emitter_receipt.json')['source_metrics'],
            hashes={'canonical_table_sha256': sha(built / 'candidate222.tm'),
                    'k_table_sha256': sha(built / 'candidate222.k.tm'),
                    'source_sha256': sha(source / 'sites.json'),
                    'logic_proof_sha256': sha(proof),
                    'fresh_runtime_cases_sha256': sha(runtime / 'runtime_cases.json'),
                    'parent_archives': ARCHIVES},
            proof_status='Executable ordinary mathematical construction, finite derivations and '
                         'unbounded induction, with the inherited uniform ZFC calibration documented '
                         'in the report. No newly compiled proof-assistant endpoint.')
        save()
        print(result['status'], flush=True)
        return 0
    except Exception as error:
        result.update(status='FAILED', error=repr(error))
        save()
        print('K222 replay failed: ' + repr(error), file=sys.stderr, flush=True)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
