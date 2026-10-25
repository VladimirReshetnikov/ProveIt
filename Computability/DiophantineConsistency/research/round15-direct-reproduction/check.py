#!/usr/bin/env python3
"""Scoped stdlib Round15 reproduction in private exact-archive trees."""
import argparse
from hashlib import sha256
import io
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = HERE.parents[3]
COMMIT = '5f3379063df18910a981d2e6cae6aee91b79cf4d'
ARCHIVE_PATH = 'docs/incoming/ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24.zip'
ARCHIVE_SHA256 = '1be83b372f888f8349b2f231978541bc872f4b5e4be9b4a3429a3d5b7016f3b2'
PREFIX = 'ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24/'


def need(ok, label):
    if not ok:
        raise ValueError(label)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def snapshot(directory):
    return {str(p.relative_to(directory)): digest(p) for p in sorted(directory.rglob('*')) if p.is_file()}


def record(path, data):
    if path.exists():
        need(path.read_bytes() == data, 'refuse changed output overwrite ' + str(path))
    else:
        path.write_bytes(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    blob = subprocess.run(['git', 'show', COMMIT + ':' + ARCHIVE_PATH], cwd=REPO,
                          check=True, stdout=subprocess.PIPE).stdout
    need(sha256(blob).hexdigest() == ARCHIVE_SHA256, 'exact original ZIP Git blob')
    commands = {}
    flags = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONPATH='')
    logs = {}
    with tempfile.TemporaryDirectory(prefix='round15-direct-private-') as temporary:
        scratch = Path(temporary)
        private = scratch / 'original'
        private.mkdir()
        with zipfile.ZipFile(io.BytesIO(blob)) as archive:
            names = []
            for item in archive.infolist():
                if item.is_dir():
                    continue
                need(item.filename.startswith(PREFIX), 'original ZIP prefix')
                relative = PurePosixPath(item.filename[len(PREFIX):])
                need(relative.parts and not relative.is_absolute() and '..' not in relative.parts,
                     'literal ZIP member path')
                name = str(relative)
                need(name not in names, 'duplicate ZIP member')
                names.append(name)
                target = private.joinpath(*relative.parts)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(archive.read(item))
        before = snapshot(private)
        need(len(before) == len(names) == 569, 'all569 original ZIP members')
        direct_pins = load(private / 'direct/SOURCE_AND_ARTIFACT_PINS.json')
        for name, pin in direct_pins.items():
            need(digest(private / name) == pin['sha256'] and (private / name).stat().st_size == pin['bytes'],
                 'whole direct source/artifact pin ' + name)
        mandatory_seed = private / 'direct/unified_reparam_derived_shell/positive_seed_certificate.json'
        need(str(mandatory_seed.relative_to(private)) in direct_pins and
             len(load(mandatory_seed)['seeds']) == 15, 'mandatory complete seed-positivity certificate')
        old = private / ('intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/'
                         'ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24')
        binding = load(private / 'architecture/SOURCE_BINDING.json')
        approved = ['100-quartics407-888', '101-constructive-reductions', '112-powered-saturation-round14']
        by_hash = {}
        for family in approved:
            for path in sorted((ROOT / 'con-zfc-diophantine-forms' / family).rglob('*.py')):
                by_hash.setdefault(digest(path), str(path.relative_to(ROOT)))
        inherited = {}
        need(len(binding['imported_executable_closure']) == 21, 'complete inherited executable closure')
        for name, expected in binding['imported_executable_closure'].items():
            need(digest(old / name) == expected and expected in by_hash, 'accepted inherited module ' + name)
            inherited[name] = dict(sha256=expected, accepted_file=by_hash[expected])
        for name in ['build_signed.py', 'factor_horn.py', 'terminal_elimination.py', 'translate_coordinates.py']:
            need(digest(private / 'direct' / name) in by_hash, 'accepted direct dependency ' + name)

        def child(label, arguments):
            command = flags + [str(private / arguments[0])] + [str(x) for x in arguments[1:]]
            result = subprocess.run(command, cwd=private, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            logs[label] = result.stdout
            need(result.returncode == 0, label + ' failed: ' + result.stdout.decode(errors='replace'))
            commands[label] = dict(status='PASS', returncode=0, stdout_sha256=sha256(result.stdout).hexdigest())

        arch_check = scratch / 'architecture-check.json'
        child('architecture-check', ['architecture/check_unified_product.py', '--output', arch_check])
        need(arch_check.read_bytes() == (private / 'architecture/CHECK.json').read_bytes(),
             'exact author complete architecture checker receipt')
        arch_rebuild = scratch / 'architecture-rebuild.json'
        arch_binding = scratch / 'architecture-source-binding.json'
        child('architecture-rebuild', ['architecture/reproduce_unified_product.py', '--output', arch_rebuild,
                                      '--source-binding', arch_binding])
        expected_rebuild = 'REPRODUCTION_OPTIMIZED.json' if sys.flags.optimize else 'REPRODUCTION.json'
        need(arch_rebuild.read_bytes() == (private / 'architecture' / expected_rebuild).read_bytes(),
             'exact author six-variant reconstruction receipt')
        need(arch_binding.read_bytes() == (private / 'architecture/SOURCE_BINDING.json').read_bytes(),
             'exact full runtime import/source binding')
        source = scratch / 'rebuilt-source'
        center = scratch / 'rebuilt-integer442'
        child('direct-source', ['direct/build_residue.py', private / 'architecture/unified_derived_shell/raw',
                                source, '--reparam'])
        source_inventory = snapshot(source)
        need(source_inventory == snapshot(private / 'direct/unified_reparam_derived_shell') and
             len(source_inventory) == 15, 'all15 rebuilt direct-source files exact and closed')
        child('direct-center', ['direct/center_integer.py', source, center])
        center_inventory = snapshot(center)
        need(center_inventory == snapshot(private / 'direct/integer442') and len(center_inventory) == 5,
             'all5 rebuilt centered endpoint files exact and closed')
        audit = scratch / 'direct-audit.json'
        child('direct-audit', ['direct_audit/check_direct.py', '--variant', 'unified_reparam_derived_shell',
                               '--raw', 'unified_derived_shell', '--endpoint', 'integer442', '--output', audit])
        result = load(audit)
        need(result['verified'] is True and len(result['natural']) == 6 and
             all(x['rejected'] for x in result['mutation_controls'].values()), 'all direct and six natural checks')
        pc = load(source / 'projection_certificate.json')
        tc = load(center / 'translation_certificate.json')
        need(snapshot(private) == before, 'every original private ZIP member remains unchanged; no extras')
        receipt = dict(schema='round15_scoped_direct_reproduction_v1', status='PASS',
                       optimized_python=bool(sys.flags.optimize), checker_sha256=digest(Path(__file__)),
                       archive_git_commit=COMMIT, archive_git_path=ARCHIVE_PATH, archive_sha256=ARCHIVE_SHA256,
                       original_members=569, original_members_unchanged=True, direct_pins=len(direct_pins),
                       mandatory_positive_seed_certificate=True, inherited_executable_closure=inherited,
                       complete_runtime_binding_exact_author=True, architecture=load(arch_check),
                       architecture_rebuild=load(arch_rebuild), direct=result,
                       generated_source_inventory=source_inventory, generated_centered_inventory=center_inventory,
                       direct_projection_steps=len(pc['steps']), direct_unconstrained_removed=pc['unconstrained_removed'],
                       final_translation_coordinates=len(tc['shifts']), final_search_steps=len(tc['search_history']),
                       commands=commands, sympy_or_top_runner_or_scalar_or_norm_or_incoming_or_lean_executed=False,
                       canonical_or_frozen_files_modified=False)
    text = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    for label, data in logs.items():
        record(args.output.with_name(args.output.stem + '-' + label + '.txt'), data)
    record(args.output, text.encode())
    print(json.dumps(dict(status='PASS', optimized_python=bool(sys.flags.optimize),
                          original_members=569, source_files=15, centered_files=5,
                          direct=receipt['direct']['signed']), sort_keys=True))


if __name__ == '__main__':
    main()
