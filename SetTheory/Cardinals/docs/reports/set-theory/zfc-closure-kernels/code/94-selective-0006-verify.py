#!/usr/bin/env python3
"""Reproduce this research package; no success label asserts a sub-245 machine.

The baseline is extracted from its unchanged archive into a fresh workspace.
Frozen delivery files are never edited by this entry point. The default uses
the Python standard library. --full adds finite C++17 mutation sweeps;
--whole-frame repeats the slower fully expanded symbolic runtime proof.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
BASELINE_ZIP_SHA = '5a38b0e7475905584eabcb75912caa8d5f4149148e8c2a2439b2702a9de49ba1'
BASELINE_OLD_SHA = 'f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'
VARIANT_OLD_SHA = 'e074e5349e32c9290625805dcae155610991fba9e4a7d61039c9bda5a2ca80ae'
VARIANT_SHA = '1c29e7659b916c0cb31d26c26e73d08f0e3e7f6444560788ec554135aecbea85'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_inventory(directory):
    count = 0
    for row in (directory / 'SHA256SUMS').read_text().splitlines():
        expected, relative = row.split('  ', 1)
        path = (directory / relative).resolve()
        assert path.is_relative_to(directory.resolve()) and path.is_file(), relative
        assert digest(path) == expected, ('Hash mismatch', relative)
        count += 1
    return count


def load(path):
    return json.loads(path.read_text())


def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full', action='store_true')
    ap.add_argument('--whole-frame', action='store_true')
    ap.add_argument('--output', type=Path, help='New or empty directory for fresh results.')
    args = ap.parse_args()
    began = time.monotonic()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-sub245-replay-'))
    if out.exists() and any(out.iterdir()):
        raise ValueError('Choose a new or empty output directory; frozen evidence is not overwritten.')
    out.mkdir(parents=True, exist_ok=True)
    file_count = verify_inventory(ROOT)
    archive = ROOT / 'reference/zfc245-proof-20261018.zip'
    assert digest(archive) == BASELINE_ZIP_SHA
    print(f'PASS: {file_count} delivered hashes and unchanged reference archive.', flush=True)
    env = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}
    py = [sys.executable, '-B']
    checks = []

    def run(name, command, cwd=ROOT):
        print('Checking ' + name + ' ...', flush=True)
        log = out / (name + '.log')
        start = time.monotonic()
        with log.open('w') as stream:
            proc = subprocess.run([str(x) for x in command], cwd=cwd, env=env,
                                  stdout=stream, stderr=subprocess.STDOUT)
        if proc.returncode:
            raise RuntimeError(name + ' failed:\n' + log.read_text()[-10000:])
        checks.append({'name': name, 'status': 'PASS',
                       'seconds': round(time.monotonic() - start, 6)})
        print('PASS: ' + name, flush=True)

    with tempfile.TemporaryDirectory(prefix='zfc-sub245-work-') as temporary:
        work = Path(temporary)
        with zipfile.ZipFile(archive) as z:
            for info in z.infolist():
                target = (work / info.filename).resolve()
                assert target.is_relative_to(work), info.filename
                # Reject archived symbolic links before extraction.
                assert (info.external_attr >> 16) & 0o170000 != 0o120000, info.filename
            z.extractall(work)
        reference = work / 'zfc245-proof-20261018'
        baseline_files = verify_inventory(reference)
        assert digest(reference / 'certificate/machine_old.tm') == BASELINE_OLD_SHA
        env['ZFC245_PACKAGE'] = str(reference)
        env['ZFC245_REFERENCE'] = str(reference)

        theory_out = out / 'theory'
        run('finite-formalism', py + [ROOT / 'theory_work/skolem_reduct.py', '--output', theory_out])
        for frozen in (ROOT / 'theory_work/skolem_reduct_results').iterdir():
            if frozen.is_file():
                assert (theory_out / frozen.name).read_bytes() == frozen.read_bytes(), frozen.name
        theory = load(theory_out / 'results.json')
        assert theory['status'] == 'PASS'
        for name, expected in [('fc15', (20, 53, 1134)), ('fc16', (21, 57, 1341))]:
            metrics = theory['theories'][name]['additional_corollaries']['raw_guard_derived_reflexivity']['metrics']
            assert (metrics['clauses'], metrics['literals'], metrics['template_bits']) == expected
        run('membership-transport-countermodel-diagnostics', py + [
            ROOT / 'grammar_work/fc15_without_e_countermodel.py',
            '--reference', ROOT / 'theory_work/reference',
            '--output', out / 'fc15-without-e.json'])
        countermodel = load(out / 'fc15-without-e.json')
        assert countermodel['status'] == 'PASS'
        assert countermodel['total_assignments_checked'] == 203478
        assert countermodel['ground_E_failure']['literal_truth_values'] == [False] * 4
        assert countermodel['FC16_failure']['literal_truth_values'] == [False] * 4

        run('fine-atom-grammar', py + [ROOT / 'grammar_work/verify_fine_identities.py',
            '--package', reference, '--candidate', ROOT / 'grammar_work/fine-seed9022.json',
            '--identities', ROOT / 'grammar_work/fine-atom-identities.json',
            '--output', out / 'fine-atom-check.json'])
        for label, strict in [('strict', True), ('readwrite', False)]:
            command = py + [ROOT / 'trace_work/check_trace_grammar.py',
                ROOT / f'trace_work/best_{label}.json', '--reference', reference,
                '--output', out / f'trace-{label}.json']
            if strict:
                command.append('--strict')
            run('trace-' + label, command)
            data = load(out / f'trace-{label}.json')
            assert data['status'] == 'PASS_ABSTRACT_TRACE_GRAMMAR'
            assert (data['rules'], data['entry_projections'], data['bootstrap_projections']) == (128, 22, 54)

        # The unchanged builder requires its grammar to live inside its package.
        # This new file is written only into the private extracted copy.
        grammar = reference / 'new-grammar.json'
        run('literal-grammar-recovery', py + [ROOT / 'trace_work/literalize_trace_grammar.py',
            '--reference', reference, '--output', grammar])
        assert grammar.read_bytes() == (ROOT / 'trace_work/routing245-d47.json').read_bytes()
        built = out / 'variant-built'
        run('variant-build-and-source-bisimulation', py + [reference / 'code/build_routing_machine.py',
            grammar, built, '--short-scan', '--padding', '64', '--boot-limit', '500000'])
        build = load(built / 'machine-audit.json')
        assert build['status'] == 'PASS_AFFINE_AND_BOOT'
        assert (build['working_states'], build['source_leaves'], build['maximum_depth'],
                build['maximum_zero_run']) == (245, 6460, 47, 6)
        assert digest(built / 'machine.tm') == VARIANT_SHA
        assert digest(built / 'machine_old.tm') == VARIANT_OLD_SHA
        for name in ['machine.tm', 'machine_old.tm', 'sites_logical.json', 'sites_physical.json',
                     'register_bisimulation.json', 'allocation.json', 'renumbering.json']:
            assert (built / name).read_bytes() == (ROOT / 'variant245/certificate' / name).read_bytes(), name
        runtime_out = out / 'variant-runtime'
        run('actual-table-macro-inductions', py + [reference / 'code/audit_existing_machine.py',
            built / 'machine_old.tm', built / 'sites_physical.json', runtime_out,
            '--padding', '64', '--boot-limit', '500000'])
        runtime = load(runtime_out / 'existing-machine-audit.json')
        assert runtime['status'] == 'PASS_AFFINE_AND_BOOT'
        assert runtime['macro_inductions']['status'] == 'PASS'
        assert runtime['affine_all_cases']['cases'] == 8391
        assert runtime['blank_boot']['blank_steps'] == 407915
        run('independent-frame-composition', py + [ROOT / 'trace_work/verify_variant_frames.py',
            '--machine', built, '--grammar', grammar,
            '--lock', reference / 'inputs/state_reduction/bootstrap-lock54.txt',
            '--output', out / 'variant-frame-composition.json'])
        frame = load(out / 'variant-frame-composition.json')
        assert frame['status'] == 'PASS' and frame['nonhalting_successors_normalized'] == 8390

        frozen_whole = load(ROOT / 'variant245/whole-frame.json')
        assert frozen_whole['status'] == 'PASS' and frozen_whole['complete']
        assert frozen_whole['table_sha256'] == VARIANT_OLD_SHA
        assert frozen_whole['counts'] == {'cases': 8391, 'symbolic_rules': 2239582}
        assert len(frozen_whole['rows']) == 490 and frozen_whole['positive_progress_checked']
        if args.whole_frame:
            run('expanded-whole-frame', py + [reference / 'code/full_symbolic_parametric.py',
                '--table', built / 'machine_old.tm', '--sites', built / 'sites_physical.json',
                '--all-values', '--output', out / 'whole-frame.json'])
            fresh_whole = load(out / 'whole-frame.json')
            assert {k:v for k,v in fresh_whole.items() if k != 'seconds'} == {
                k:v for k,v in frozen_whole.items() if k != 'seconds'}

        # Component scripts historically emit beside themselves; run only a copy.
        framework = work / 'framework_work'
        shutil.copytree(ROOT / 'framework_work', framework)
        command = py + [framework / 'reproduce_findings.py', '--reference', reference,
                        '--output', out / 'framework-findings.json']
        if args.full:
            command.append('--full')
        run('framework-findings-and-negative-controls', command)
        findings = load(out / 'framework-findings.json')
        assert findings['status'] == 'PASS_FINDINGS_REPRODUCED'
        assert findings['symbolic_audit']['failed_cases'] == 99
        assert findings['first_clean_frame_disagreement']['mutant_added_one'] == 13

    result = {
        'status': 'PASS_RESEARCH_ARTIFACTS_REPRODUCED',
        'scope': 'No machine below 245 working states is certified. Positive machine result is the depth-47 245-state variant; smaller tables are diagnostic experiments.',
        'source_commit': '6446ff5668307a2ac6aee1896037f0b792090389',
        'delivered_files_hashed': file_count, 'baseline_files_hashed': baseline_files,
        'variant_working_states': 245, 'variant_canonical_sha256': VARIANT_SHA,
        'variant_source_depth': 47, 'variant_zero_run': 6,
        'source_bisimulation': build['register_program_bisimulation'],
        'all_parametric_instruction_cases': 8391, 'nonhalting_successors_normalized': 8390,
        'exact_blank_steps': 407915,
        'whole_frame_frozen_cases': 8391, 'whole_frame_frozen_literal_rows': 490,
        'expanded_whole_frame_freshly_repeated': args.whole_frame,
        'framework_mutation_sweeps_freshly_repeated': args.full,
        'finite_theory_output_byte_equality': True,
        'finite_theory_primary': {'fc15': {'clauses': 20, 'literals': 53, 'template_bits': 1134},
                                 'fc16': {'clauses': 21, 'literals': 57, 'template_bits': 1341}},
        'countermodel_diagnostic_assignments': 203478,
        'python': platform.python_version(), 'checks': checks,
        'output_directory': str(out),
        'seconds': round(time.monotonic() - began, 6)}
    (out / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
