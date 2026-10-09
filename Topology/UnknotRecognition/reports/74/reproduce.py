#!/usr/bin/env python3
"""Quick verification by default; optional audits write fresh reproduction data.

Run ``python reproduce.py`` for recorded-source checks, 66 independent
envelope-certificate replays, one essential-disc replay, and 24 focused tests.
No third-party Python package is required for the default workflow.
"""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import importlib.abc
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
CODE = ROOT / 'code'
PIN = '66098968e88bba797143ac1bf7ad0ac4c5f697df'


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def recorded_source_checks(emit):
    checked = []
    for name in ('benchmark.json', 'audit.json', 'coverage.json'):
        record = read_json(ROOT / 'results' / name)
        if 'baseline_commit' in record and record['baseline_commit'] != PIN:
            raise RuntimeError('unexpected source pin in ' + name)
        for relative, expected in record['source_sha256'].items():
            if relative == 'coverage_benchmark.py':
                path = ROOT / 'experiments' / relative
            else:
                path = CODE / relative
                if CODE.resolve() not in path.resolve().parents:
                    raise RuntimeError('source path outside code snapshot')
            actual = sha256(path.read_bytes()).hexdigest()
            if actual != expected:
                raise RuntimeError('recorded source hash mismatch: ' + str(path))
            checked.append(str(path.relative_to(ROOT)))
    corpus = ROOT / 'fixtures' / 'discovery_corpus.json'
    digest = sha256(corpus.read_bytes()).hexdigest()
    if digest != read_json(ROOT / 'results/audit.json')['corpus_sha256']:
        raise RuntimeError('frozen corpus differs from the main audit')
    if digest != read_json(ROOT / 'results/independent_envelope_audit.json')['source_sha256']:
        raise RuntimeError('frozen corpus differs from the independent audit')
    if (ROOT / 'reference/normal_sector.py').read_bytes() != (
            CODE / 'sector_envelope_research/baseline_normal_sector.py').read_bytes():
        raise RuntimeError('pinned reference and timed baseline differ')
    emit('PASS recorded source hashes: {} entries, {} distinct source files; '
         'both corpus bindings and the pinned baseline copy'.format(
             len(checked), len(set(checked))))
    return dict(recorded_source_entries=len(checked),
                distinct_source_files=len(set(checked)), corpus_bindings=2,
                baseline_copy=True)


class BlockEnumerationProducers(importlib.abc.MetaPathFinder):
    """Make accidental ray-producing imports fail during saved-proof replay."""

    blocked = {'fastunknot.normal_sector', 'fastunknot.sector_envelope',
               'fastunknot.sector_envelope_certificate'}

    def find_spec(self, fullname, path=None, target=None):
        if fullname in self.blocked or fullname.startswith('sector_envelope_research'):
            raise RuntimeError('enumeration producer imported during replay: ' + fullname)
        return None


def replay_saved_certificates(emit):
    sys.path.insert(0, str(CODE))
    guard = BlockEnumerationProducers()
    sys.meta_path.insert(0, guard)
    try:
        from fastunknot.sector_envelope_verify import verify_sector_envelope_certificate
        from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate
        from fastunknot.integer_codec import encoded_integer

        model_audit = read_json(ROOT / 'results/independent_envelope_audit.json')
        complete, model_only = 0, 0
        for entry in model_audit['records']:
            proof = entry.get('certificate')
            if proof is None:
                if entry['dimension'] <= 2:
                    raise RuntimeError('missing eligible audit certificate')
                model_only += 1
                continue
            if not verify_sector_envelope_certificate(entry['triangulation'], proof):
                raise RuntimeError('independent audit replay failed: ' + entry['fixture'])
            complete += 1
        if complete != 60 or complete != model_audit['complete_certificates']:
            raise RuntimeError('unexpected independent-audit certificate count')
        coverage = read_json(ROOT / 'results/coverage.json')
        coverage_count = 0
        for entry in coverage['certificates']:
            if not verify_sector_envelope_certificate(
                    entry['fixture']['triangulation'], entry['certificate']):
                raise RuntimeError('coverage benchmark certificate replay failed')
            coverage_count += 1
        if coverage_count != 6:
            raise RuntimeError('unexpected coverage certificate count')
        example = read_json(ROOT / 'examples/extra_non_q_disc.json')
        if not verify_normal_disk_count_certificate(
                example['triangulation'], example['coordinates'],
                example['disk_certificate']):
            raise RuntimeError('extra non-Q disc certificate replay failed')
        if encoded_integer(example['disk_certificate']['compressing_disk_components']) != 1:
            raise RuntimeError('the extra-ray example does not assert one essential disc')
    finally:
        sys.meta_path.remove(guard)
    emit('PASS saved proofs: 60 independent-audit envelope certificates, '
         '6 coverage certificates, 1 essential-disc certificate; '
         '{} higher-nullity model-only records retained'.format(model_only))
    return dict(independent_envelope_certificates=complete,
                coverage_certificates=coverage_count, essential_disc_certificates=1,
                higher_nullity_model_only=model_only, enumeration_producers_blocked=True)


def run_command(command, name, folder, env, emit, cwd=ROOT):
    emit('RUN ' + name)
    output = []
    with (folder / (name + '.log')).open('w', encoding='utf-8') as log:
        with subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True,
                              encoding='utf-8', errors='replace') as process:
            for line in process.stdout:
                log.write(line)
                output.append(line)
                emit(line.rstrip('\n'))
            status = process.wait()
    if status:
        raise RuntimeError('{} failed with exit status {}'.format(name, status))
    return ''.join(output)


def main():
    if sys.version_info < (3, 10):
        raise SystemExit('Python 3.10 or newer is required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', action='store_true',
                        help='repeat all 9,344 eligible frozen-corpus sector comparisons')
    parser.add_argument('--fresh-regina', action='store_true',
                        help='implies --audit; also repeat the 15 declared fresh enumerations')
    parser.add_argument('--family', action='store_true',
                        help='repeat the closed-form capped-family and topology audit')
    parser.add_argument('--bench', action='store_true',
                        help='repeat the full five-round and three-round benchmark protocols')
    parser.add_argument('--pdf', action='store_true',
                        help='compile the article twice into the fresh reproduction directory')
    args = parser.parse_args()
    sys.dont_write_bytecode = True
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S_%fZ')
    folder = ROOT / 'reproduction' / ('run_' + stamp)
    folder.mkdir(parents=True, exist_ok=False)
    started = time.perf_counter()
    with (folder / 'run.log').open('w', encoding='utf-8', buffering=1) as log:
        def emit(message):
            print(message, flush=True)
            log.write(message + '\n')

        emit('Reproduction output: ' + str(folder))
        emit('Source pin: ' + PIN)
        report = dict(schema='minimum-envelope-reproduction-v1', source_pin=PIN,
                      python=sys.version, status='RUNNING')
        try:
            report['source_checks'] = recorded_source_checks(emit)
            report['certificate_replay'] = replay_saved_certificates(emit)
            env = dict(os.environ)
            env['PYTHONDONTWRITEBYTECODE'] = '1'
            env['PYTHONPATH'] = str(CODE) + (
                os.pathsep + env['PYTHONPATH'] if env.get('PYTHONPATH') else '')
            text = run_command([sys.executable, '-B', '-m', 'unittest', 'discover',
                                '-s', str(CODE / 'tests'), '-p',
                                'test_sector_envelope*.py', '-v'],
                               'focused_tests', folder, env, emit)
            match = re.search(r'Ran (\d+) tests', text)
            if match is None or int(match.group(1)) != 24:
                raise RuntimeError('expected all 24 focused tests')
            report['focused_tests'] = 24
            if args.audit or args.fresh_regina:
                command = [sys.executable, '-B', '-m', 'sector_envelope_research.audit',
                           '--corpus', str(ROOT / 'fixtures/discovery_corpus.json'),
                           '--output', str(folder / 'audit.json')]
                if args.fresh_regina:
                    command.append('--fresh-regina')
                run_command(command, 'audit', folder, env, emit)
                report['audit'] = read_json(folder / 'audit.json')['counts']
            if args.family:
                run_command([sys.executable, '-B', str(ROOT / 'experiments/family_oracle.py'),
                             '--code-root', str(CODE), '--output',
                             str(folder / 'family_oracle.json')],
                            'family', folder, env, emit)
                report['family'] = read_json(folder / 'family_oracle.json')['counts']
            if args.bench:
                emit('The full benchmark takes several minutes; avoid concurrent CPU-heavy work.')
                run_command([sys.executable, '-B', '-m', 'sector_envelope_research.benchmark',
                             '--repeats', '5', '--output', str(folder / 'benchmark.json')],
                            'benchmark', folder, env, emit)
                run_command([sys.executable, '-B', str(ROOT / 'experiments/coverage_benchmark.py'),
                             '--code-root', str(CODE), '--repeats', '3',
                             '--output', str(folder / 'coverage.json')],
                            'coverage_benchmark', folder, env, emit)
                report['benchmarks'] = ['benchmark.json', 'coverage.json']
            if args.pdf:
                executable = shutil.which('pdflatex')
                if executable is None:
                    raise RuntimeError('pdflatex is required for --pdf')
                pdf_folder = folder / 'pdf'
                pdf_folder.mkdir()
                for iteration in (1, 2):
                    run_command([executable, '-interaction=nonstopmode', '-halt-on-error',
                                 '-output-directory', str(pdf_folder), 'minimum_envelopes.tex'],
                                'pdflatex_' + str(iteration), folder, env, emit,
                                cwd=ROOT / 'article')
                report['pdf'] = str((pdf_folder / 'minimum_envelopes.pdf').relative_to(folder))
            report['status'] = 'COMPLETE'
            report['seconds'] = time.perf_counter() - started
            emit('COMPLETE in {:.3f} seconds. Original results were preserved.'.format(
                report['seconds']))
        except Exception as exc:
            report.update(status='FAILED', error=repr(exc),
                          seconds=time.perf_counter() - started)
            emit('FAILED: ' + str(exc))
            raise
        finally:
            (folder / 'run_report.json').write_text(
                json.dumps(report, indent=2) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
