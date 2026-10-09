#!/usr/bin/env python3
"""Run independent reproduction jobs from the unpacked research archive.

All new results and build products go under rerun/. The script's own location,
not the calling shell's working directory, determines the archive root.
"""

import argparse
import hashlib
import importlib.util
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
FAST = ROOT / 'code' / 'fast'
RERUN = ROOT / 'rerun'
RESULTS = RERUN / 'results'
MAIN_TEX = 'compressed_component_certificates.tex'
PINNED_COMMIT = '274909dd8724e411ece14e47ac4addea717aeca6'
BASELINE_SHA256 = '1d8b70ce02336872e8d2709bb4d1d156a230dfce5f46eab4e119d677156ec562'


class ReproductionError(RuntimeError):
    """A missing dependency, incomplete archive, or failed subprocess."""


def required_file(path):
    if not path.is_file():
        raise ReproductionError(f'Required archive file is missing: {path}')
    return path


def environment():
    env = os.environ.copy()
    env['PYTHONUNBUFFERED'] = '1'
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env['MPLBACKEND'] = 'Agg'
    env['MPLCONFIGDIR'] = str(RERUN / 'matplotlib-config')
    return env


def run(command, *, cwd=FAST, log, append=False):
    """Tee merged stdout/stderr live, retain a log, and reject nonzero exits."""
    command = [str(part) for part in command]
    if not cwd.is_dir():
        raise ReproductionError(f'Required working directory is missing: {cwd}')
    log.parent.mkdir(parents=True, exist_ok=True)
    heading = f'Working directory: {cwd}\nCommand: {shlex.join(command)}\n'
    print(heading, flush=True)
    with log.open('a' if append else 'w', encoding='utf-8') as output:
        output.write(heading)
        output.flush()
        with subprocess.Popen(command, cwd=cwd, env=environment(),
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              text=True, encoding='utf-8', errors='replace',
                              bufsize=1) as process:
            assert process.stdout is not None
            for line in process.stdout:
                sys.stdout.write(line)
                sys.stdout.flush()
                output.write(line)
                output.flush()
            returncode = process.wait()
        output.write(f'\nExit code: {returncode}\n')
    if returncode:
        raise ReproductionError(
            f'Command failed with exit code {returncode}. Full output: {log}')
    print(f'Completed. Log: {log}', flush=True)


def python_command(*arguments):
    return [sys.executable, '-u', '-B', *arguments]


def prepare_article():
    """Copy once, then preserve any tables and figures regenerated there."""
    source = ROOT / 'article'
    required_file(source / MAIN_TEX)
    target = RERUN / 'article'
    if not target.exists():
        shutil.copytree(source, target, ignore=shutil.ignore_patterns(
            '*.aux', '*.bbl', '*.blg', '*.fdb_latexmk', '*.fls', '*.log',
            '*.out', '*.toc', '*.synctex.gz', '__pycache__'))
        print(f'Copied manuscript to {target}', flush=True)
    required_file(target / MAIN_TEX)
    return target


def demo(_args):
    run(python_command('-m', 'component_profile_research.demo', '--output',
                       RESULTS / 'component_demo.json'),
        log=RESULTS / 'demo.log')


def tests(_args):
    # The maintained weighted tests write beside their research module.
    # Save that fresh diagnostic, then restore any delivered copy exactly.
    summary = FAST / 'component_profile_research' / 'weighted_test_summary.json'
    saved = summary.read_bytes() if summary.exists() else None
    previous_stat = summary.stat() if summary.exists() else None
    copied = False
    try:
        run(python_command('-m', 'unittest', 'discover', '-s', 'tests', '-v'),
            log=RESULTS / 'full_tests.log')
    finally:
        if summary.exists():
            changed = (previous_stat is None
                       or summary.stat().st_mtime_ns != previous_stat.st_mtime_ns
                       or summary.read_bytes() != saved)
            if changed:
                shutil.copy2(summary, RESULTS / 'weighted_test_summary.json')
                copied = True
                print(f'Copied weighted diagnostic to {RESULTS}', flush=True)
        if saved is None:
            summary.unlink(missing_ok=True)
        else:
            summary.write_bytes(saved)
            os.utime(summary, ns=(previous_stat.st_atime_ns,
                                  previous_stat.st_mtime_ns))
    if not copied:
        raise ReproductionError('The test run did not produce a fresh weighted summary.')


def audit(_args):
    if importlib.util.find_spec('regina') is None:
        raise ReproductionError(
            'The independent normal-surface audit requires Regina. '
            'Install the optional normal dependency described in README.md.')
    script = required_file(ROOT / 'experiments' / 'independent_normal_audit.py')
    fixture = required_file(ROOT / 'experiments' / 'finite_trefoil_fixture.json')
    run(python_command(script, '--fast-root', FAST, '--trefoil-fixture', fixture,
                       '--output', RESULTS / 'independent_normal_audit.json'),
        log=RESULTS / 'independent_normal_audit.log')


def benchmark(args):
    baseline = required_file(ROOT / 'reference' / 'interval_orbits.py')
    observed = hashlib.sha256(baseline.read_bytes()).hexdigest()
    if observed != BASELINE_SHA256:
        raise ReproductionError(
            'The historical interval producer differs from the exact pinned '
            f'baseline at commit {PINNED_COMMIT}. Observed SHA-256: {observed}')
    script = required_file(ROOT / 'experiments' / 'benchmark_orbits.py')
    print('Collect timings without concurrent benchmarks or other heavy jobs.', flush=True)
    run(python_command(script, '--fast-dir', FAST, '--baseline', baseline,
                       '--rounds', args.rounds, '--seed', args.seed,
                       '--output', RESULTS / 'benchmark_orbits.json'),
        log=RESULTS / 'benchmark_orbits.log')


def figures(args):
    if importlib.util.find_spec('matplotlib') is None:
        raise ReproductionError('Figure regeneration requires Matplotlib.')
    if args.results is not None:
        measurements = args.results.resolve()
    else:
        measurements = ROOT / 'results' / 'benchmark_orbits.json'
    required_file(measurements)
    article = prepare_article()
    script = required_file(ROOT / 'experiments' / 'make_tables_figures.py')
    print(f'Regenerating tables and figures from {measurements}', flush=True)
    run(python_command(script, '--results', measurements, '--article', article),
        log=RESULTS / 'figures.log')


def article(_args):
    target = prepare_article()
    if shutil.which('pdflatex') is None:
        raise ReproductionError('PDF compilation requires pdfLaTeX on PATH.')
    flags = ['-interaction=nonstopmode', '-halt-on-error', '-file-line-error']
    if shutil.which('latexmk') is not None:
        commands = [['latexmk', '-pdf', *flags, MAIN_TEX]]
    else:
        if shutil.which('bibtex') is None:
            raise ReproductionError(
                'Without latexmk, the PDF build requires both pdfLaTeX and BibTeX.')
        commands = [
            ['pdflatex', *flags, MAIN_TEX],
            ['bibtex', Path(MAIN_TEX).stem],
            ['pdflatex', *flags, MAIN_TEX],
            ['pdflatex', *flags, MAIN_TEX],
        ]
    for index, command in enumerate(commands):
        run(command, cwd=target, log=RESULTS / 'article_build.log', append=index > 0)
    pdf = required_file(target / Path(MAIN_TEX).with_suffix('.pdf'))
    print(f'Rebuilt article: {pdf}', flush=True)


def positive_integer(raw):
    value = int(raw)
    if value < 1:
        raise argparse.ArgumentTypeError('must be a positive integer')
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest='command', required=True)
    for name, function, description in (
            ('demo', demo, 'Run the dependency-free component certificate demonstration.'),
            ('tests', tests, 'Run the complete maintained unittest suite with a live log.'),
            ('audit', audit, 'Run the finite independent normal-surface audit (Regina).'),
            ('benchmark', benchmark, 'Measure exact pinned-source paired orbit timings.'),
            ('figures', figures, 'Regenerate manuscript tables and vector figures.'),
            ('article', article, 'Rebuild the copied manuscript with LaTeX.')):
        command = subparsers.add_parser(name, help=description, description=description)
        command.set_defaults(function=function)
        if name == 'benchmark':
            command.add_argument('--rounds', type=positive_integer, default=7)
            command.add_argument('--seed', type=int, default=26100945)
        elif name == 'figures':
            command.add_argument('--results', type=Path,
                                 help='measurement JSON; defaults to the recorded results')
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        parser.error('Python 3.10 or later is required.')
    RESULTS.mkdir(parents=True, exist_ok=True)
    try:
        args.function(args)
    except (ReproductionError, OSError) as exc:
        print(f'Reproduction failed: {exc}', file=sys.stderr, flush=True)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
