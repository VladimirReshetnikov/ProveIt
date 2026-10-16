"""Recover batch151 offline and optionally replay its finite computations.

Default/--prepare-only: recover both original Git archives to fresh scratch.
--run24,25|all: replay the selected packages' finite functional checks.
--searches: also replay source24's264 compiler recipes and source25's20,480
compiled recipes; implies --run all. --fusion additionally runs source25's
148,368 bounded symbol-wise fusions and implies --run25.

No network, Lean/Coq, PDF build or unbounded consistency search is invoked.
Bulk source/artifact manifests are entirely skipped using in-memory adapters.
Functional table/program pins, exact regenerated artifacts, operation checks,
finite mathematical checks and candidate-ledger comparisons remain enabled.
The recovered source files are never patched on disk.
"""
from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from zipfile import ZipFile

ARRIVAL = '121a0de1bb6ea2d9464cd524b95030b39a7c614a'
PACKAGES = {
    24: ('zfc_consistency_proposal.zip', 'zfc_minimal_theory',
         '2178c3885423f923021d4aaf1dbf52b4e2060837'),
    25: ('zfc_exact_hull_research.zip', 'zfc_exact_hull_research',
         'de047657e193ec605e930eaf149a44a38031820b'),
}
PATCHES = {
    '24-proxy': [
        ('''        pins = json.loads((here/"vendor_source_pins.json").read_text())
        for relative, expected in pins.items():
            if hashlib.sha256((here/relative).read_bytes()).hexdigest() != expected:
                raise ValueError("vendored source changed: "+relative)
''', ''),
    ],
    '25-full': [
        ("'artifact_integrity': artifact_integrity(),",
         "'artifact_integrity': {'status': 'skipped by intake policy', 'verified': False},"),
    ],
    '25-machine': [
        ("'pinned_inputs': check_sources(),",
         "'pinned_inputs': {'pinned_files_verified': 0, 'manifest_checks_skipped': True},"),
    ],
}


def patched(kind: str, path: Path) -> str:
    source = path.read_text()
    for old, new in PATCHES[kind]:
        if source.count(old) != 1:
            raise ValueError(f'Expected unique intake adapter marker: {kind}: {path}')
        source = source.replace(old, new)
    compile(source, str(path), 'exec')
    return source


def execute(path: Path, argv: list[str], source: str | None = None) -> None:
    sys.argv = [str(path), *argv]
    exec(compile(path.read_text() if source is None else source, str(path), 'exec'),
         {'__file__': str(path), '__name__': '__main__'})


def child_script(command: list) -> tuple[int, Path] | None:
    """Find the Python file after interpreter flags such as -B."""
    for i, value in enumerate(command[1:], 1):
        if str(value).endswith('.py'):
            return i, Path(value)
    return None


def worker(kind: str, root: Path, argv: list[str]) -> None:
    root = root.resolve()
    helper = str(Path(__file__).resolve())
    if kind in ('24-full', '25-full'):
        original_run = subprocess.run

        def adapted_run(command, *args, **kwargs):
            command = list(command)
            child = child_script(command)
            if child is not None:
                i, script = child
                adapter = ('24-proxy' if kind == '24-full' and script.name == 'measure_proxy.py'
                           else '25-machine' if kind == '25-full' and
                           script.name == 'reproduce.py' and script.parent.name == 'machine'
                           else None)
                if adapter is not None:
                    command = [sys.executable, '-B', helper, '_worker', adapter,
                               str(root), *map(str, command[i + 1:])]
            return original_run(command, *args, **kwargs)

        subprocess.run = adapted_run
        path = root / 'reproduce.py'
        execute(path, argv, patched(kind, path) if kind in PATCHES else None)
    elif kind == '24-proxy':
        path = root / 'experiments/o_erasure/measure_proxy.py'
        execute(path, argv, patched(kind, path))
    elif kind == '25-machine':
        path = root / 'machine/reproduce.py'
        execute(path, argv, patched(kind, path))
    else:
        raise ValueError(f'Unknown internal worker: {kind}')


def repository(explicit: Path | None) -> Path:
    candidates = [explicit] if explicit else [Path.cwd(), *Path.cwd().parents,
                                             *Path(__file__).resolve().parents]
    for candidate in candidates:
        if candidate is not None and (candidate / '.git').exists():
            return candidate.resolve()
    raise ValueError('Run inside ProveIt or pass --repo.')


def main() -> None:
    if not __debug__:
        raise SystemExit('Run without -O/PYTHONOPTIMIZE: functional checks use assertions.')
    sys.dont_write_bytecode = True
    if len(sys.argv) > 1 and sys.argv[1] == '_worker':
        worker(sys.argv[2], Path(sys.argv[3]), sys.argv[4:])
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--output', type=Path, help='new or empty scratch directory outside the checkout')
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--run', default='', metavar='24,25|all',
                        help='optional finite package replays; default is recovery only')
    parser.add_argument('--searches', action='store_true',
                        help='also replay the264 and20,480 compiled grammar families')
    parser.add_argument('--fusion', action='store_true',
                        help='explicitly replay148,368 bounded fusions (can take several minutes)')
    args = parser.parse_args()
    try:
        selected = set(PACKAGES) if args.run == 'all' else {
            int(s.strip()) for s in args.run.split(',') if s.strip()}
    except ValueError:
        parser.error('--run must be all or a comma-separated list of24,25')
    if selected - PACKAGES.keys():
        parser.error('--run source numbers must be24,25')
    if args.prepare_only and (selected or args.searches or args.fusion):
        parser.error('--prepare-only cannot be combined with --run/--searches/--fusion')
    if args.searches:
        selected.update(PACKAGES)
    if args.fusion:
        selected.add(25)
    repo = repository(args.repo)
    scratch = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-batch151-reproduce-'))
    if scratch.is_relative_to(repo):
        raise ValueError('Output must be outside the checkout.')
    if args.output:
        scratch.mkdir(parents=True, exist_ok=True)
        if any(scratch.iterdir()):
            raise ValueError('Requested output must be empty; delivered trees are never reused.')
    roots = {}
    print(f'Scratch: {scratch}', flush=True)
    for number, (archive, wrapper, _) in PACKAGES.items():
        raw = subprocess.check_output(['git', 'show', f'{ARRIVAL}:docs/incoming/{archive}'], cwd=repo)
        destination = scratch / str(number)
        with ZipFile(io.BytesIO(raw)) as zipped:
            for name in zipped.namelist():
                path = Path(name)
                if path.is_absolute() or '..' in path.parts:
                    raise ValueError(f'Archive path escapes scratch: {name}')
            zipped.extractall(destination)
        roots[number] = destination / wrapper
        if not roots[number].is_dir():
            raise ValueError(f'Missing expected archive wrapper: {wrapper}')
    for kind, path in {
        '24-proxy': roots[24] / 'experiments/o_erasure/measure_proxy.py',
        '25-full': roots[25] / 'reproduce.py',
        '25-machine': roots[25] / 'machine/reproduce.py',
    }.items():
        patched(kind, path)
    summary = dict(batch=151, arrival=ARRIVAL, python=sys.version, scratch=str(scratch),
                   packages={str(n): dict(archive=a, wrapper=w, repository_pin=p, root=str(roots[n]))
                             for n, (a, w, p) in PACKAGES.items()},
                   selected_sources=sorted(selected), searches=args.searches, fusion=args.fusion,
                   checksum_manifests_checked=False, bulk_provenance_checks=False,
                   selective_adapters_validated=True, recovered_sources_patched_on_disk=False,
                   network_used=False, proof_assistant_invoked=False, pdf_build_invoked=False,
                   unbounded_search_run=False, checks=[])

    def save():
        (scratch / 'reproduction.json').write_text(json.dumps(summary, indent=2) + '\n')

    def run(name: str, cwd: Path, command: list[str]):
        begin = time.monotonic()
        result = subprocess.run([sys.executable, '-B', *command], cwd=cwd,
                                capture_output=True, text=True)
        log = scratch / f'{name}.log'
        log.write_text(result.stdout + result.stderr)
        summary['checks'].append(dict(check=name, cwd=str(cwd), command=command,
                                     returncode=result.returncode,
                                     seconds=round(time.monotonic() - begin, 3), log=str(log)))
        save()
        print(f'{name}: exit {result.returncode}', flush=True)
        if result.returncode:
            print(result.stdout + result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)

    save()
    helper = str(Path(__file__).resolve())
    for number in sorted(selected):
        arguments = ([] if number == 24 else
                     ['--quick', '--output', str(scratch / 'source25-replay.json')])
        if number == 25 and args.searches:
            arguments.append('--full-search')
        run(f'{number}-finite', roots[number],
            [helper, '_worker', f'{number}-full', str(roots[number]), *arguments])
    if args.searches:
        output = scratch / 'source24-full264'
        run('24-full264', roots[24] / 'experiments/o_erasure',
            [helper, '_worker', '24-proxy', str(roots[24]), '--seeds', '32', '--output', str(output)])
        actual = json.loads((output / 'proxy_measurements.json').read_text())
        expected = json.loads((roots[24] / 'experiments/o_erasure/measurement/proxy_measurements.json').read_text())
        if actual['variants'] != expected['variants']:
            raise ValueError('Source24 full264 variants, histograms or recipes differ.')
        summary['source24_full264_all_variants_match'] = True
        save()
    if args.fusion:
        run('25-bounded-fusion', roots[25] / 'machine',
            [helper, '_worker', '25-machine', str(roots[25]), '--fusion', '--output',
             str(scratch / 'source25-fusion-replay.json')])
    summary['requested_checks_passed'] = True
    save()


if __name__ == '__main__':
    main()
