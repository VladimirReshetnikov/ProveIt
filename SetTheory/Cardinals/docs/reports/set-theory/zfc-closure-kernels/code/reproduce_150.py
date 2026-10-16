"""Recover batch 150 offline and optionally replay its finite computations.

Default/--prepare-only: recover all four original packages from Git to scratch.
--run 20,21,22,23 (or all): select complete finite package replays.
--searches: additionally run source20's bounded decoder-fold diagnostic and
source23's 960/6000 grammar sweeps; this implies --run 20,23.

No network, proof assistant, PDF build or unbounded consistency search runs.
Bulk provenance/checksum loops are omitted only from in-memory source copies.
Functional source/table pins, affine contracts, edge checks and exact generated
artifact comparisons remain enabled. Delivered files are never modified.
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
from types import ModuleType
from zipfile import ZipFile

ARRIVAL = '47e8871089dd8d5b5a912350f3285734041528bb'
PACKAGES = {
    20: ('zfc_consistency_completion_proposal.zip', 'zfc_completion_proposal',
         'af518abcf8ca2a7c1b795c07973885041aee0d25'),
    21: ('zfc_epsc2_proposal.zip', 'zfc_epsc2_proposal',
         'af518abcf8ca2a7c1b795c07973885041aee0d25'),
    22: ('zfc_minimal_rule_research.zip', 'zfc_minimal_rule_research',
         'c1f2cc90c15fbdcd5f3ddfd7fcbb0b635c93c650'),
    23: ('zfc_qnand_research.zip', 'zfc_qnand_research',
         'de047657e193ec605e930eaf149a44a38031820b'),
}

# Only bulk provenance checks are removed. Exact baseline/generated-table
# constraints and all operational checks are intentionally left intact.
PATCHES = {
    '20-decoder': [
        ("    provenance = json.loads((vendor / 'PROVENANCE.json').read_text())\n", ''),
        ("        assert hashlib.sha256(source.read_bytes()).hexdigest() == provenance['files_sha256'][rel], ('vendor source mismatch', rel)\n", ''),
        ('    spec.loader.exec_module(module)\n',
         "    intake_load_verify(module, work / 'verify.py')\n"),
    ],
    '20-vendor-verify': [
        ("for filename, digest in VENDOR_HASHES.items():\n    assert hashlib.sha256((HERE / 'vendor' / filename).read_bytes()).hexdigest() == digest\n", ''),
    ],
    '20-epsc': [
        ("    for n,h in EXPECTED.items():\n        if digest(vendor/n)!=h:raise ValueError('Pinned source changed: '+n)\n", ''),
    ],
    '21-full': [
        ('''    for source in provenance["sources"]:
        path = ROOT / "engineering" / source["path"]
        require(path.stat().st_size == source["bytes"],
                f"Vendor size mismatch: {source['path']}")
        require(sha256(path) == source["sha256"],
                f"Vendor hash mismatch: {source['path']}")
    print(f"Verified {len(provenance['sources'])} pinned source/notice hashes.")
''', '    print("Bulk provenance validation skipped by intake policy.")\n'),
        ('"vendor_hashes_checked": len(provenance["sources"]),',
         '"vendor_hashes_checked": 0,'),
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


def execute(path: Path, argv: list[str], source: str | None = None,
            extra: dict | None = None) -> None:
    sys.argv = [str(path), *argv]
    namespace = {'__file__': str(path), '__name__': '__main__'}
    namespace.update(extra or {})
    exec(compile(source if source is not None else path.read_text(), str(path), 'exec'),
         namespace)


def worker(kind: str, root: Path, argv: list[str]) -> None:
    root = root.resolve()
    if kind == '20-full':
        original_run = subprocess.run
        helper = Path(__file__).resolve()
        def adapted_run(command, *args, **kwargs):
            command = list(command)
            if len(command) > 1:
                child = Path(command[1]).name
                adapter = {'reproduce_decoder255.py': '20-decoder',
                           'reproduce_epsc271.py': '20-epsc'}.get(child)
                if adapter:
                    command = [sys.executable, '-B', str(helper), '_worker', adapter,
                               str(root), *command[2:]]
            return original_run(command, *args, **kwargs)
        subprocess.run = adapted_run
        execute(root / 'reproduce.py', argv)
    elif kind == '20-decoder':
        def load_verify(module: ModuleType, path: Path) -> None:
            # The source09 module itself is still copied unchanged on disk.
            # Its fixed baseline254 table identity assertion remains enabled.
            exec(compile(patched('20-vendor-verify', path), str(path), 'exec'),
                 module.__dict__)
        path = root / 'code/reproduce_decoder255.py'
        sys.path.insert(0, str(root / 'code'))
        execute(path, argv, patched(kind, path), {'intake_load_verify': load_verify})
    elif kind == '20-folds':
        def load_verify(module: ModuleType, path: Path) -> None:
            exec(compile(patched('20-vendor-verify', path), str(path), 'exec'),
                 module.__dict__)
        path = root / 'code/reproduce_decoder255_folds.py'
        source = path.read_text()
        old = '    spec.loader.exec_module(verify)\n'
        assert source.count(old) == 1
        source = source.replace(old, "    intake_load_verify(verify, here / '_source09/verify.py')\n")
        execute(path, argv, source, {'intake_load_verify': load_verify})
    elif kind == '20-epsc':
        path = root / 'code/reproduce_epsc271.py'
        sys.path.insert(0, str(root / 'code'))
        execute(path, argv, patched(kind, path))
    elif kind == '21-full':
        path = root / 'reproduce.py'
        execute(path, argv, patched(kind, path))
    elif kind in ('22-full', '23-full'):
        execute(root / 'reproduce.py', argv)
    else:
        raise ValueError(f'Unknown internal adapter {kind}')


def repository(explicit: Path | None) -> Path:
    candidates = [explicit] if explicit else [*Path.cwd().parents, Path.cwd(),
                                             *Path(__file__).resolve().parents]
    for candidate in candidates:
        if candidate is not None and (candidate / '.git').exists():
            return candidate.resolve()
    raise ValueError('Run inside the ProveIt checkout or supply --repo.')


def main() -> None:
    if not __debug__:
        raise SystemExit('Run without -O/PYTHONOPTIMIZE: functional checks use assertions.')
    if len(sys.argv) > 1 and sys.argv[1] == '_worker':
        worker(sys.argv[2], Path(sys.argv[3]), sys.argv[4:])
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--output', type=Path, help='new or empty scratch directory')
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--run', default='', metavar='20,21,22,23|all',
                        help='optional finite package replays; default is recovery only')
    parser.add_argument('--searches', action='store_true',
                        help='also replay bounded source20 folds and source23 grammar sweeps')
    args = parser.parse_args()
    try:
        selected = set(PACKAGES) if args.run == 'all' else {
            int(s.strip()) for s in args.run.split(',') if s.strip()}
    except ValueError:
        parser.error('--run must be all or a comma-separated list of 20,21,22,23')
    if selected - PACKAGES.keys():
        parser.error('--run source numbers must be 20,21,22,23')
    if args.prepare_only and (selected or args.searches):
        parser.error('--prepare-only cannot be combined with --run/--searches')
    if args.searches:
        selected.update((20, 23))
    repo = repository(args.repo)
    scratch = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-batch150-reproduce-'))
    if args.output:
        scratch.mkdir(parents=True, exist_ok=True)
        if any(scratch.iterdir()):
            raise ValueError('Requested output must be empty; delivered trees are never reused.')
    print(f'Scratch: {scratch}', flush=True)
    roots = {}
    for number, (archive, wrapper, pin) in PACKAGES.items():
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
            raise ValueError(f'Missing expected package wrapper: {wrapper}')
    # Validate every selective in-memory adapter without executing its script.
    for kind, path in {
        '20-decoder': roots[20] / 'code/reproduce_decoder255.py',
        '20-vendor-verify': roots[20] / 'vendor/decoder255/verify.py',
        '20-epsc': roots[20] / 'code/reproduce_epsc271.py',
        '21-full': roots[21] / 'reproduce.py',
    }.items():
        patched(kind, path)
    summary = dict(batch=150, arrival=ARRIVAL, python=sys.version, scratch=str(scratch),
                   packages={str(n): dict(archive=a, wrapper=w, repository_pin=p,
                                          root=str(roots[n])) for n, (a,w,p) in PACKAGES.items()},
                   selected_sources=sorted(selected), searches=args.searches,
                   checksum_manifests_checked=False, bulk_provenance_checks=False,
                   adapters_validated=True, network_used=False,
                   proof_assistant_invoked=False, unbounded_search_run=False, checks=[])
    def save():
        (scratch / 'reproduction.json').write_text(json.dumps(summary, indent=2) + '\n')
    def run(name: str, cwd: Path, command: list[str]):
        start = time.monotonic()
        result = subprocess.run([sys.executable, '-B', *command], cwd=cwd,
                                capture_output=True, text=True)
        log = scratch / f'{name}.log'
        log.write_text(result.stdout + result.stderr)
        summary['checks'].append(dict(check=name, cwd=str(cwd), command=command,
                                     returncode=result.returncode,
                                     seconds=round(time.monotonic()-start, 3), log=str(log)))
        save()
        print(f'{name}: exit {result.returncode}', flush=True)
        if result.returncode:
            print(result.stdout + result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)
    save()
    helper = str(Path(__file__).resolve())
    for number in sorted(selected):
        output = scratch / f'source{number}-output'
        arguments = {20: ['--output', str(output)],
                     21: ['--record', str(scratch / 'source21-replay.json')],
                     22: [], 23: ['--output', str(output)]}[number]
        run(f'{number}-finite', roots[number],
            [helper, '_worker', f'{number}-full', str(roots[number]), *arguments])
    if args.searches:
        run('20-bounded-folds', roots[20],
            [helper, '_worker', '20-folds', str(roots[20]),
             str(scratch / 'source20-output/decoder255')])
        control = roots[23] / 'machine_control'
        run('23-initial960', control,
            ['library_grammar.py', '--search', '--seeds', '40', '--output', str(scratch/'source23-initial960')])
        run('23-targeted6000', control,
            ['library_grammar.py', '--search', '--seeds', '1000', '--families', 'quantifier,variables',
             '--output', str(scratch/'source23-targeted6000')])
    summary['requested_checks_passed'] = True
    save()


if __name__ == '__main__':
    main()
