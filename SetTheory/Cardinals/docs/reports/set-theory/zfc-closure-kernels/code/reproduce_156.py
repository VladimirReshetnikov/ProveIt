"""Recover batch156 offline and replay selected functional suites on fresh copies.

The default (or --prepare-only) recovers sources47–49 from their arrival Git
commit and writes recovered-paths.json linking delivered paths to their flat
repository locations. --run 47,48,49|all selects the finite default suites.
--compiler-controls adds source47's full32-seed compiler controls; --extended
also reruns its166,413 incoming-action recipes and the advertised full searches
of sources48/49. These optional jobs can take several minutes and need g++ for
source49. No network, Lean or Coq is used. Known bulk release-manifest checks
are omitted, while functional table/source identities and assertions remain.
No delivered file is patched. Run without Python optimization.
"""
from __future__ import annotations

import argparse
import ast
import gzip
import io
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from zipfile import ZipFile

ARRIVAL = '2447a98214b1c4a3e24e51ee654439fbcfa002d9'
HOST = Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels')
PACKAGES = {
    47: ('zfc_consistency_252_research_20261017.zip', 'zfc_consistency_252_research', 'cofinal', 174),
    48: ('zfc_consistency_research_20261017.zip', 'zfc_consistency_research_20261017', 'sparse', 70),
    49: ('zfc_reset_hod_research_2026-10-17.zip', 'zfc_reset_hod_research', 'reset', 69),
}
CODE_SUFFIXES = {'.py', '.sh', '.ps1', '.wl', '.wls', '.lean', '.cpp', '.c', '.h', '.v', '.patch'}
SOURCE47_RELEASE_ASSERTIONS = {
    "digest(ROOT / 'data/incoming_action_results.json') == manifest['results_sha256']",
    "digest(ROOT / 'code/incoming_action_search.py') == manifest['driver_sha256']",
    "digest(archive) == manifest['journal_compressed_sha256']",
    "archive.stat().st_size == manifest['journal_compressed_bytes']",
    "hasher.hexdigest() == manifest['journal_uncompressed_sha256']",
    "byte_count == manifest['journal_uncompressed_bytes']",
}


def source47_functional(package: Path, output: Path) -> None:
    """Run the delivered finite verifier, excluding only named bulk release checks."""
    if not __debug__:
        raise RuntimeError('Keep Python assertions enabled.')
    script = package / 'code/verify.py'
    tree = ast.parse(script.read_text(), filename=str(script))
    sources = 0
    search_functions = 0
    skipped = []
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name == 'check_sources':
            sources += 1
            node.body = ast.parse("return {'status': 'omitted by intake instruction', 'reference_files_checked': 0, 'vendor_blobs_checked': 0}").body
        if isinstance(node, ast.FunctionDef) and node.name == 'check_search_record':
            search_functions += 1
            kept = []
            for statement in node.body:
                expression = ast.unparse(statement.test) if isinstance(statement, ast.Assert) else None
                if expression in SOURCE47_RELEASE_ASSERTIONS:
                    skipped.append(expression)
                else:
                    kept.append(statement)
            node.body = kept
    if sources != 1 or search_functions != 1 or len(skipped) != 6 or set(skipped) != SOURCE47_RELEASE_ASSERTIONS:
        raise ValueError('Unexpected source47 verifier; review the adapter before use.')
    namespace = {'__name__': 'intake_source47_functional', '__file__': str(script)}
    exec(compile(ast.fix_missing_locations(tree), str(script), 'exec'), namespace)
    result = {
        'reference_machine': namespace['check_reference_machine'](),
        'bulk_source_manifests': namespace['check_sources'](),
        'logical_diagnostics': namespace['check_logical_diagnostics'](),
        'search_journal_semantics': namespace['check_search_record'](),
        'compiler_table_records': namespace['check_compiler_records'](),
        'adapter': {'check_sources_omitted': True, 'release_assertions_omitted': skipped,
                    'functional_table_and_source_identity_assertions_retained': True},
        'scope': 'Finite bootstrap, syntax and delivered-record replay; affine search and compiler are not re-executed in this default suite. No Lean/Coq build or consistency proof execution.',
        'status': 'PASS',
    }
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


def source47_compiler_comparison(package: Path, fresh: Path, output: Path) -> None:
    delivered = package / 'experiments/cofinal_gate'
    new = json.loads((fresh / 'results.json').read_text())
    old = json.loads((delivered / 'results.json').read_text())
    assert new == old, 'Compiler results differ from delivery.'
    exact = []
    for directory in ('original', 'cofinal_general/unshared', 'cofinal_general/best',
                      'cofinal_fixed_cg/unshared', 'cofinal_fixed_cg/best'):
        for name in ('machine.tm', 'dag.json', 'labels.json'):
            relative = Path(directory) / name
            assert (fresh / relative).read_bytes() == (delivered / relative).read_bytes(), relative
            exact.append(relative.as_posix())
    output.write_text(json.dumps({'status': 'PASS', 'all_results_json_exact': True,
                                 'selected_artifacts_byte_exact': exact, 'count': len(exact),
                                 'scope': 'Recompilation of32 deterministic seeds per variant; uncalibrated compiler controls, no new machine endpoint.'}, indent=2) + '\n')


def source47_search_comparison(package: Path, fresh: Path, output: Path) -> None:
    actual = json.loads((fresh / 'results.json').read_text())
    old = json.loads((package / 'data/incoming_action_results.json').read_text())
    metadata = {'command', 'elapsed_seconds', 'python', 'recipe_journal', 'scratch', 'search_wall_seconds_limit'}
    assert {k: v for k, v in actual.items() if k not in metadata} == {k: v for k, v in old.items() if k not in metadata}
    assert actual['status'] == 'completed' and actual['completed_recipes'] == 166413
    count = byte_count = 0
    with (fresh / 'recipes.jsonl').open('rb') as new, gzip.open(package / 'data/incoming_action_journal.jsonl.gz', 'rb') as recorded:
        for a, b in itertools.zip_longest(new, recorded):
            assert a is not None and a == b, f'Journal differs at recipe{count}.'
            count += 1
            byte_count += len(a)
    assert count == 166413
    output.write_text(json.dumps({'status': 'PASS', 'functional_summary_exact': True,
                                 'metadata_keys_ignored': sorted(metadata),
                                 'journal_rows_byte_exact': count, 'uncompressed_bytes': byte_count,
                                 'affine_checks': actual['affine_checks'],
                                 'scope': 'Full bounded re-execution and exact recipe comparison; no impossibility/lower-bound theorem or altered unbounded machine certificate.'}, indent=2) + '\n')


def worker(kind: str, package: Path, argv: list[str]) -> None:
    if not __debug__:
        raise RuntimeError('Keep Python assertions enabled.')
    if kind == '47':
        if len(argv) != 1:
            raise ValueError('Expected source47 output path.')
        source47_functional(package, Path(argv[0]).resolve())
    elif kind in {'47-compiler-compare', '47-search-compare'}:
        if len(argv) != 2:
            raise ValueError('Expected fresh results and comparison output paths.')
        fn = source47_compiler_comparison if kind == '47-compiler-compare' else source47_search_comparison
        fn(package, Path(argv[0]).resolve(), Path(argv[1]).resolve())
    else:
        raise ValueError(kind)


def hosted_target(number: int, relative: Path) -> Path | None:
    """Reconstruct the batch156 placement rule; this does not verify manifests."""
    if relative.suffix.lower() in {'.tex', '.pdf', '.bib'} or (len(relative.parts) == 1 and relative.name in {'README.md', 'README.txt'}):
        return None
    flat = relative.as_posix().replace('vendor/proveit/', 'v/')
    for before, after in (
        ('Computability/BusyBeaver/Research/ZFC/', 'research/'),
        ('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/', 'lean/'),
        ('lib/jeff-busy-beaver-zfc254/', 'upstream/'),
        ('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/', 'host/')):
        flat = flat.replace(before, after)
    flat = flat.replace('/', '-')
    if relative.suffix == '.log':
        flat += '.txt'
    folder = 'code' if relative.suffix.lower() in CODE_SUFFIXES or relative.name == 'Makefile' else 'data'
    if relative.suffix.lower() == '.md' or relative.name.startswith('LICENSE') or relative.name == 'NOTICE':
        folder = ''
    return HOST / folder / f'{number:02}-{PACKAGES[number][2]}-{flat}'


def recover(repo: Path, work: Path) -> tuple[dict[int, Path], dict]:
    packages, rows, targets = {}, [], set()
    for number, (archive, wrapper, _, expected_count) in PACKAGES.items():
        archive_path = 'docs/incoming/' + archive
        raw = subprocess.check_output(['git', 'show', f'{ARRIVAL}:{archive_path}'], cwd=repo)
        destination = work / str(number)
        with ZipFile(io.BytesIO(raw)) as zipped:
            for member in zipped.infolist():
                if '\\' in member.filename or not (destination / member.filename).resolve().is_relative_to(destination.resolve()):
                    raise ValueError('Archive path escapes scratch.')
                if ((member.external_attr >> 16) & 0o170000) == 0o120000:
                    raise ValueError('Archive symlink rejected.')
            zipped.extractall(destination)
        children = list(destination.iterdir())
        package = destination / wrapper
        if len(children) != 1 or not package.is_dir():
            raise ValueError('Unexpected package wrapper.')
        files = sorted(p for p in package.rglob('*') if p.is_file())
        if len(files) != expected_count:
            raise ValueError(f'Unexpected source{number} file count.')
        packages[number] = package
        for path in files:
            relative = path.relative_to(package)
            target = hosted_target(number, relative)
            if target is not None:
                key = target.as_posix().lower()
                if key in targets:
                    raise ValueError('Flattened target collision.')
                targets.add(key)
            rows.append({'local_source': number, 'archive': archive_path,
                         'delivered': relative.as_posix(), 'recovered': str(path),
                         'target': target.as_posix() if target is not None else None,
                         'placement': 'hosted ancillary' if target is not None else 'archive only'})
    mapping = {'batch': 156, 'arrival': ARRIVAL, 'files': rows,
               'scope': 'Deterministic delivery-to-host path reconstruction only. Recovered bytes come from committed ZIPs; no bulk checksum manifest or staged-byte verification is performed.',
               'counts': {str(n): {'files': sum(r['local_source'] == n for r in rows),
                                  'staged': sum(r['local_source'] == n and r['target'] is not None for r in rows),
                                  'archive_only': sum(r['local_source'] == n and r['target'] is None for r in rows)} for n in PACKAGES}}
    (work / 'recovered-paths.json').write_text(json.dumps(mapping, indent=2) + '\n')
    return packages, mapping


def main() -> None:
    if not __debug__:
        raise SystemExit('Assertions must remain enabled; do not use -O.')
    sys.dont_write_bytecode = True
    if len(sys.argv) > 1 and sys.argv[1] == '_worker':
        return worker(sys.argv[2], Path(sys.argv[3]).resolve(), sys.argv[4:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--run', default='')
    parser.add_argument('--compiler-controls', action='store_true')
    parser.add_argument('--extended', action='store_true')
    parser.add_argument('--search-seconds', type=float, default=600,
                        help='source47 full search wall bound; a partial run is a failure, not a completed replay')
    args = parser.parse_args()
    repo = args.repo.resolve() if args.repo else next((p for p in Path(__file__).resolve().parents if (p / '.git').exists()), None)
    if repo is None:
        parser.error('Pass --repo when this helper is outside the checkout.')
    try:
        selected = set(PACKAGES) if args.run == 'all' else {int(x) for x in args.run.split(',') if x}
    except ValueError:
        parser.error('--run expects47,48,49 or all.')
    if selected - PACKAGES.keys() or (args.prepare_only and selected):
        parser.error('Choose sources47–49, or --prepare-only without --run.')
    if (args.extended or args.compiler_controls) and not selected:
        parser.error('Optional replays require --run.')
    if args.compiler_controls and 47 not in selected:
        parser.error('--compiler-controls requires source47 selected.')
    if args.search_seconds <= 0:
        parser.error('--search-seconds must be positive.')
    work = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-batch156-reproduce-'))
    if work == repo or work.is_relative_to(repo) or (work.exists() and any(work.iterdir())):
        parser.error('Use a new or empty scratch directory outside the checkout.')
    work.mkdir(parents=True, exist_ok=True)
    packages, mapping = recover(repo, work)
    record = {'batch': 156, 'arrival': ARRIVAL, 'scratch': str(work),
              'packages': {str(k): str(v) for k, v in packages.items()},
              'recovered_path_map': str(work / 'recovered-paths.json'),
              'recovery_counts': mapping['counts'], 'checks': [],
              'scope': 'Offline recovery and explicitly selected finite functional replays; not execution of an unbounded consistency proof or a fresh formal build.',
              'bulk_manifests': {'47': 'check_sources and exactly six release assertions omitted in memory; functional table/source pins retained',
                                 '48': 'native --skip-manifest option',
                                 '49': 'no bulk-manifest loop in advertised driver; all functional guards retained'},
              'Lean_built': False, 'Coq_built': False}
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    environment.pop('PYTHONOPTIMIZE', None)
    helper = str(Path(__file__).resolve())
    def run(name: str, number: int, command: list[str]) -> None:
        start = time.monotonic()
        log = work / (name + '.log')
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=packages[number], env=environment, stdout=stream, stderr=subprocess.STDOUT)
        record['checks'].append({'name': name, 'source': number, 'command': command,
                                 'returncode': result.returncode, 'seconds': round(time.monotonic() - start, 3),
                                 'log': str(log)})
        (work / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
        print(name, 'exit', result.returncode, flush=True)
        if result.returncode:
            raise SystemExit(f'{name} failed; inspect {log}.')
    if 47 in selected:
        package = packages[47]
        run('47-default', 47, [sys.executable, '-B', helper, '_worker', '47', str(package), str(work / 'source47.json')])
        if args.compiler_controls or args.extended:
            fresh = work / 'source47-compiler'
            run('47-compiler', 47, [sys.executable, '-B', str(package / 'code/cofinal_gate_cost.py'), '--repo', str(package / 'vendor/proveit'), '--output', str(fresh), '--seeds', '32'])
            run('47-compiler-compare', 47, [sys.executable, '-B', helper, '_worker', '47-compiler-compare', str(package), str(fresh), str(work / 'source47-compiler-comparison.json')])
        if args.extended:
            fresh = work / 'source47-search'
            run('47-search', 47, [sys.executable, '-B', str(package / 'code/incoming_action_search.py'), '--repo', str(package / 'vendor/proveit'), '--output', str(fresh / 'results.json'), '--scratch', str(fresh), '--seconds', str(args.search_seconds), '--affine-fuel', '1000'])
            run('47-search-compare', 47, [sys.executable, '-B', helper, '_worker', '47-search-compare', str(package), str(fresh), str(work / 'source47-search-comparison.json')])
    if 48 in selected:
        command = [sys.executable, '-B', str(packages[48] / 'reproduce.py'), '--skip-manifest', '--output', str(work / 'source48.json')]
        if args.extended:
            command.append('--full-searches')
        run('48-replay', 48, command)
    if 49 in selected:
        command = [sys.executable, '-B', str(packages[49] / 'code/verify_bundle.py')]
        if args.extended:
            command.append('--full')
        run('49-replay', 49, command)
    record['status'] = 'PASS'
    (work / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('Evidence:', work, flush=True)


if __name__ == '__main__':
    main()
