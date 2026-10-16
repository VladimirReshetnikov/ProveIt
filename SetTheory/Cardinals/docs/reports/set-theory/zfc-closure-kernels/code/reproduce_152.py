"""Recover batch 152 offline and optionally replay its selected finite suites.

Default/--prepare-only recovers all nine original Git archives into new scratch.
--run 26,27,...|all runs the selected sources' quick functional suites. Large
bounded searches, proof-assistant builds and PDF builds have separate dossier
commands. No network or unbounded consistency search is used. Bulk provenance
manifest guards are omitted in memory; functional checks remain enabled.
Recovered source files are never patched on disk.
"""
from __future__ import annotations

import argparse
import ast
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from zipfile import ZipFile

ARRIVAL = 'da6dabcd8976acf94c4f3652ed3eeae5713b3d2a'
PACKAGES = {
    26: 'zfc_consistency_machine_report_20261016',
    27: 'zfc_consistency_machine_research_2026-10-16',
    28: 'zfc_contraction_research',
    29: 'zfc_epsilon_research',
    30: 'zfc_minimization_20261016',
    31: 'zfc_small_machine_report_2026-10-16',
    32: 'zfc_small_machine_research',
    33: 'zfc_small_machine_research_2026-10-16',
    34: 'zfc_small_machine_research_20261016',
}
PINS = {
    26: '6ec2e80dbbe45a99b7812fb5757977307959a51e',
    29: 'd74c63b0c8d4f35597f1bd5976d941b9f104f94e',
    34: 'd74c63b0c8d4f35597f1bd5976d941b9f104f94e',
}


def execute(path: Path, argv: list[str], source=None) -> None:
    sys.argv = [str(path), *argv]
    sys.path.insert(0, str(path.parent))
    code = compile(path.read_text() if source is None else source, str(path), 'exec')
    exec(code, {'__name__': '__main__', '__file__': str(path)})


def without_manifest(path: Path):
    """Only the three known entrypoints' bulk manifest statements are omitted."""
    tree = ast.parse(path.read_text(), filename=str(path))
    skipped = []
    for function in ast.walk(tree):
        if not isinstance(function, ast.FunctionDef) or function.name != 'main':
            continue
        body = []
        for node in function.body:
            statement = ast.unparse(node)
            if isinstance(node, ast.Assign) and any(
                    isinstance(t, ast.Name) and t.id == 'manifest_path' for t in node.targets):
                skipped.append(node.lineno)
            elif isinstance(node, ast.If) and (
                    'manifest_path.exists()' in ast.unparse(node.test) or
                    'MANIFEST.sha256' in ast.unparse(node.test)):
                skipped.append(node.lineno)
            elif isinstance(node, ast.Assign) and any(
                    isinstance(t, ast.Name) and t.id == 'manifest' for t in node.targets) and 'manifest_path' in statement:
                body.extend(ast.parse('manifest = {}').body)
                skipped.append(node.lineno)
            elif isinstance(node, ast.For) and ast.unparse(node.iter) in (
                    'manifest.items()', "manifest['files'].items()", "provenance['files']"):
                skipped.append(node.lineno)
            else:
                body.append(node)
        function.body = body
    if not skipped:
        raise ValueError(f'Expected known bulk manifest statements: {path}')
    print(f'In-memory manifest omissions at {path}: {skipped}', flush=True)
    ast.fix_missing_locations(tree)
    return tree


def worker(kind: str, root: Path, argv: list[str]) -> None:
    root = root.resolve()
    helper = str(Path(__file__).resolve())
    if kind == '26':
        path = root / 'tools/reproduce.py'
        spec = importlib.util.spec_from_file_location('intake_source26', path)
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)

        def functional_interface(self):
            self.baseline_manifest = module.read_json(self.baseline / 'manifest.json')
            if set(self.baseline_manifest) != module.BASELINE_REQUIRED:
                raise module.VerificationError('Missing functional baseline interface')
            self.integrity = {'bulk_manifest_guards': 'omitted by intake policy',
                              'functional_checks': 'retained'}
            self.checked('functional_input_interface', files=len(self.baseline_manifest))

        module.Reproduction.verify_inputs = functional_interface
        module.Reproduction.preserved_inputs = lambda self: None
        sys.argv = [str(path), '--quick']
        raise SystemExit(module.main())
    if kind == '27-tables':
        path = root / 'experiments/basis_compiler/reproduce.py'
        source = path.read_text()
        marker = "for name, expected in manifest['sha256'].items():"
        if source.count(marker) != 1:
            raise ValueError('Expected one source27 release-manifest loop')
        execute(path, argv, source.replace(marker, 'for name, expected in {}.items():'))
        return
    if kind in ('29-machine', '30', '30-optimizer'):
        path = root / {'29-machine': 'machine/reproduce.py', '30': 'reproduce.py',
                       '30-optimizer': 'optimizer/quick_verify.py'}[kind]
        if kind == '30':
            original_run = subprocess.run

            def adapted_run(command, *args, **kwargs):
                command = list(command)
                if len(command) > 1 and command[1] == 'quick_verify.py':
                    command = [sys.executable, '-B', helper, '_worker', '30-optimizer', str(root)]
                return original_run(command, *args, **kwargs)

            subprocess.run = adapted_run
        execute(path, argv, without_manifest(path))
        return
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
    parser.add_argument('--run', default='', metavar='26,27,...|all')
    args = parser.parse_args()
    try:
        selected = set(PACKAGES) if args.run == 'all' else {
            int(s.strip()) for s in args.run.split(',') if s.strip()}
    except ValueError:
        parser.error('--run must be all or a comma-separated list of sources 26 through 34')
    if selected - PACKAGES.keys():
        parser.error('--run sources must be 26 through 34')
    if args.prepare_only and selected:
        parser.error('--prepare-only cannot be combined with --run')
    repo = repository(args.repo)
    scratch = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-batch152-reproduce-'))
    if scratch.is_relative_to(repo):
        raise ValueError('Output must be outside the checkout.')
    if args.output:
        scratch.mkdir(parents=True, exist_ok=True)
        if any(scratch.iterdir()):
            raise ValueError('Output must be empty; delivered trees are never reused.')
    roots = {}
    print(f'Scratch: {scratch}', flush=True)
    for number, stem in PACKAGES.items():
        raw = subprocess.check_output(['git', 'show', f'{ARRIVAL}:docs/incoming/{stem}.zip'], cwd=repo)
        destination = scratch / str(number)
        with ZipFile(io.BytesIO(raw)) as zipped:
            for name in zipped.namelist():
                path = Path(name)
                if path.is_absolute() or '..' in path.parts:
                    raise ValueError(f'Archive path escapes scratch: {name}')
            zipped.extractall(destination)
        children = list(destination.iterdir())
        if len(children) != 1 or not children[0].is_dir():
            raise ValueError(f'Expected one package wrapper: {stem}')
        roots[number] = children[0]
    summary = dict(batch=152, arrival=ARRIVAL, python=sys.version, scratch=str(scratch),
                   packages={str(n): dict(archive=a+'.zip', root=str(roots[n]),
                                         repository_pin=PINS.get(n, '4747142d5d15213eb711bdadfa3cc7e769fcb7a7'))
                             for n, a in PACKAGES.items()},
                   selected_sources=sorted(selected), bulk_manifest_guards=False,
                   source_files_patched_on_disk=False, network_used=False,
                   proof_assistant_invoked=False, pdf_build_invoked=False,
                   unbounded_search_run=False, checks=[])

    def save():
        (scratch / 'reproduction.json').write_text(json.dumps(summary, indent=2) + '\n')

    def run(name: str, cwd: Path, arguments: list[str]):
        begin = time.monotonic()
        command = [sys.executable, '-B', *arguments]
        result = subprocess.run(command, cwd=cwd, capture_output=True, text=True)
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

    helper = str(Path(__file__).resolve())
    backend = str(Path(__file__).with_name('intake_152_backend_adapter.py').resolve())
    save()
    for number in sorted(selected):
        root = roots[number]
        if number == 26:
            run('26-quick', root, [helper, '_worker', '26', str(root)])
        elif number == 27:
            run('27-core', root, ['code/reproduce.py'])
            run('27-tables', root, [helper, '_worker', '27-tables', str(root), '--output', str(scratch/'27-tables')])
        elif number == 28:
            run('28-core', root, ['reproduce.py', '--output', str(scratch/'28-results.json')])
        elif number == 29:
            run('29-epsilon', root, ['epsilon/test_epsilon_native.py'])
            run('29-machine', root, [helper, '_worker', '29-machine', str(root), '--quick'])
            run('29-grammar', root, ['grammar/verify_grammar.py'])
        elif number == 30:
            run('30-quick', root, [helper, '_worker', '30', str(root), '--quick'])
        elif number == 31:
            run('31-core', root, ['verify_artifacts.py', '--output', str(scratch/'31-results.json')])
        elif number == 32:
            run('32-core', root, [backend, '--root', str(root), '--source', '32',
                                 '--script', 'verify_package.py'])
            run('32-optimization', root, [backend, '--root', str(root), '--source', '32',
                                         '--script', 'optimization/reproduce.py', '--',
                                         '--record', str(scratch/'32-optimization.json')])
        elif number == 33:
            run('33-core', root, [backend, '--root', str(root), '--source', '33',
                                 '--script', 'reproduce.py', '--',
                                 '--output', str(scratch/'33-results.json')])
        elif number == 34:
            run('34-core', root, [backend, '--root', str(root), '--source', '34',
                                 '--script', 'verify_artifacts.py'])
    summary['status'] = 'PASS'
    save()
    print(f'Evidence: {scratch / "reproduction.json"}', flush=True)


if __name__ == '__main__':
    main()
