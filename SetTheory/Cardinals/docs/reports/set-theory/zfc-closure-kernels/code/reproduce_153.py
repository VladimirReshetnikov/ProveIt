"""Recover batch153 archives offline and replay their scoped finite suites.

--prepare-only (the default) recovers both archives into fresh scratch.
--run 35,36|all runs source35's quick suite and source36's default suite.
--extended additionally regenerates all advertised bounded searches.
--lean explicitly adds source35's fresh19-module pinned Lean build.
Only known bulk-manifest checks are omitted in memory. Functional assertions,
table identities and certificate tests remain. No delivered file is patched,
no network is used and Coq is never built.
"""
from __future__ import annotations

import argparse
import ast
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from zipfile import ZipFile

ARRIVAL = '4e720ccbbfaa836b95be3b2f3f268a737b48c6d1'
ARCHIVES = {35: 'zfc_consistency_research_2026-10-16.zip',
            36: 'zfc_small_machine_research_2026-10-16 (2).zip'}


def adapted(script: Path, kind: str, argv: list[str]) -> None:
    tree = ast.parse(script.read_text(), filename=str(script))
    if kind in {'35-quick', '35-lean'}:
        expected = 'code/quick_checks.py' if kind == '35-quick' else 'formal/build.py'
        if not script.as_posix().endswith('/' + expected):
            raise ValueError('Unexpected source35 entrypoint')
        class OmitBulk(ast.NodeTransformer):
            matches = 0
            def visit_For(self, node):
                if ast.unparse(node.iter) == "manifest['sources']":
                    self.matches += 1
                    return ast.copy_location(ast.Pass(), node)
                return self.generic_visit(node)
        adapter = OmitBulk()
        tree = adapter.visit(tree)
        if adapter.matches != 1:
            raise ValueError('Expected exactly one source35 bulk-manifest loop')
    elif kind == '36':
        if not script.as_posix().endswith('/reproduction/reproduce.py'):
            raise ValueError('Unexpected source36 entrypoint')
        matches = 0
        for node in tree.body:
            if isinstance(node, ast.FunctionDef) and node.name == 'verify_files':
                node.body = ast.parse("""assert digest(ROOT / 'zf_audit/zfc_253.tm') == SHA253
assert digest(ROOT / 'experiments/baseline268/candidate.tm') == SHA268
assert digest(ROOT / 'proveit_audit/eout_results/best_complete_proxy.tm') == SHA290
return {'bulk_manifests': 'omitted by intake policy', 'functional_table_pins': 3}
""").body
                matches += 1
        if matches != 1:
            raise ValueError('Expected exactly one source36 manifest function')
    else:
        raise ValueError(kind)
    print('Intake adapter: bulk-manifest checks omitted; functional checks retained.', flush=True)
    ast.fix_missing_locations(tree)
    sys.argv = [str(script), *argv]
    sys.path.insert(0, str(script.parent))
    exec(compile(tree, str(script), 'exec'), {'__name__': '__main__', '__file__': str(script)})


def main() -> None:
    if not __debug__:
        raise SystemExit('Assertions must remain enabled; do not use -O.')
    sys.dont_write_bytecode = True
    if len(sys.argv) > 1 and sys.argv[1] == '_worker':
        adapted(Path(sys.argv[3]).resolve(), sys.argv[2], sys.argv[4:])
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--run', default='')
    parser.add_argument('--extended', action='store_true')
    parser.add_argument('--lean', type=Path, help='explicit pinned Lean4.32 compiler for optional fresh build')
    args = parser.parse_args()
    repo = args.repo.resolve() if args.repo else next(
        p for p in Path(__file__).resolve().parents if (p / '.git').exists())
    try:
        selected = set(ARCHIVES) if args.run == 'all' else {int(x) for x in args.run.split(',') if x}
    except ValueError:
        parser.error('--run expects 35,36 or all')
    if selected - ARCHIVES.keys() or (args.prepare_only and (selected or args.lean)):
        parser.error('Choose sources35/36; --prepare-only excludes execution')
    work = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-batch153-reproduce-'))
    if work.is_relative_to(repo) or (work.exists() and any(work.iterdir())):
        parser.error('Use a new or empty scratch directory outside the checkout')
    work.mkdir(parents=True, exist_ok=True)
    packages = {}
    for number, archive in ARCHIVES.items():
        raw = subprocess.check_output(['git', 'show', f'{ARRIVAL}:docs/incoming/{archive}'], cwd=repo)
        dest = work / str(number)
        with ZipFile(io.BytesIO(raw)) as zipped:
            for member in zipped.infolist():
                if not (dest / member.filename).resolve().is_relative_to(dest.resolve()):
                    raise ValueError('Archive path escapes scratch')
            zipped.extractall(dest)
        children = list(dest.iterdir())
        if len(children) != 1 or not children[0].is_dir():
            raise ValueError('Expected a single package wrapper')
        packages[number] = children[0]
    record = dict(arrival=ARRIVAL, scratch=str(work), packages={str(k): str(v) for k,v in packages.items()},
                  scope='Offline archive recovery and explicitly selected finite checks; no consistency endpoint.', checks=[])
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    environment.pop('PYTHONOPTIMIZE', None)
    helper = str(Path(__file__).resolve())
    def run(name, number, command):
        start = time.monotonic()
        with (work / (name + '.log')).open('w') as log:
            r = subprocess.run(command, cwd=packages[number], env=environment, stdout=log, stderr=subprocess.STDOUT)
        record['checks'].append(dict(name=name, command=command, returncode=r.returncode, seconds=round(time.monotonic()-start,3)))
        (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
        print(name, 'exit', r.returncode, flush=True)
        if r.returncode:
            raise SystemExit(f'{name} failed; inspect {work / (name + ".log")}')
    if 35 in selected:
        p=packages[35]
        run('35-quick',35,[sys.executable,'-B',helper,'_worker','35-quick',str(p/'code/quick_checks.py'),'--output-dir',str(work/'quick35')])
        if args.extended:
            table=str(p/'machines/zfc_253.tm')
            for radius in (6,7):
                run(f'35-radius{radius}',35,[sys.executable,'-B',str(p/'optimization/edge_replacement_search.py'),table,'--radius',str(radius),'--steps','128','--output',str(work/f'r{radius}.json')])
            run('35-staged',35,[sys.executable,'-B',str(p/'optimization/staged_replacement_search.py'),table,str(work/'r6.json'),'--output',str(work/'staged.json')])
            run('35-ledger',35,[sys.executable,'-B',str(p/'optimization/verify_edge_evidence.py'),table,str(work/'r6.json'),'--output',str(work/'r6-verified.json')])
            run('35-shortgap',35,[sys.executable,'-B',str(p/'notes/runtime252_short_gap.py'),'--upstream',str(p/'vendor/busy-beaver'),'--limit','1000000','--output',str(work/'shortgap.json')])
    if 36 in selected:
        command=[sys.executable,'-B',helper,'_worker','36',str(packages[36]/'reproduction/reproduce.py'),'--output',str(work/'replay36')]
        if args.extended:command.append('--extended')
        run('36-replay',36,command)
    if args.lean:
        run('35-lean',35,[sys.executable,'-B',helper,'_worker','35-lean',str(packages[35]/'formal/build.py'),'--lean',str(args.lean.resolve()),'--build-dir',str(work/'lean-build')])
    (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    print('Evidence:',work,flush=True)


if __name__ == '__main__':
    main()
