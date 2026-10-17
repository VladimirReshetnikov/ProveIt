"""Check only the IOpen Cantor package and its stored audit, serially.

This checker is separate from the Std-only check_lean.py/umbrella. It requires
an existing full ProveIt dependency checkout with built Foundation/Mathlib,
and a successful core integration JSON with matching Code254 source hashes.
No dependency is rebuilt, installed, downloaded or updated. Existing .lake
library directories are discovered read-only from lake-manifest.json, or may
be supplied in order with repeated --library-path. Cached dependencies are
explicitly reused; only ArithmeticCantor and its audit are freshly checked.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

TOOLCHAIN = 'leanprover/lean4:v4.32.0'
FOUNDATION_PIN = '32e1a0956a8622fad067328ca1959729a7634428'
SOURCE = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCantor.lean')
MODULE = 'BusyBeaver.ZFC.ArithmeticCantor'
PREFIX = 'SetTheory.BusyBeaver.ZFC.ArithmeticCantor.'
PROBES = (
    'triangle_double', 'triangle_succ', 'triangle_mono', 'le_triangle',
    'cantor_double', 'cantor_graph', 'components_le', 'diagonal_lt',
    'cantor_injective', 'diagonal_exists', 'cantor_surjective',
    'projections_spec', 'cantor_projections', 'first_cantor', 'second_cantor',
    'cantor_defined', 'first_defined', 'second_defined', 'triangle_nat',
    'cantor_nat', 'projections_nat', 'first_nat', 'second_nat',
    'codeP_defined', 'codeFirst_defined', 'codeSecond_defined', 'codeP_graph',
)
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True).strip()


def fail(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def lean_imports(text: str) -> list[str]:
    """Read the simple header imports used by the evidence's project modules.

    Nested block comments and line comments are removed. Only ordinary single
    line import commands are supported; an unfamiliar command fails closed.
    """
    cleaned = []
    depth = i = 0
    while i < len(text):
        pair = text[i:i+2]
        if pair == '/-':
            depth += 1; i += 2
        elif pair == '-/' and depth:
            depth -= 1; i += 2
        elif depth:
            if text[i] == '\n':
                cleaned.append('\n')
            i += 1
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            cleaned.append(text[i]); i += 1
    fail(depth == 0, 'Unclosed project-source block comment.')
    imports = []
    for line in ''.join(cleaned).splitlines():
        match = re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*$', line)
        if match:
            names = match.group(1).split()
            fail(all(re.fullmatch(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*', n) for n in names),
                 'Unsupported project import syntax; review before reusing its object.')
            imports.extend(names)
    return imports


def core_closure(repo: Path, evidence_path: Path, cache_override: Path | None) -> tuple[list[dict], dict]:
    evidence = json.loads(evidence_path.read_text())
    fail(str(evidence.get('status', '')).startswith('PASS'), 'Core evidence is not a successful integration.')
    fail(evidence.get('all_source_identities_unchanged_after_check') is True,
         'Core evidence does not record its post-check source identity audit.')
    fail(evidence.get('audit', {}).get('exit_code') == 0, 'Core evidence audit did not pass.')
    checks = evidence.get('fresh_checks')
    fail(isinstance(checks, list) and bool(checks) and all(row.get('exit_code') == 0 for row in checks),
         'Core evidence needs successful recorded fresh checks.')
    fail(isinstance(evidence.get('source_closure'), list) and evidence['source_closure'],
         'Expected source_closure integration evidence (for example161 or163).')
    modules = {}
    for row in evidence['source_closure']:
        path = Path(row['path'])
        fail(path.suffix == '.lean', 'Core source_closure entries must be Lean sources.')
        fail(not path.is_absolute() and '..' not in path.parts, 'Unsafe core-evidence source path.')
        if '/Lean/' not in path.as_posix():
            continue
        relative = path.as_posix().split('/Lean/', 1)[1]
        name = relative.removesuffix('.lean').replace('/', '.')
        fail(name not in modules, f'Duplicate core module: {name}')
        modules[name] = row
    cache = cache_override.resolve() if cache_override else Path(evidence.get('cache', '')).resolve()
    fail(cache.is_dir(), 'Recorded core cache is unavailable; pass --core-cache for a relocated matching cache.')
    required, visiting = {}, set()
    def visit(name: str) -> None:
        if name in required:
            return
        fail(name not in visiting, f'Project import cycle: {name}')
        fail(name in modules, f'Module absent from successful source evidence: {name}')
        visiting.add(name)
        row = modules[name]
        source = repo / row['path']
        fail(source.is_file() and digest(source) == row['sha256'], f'Core source differs from checked evidence: {source}')
        for imported in lean_imports(source.read_text()):
            if imported in modules:
                visit(imported)
            else:
                # Code254's current project closure has no external library import.
                # Do not silently weaken this boundary for changed source.
                fail(imported in {'Init', 'Std', 'Lean'} or imported.startswith(('Init.', 'Std.', 'Lean.')),
                     f'Unexpected external import in Code254 closure: {imported}')
        relative = Path(name.replace('.', '/')).with_suffix('.olean')
        obj = cache / relative
        fail(obj.is_file(), f'Core object missing; build its core closure separately: {obj}')
        required[name] = dict(module=name, path=row['path'], source_sha256=row['sha256'],
                              olean=str(obj.resolve()), olean_sha256=digest(obj),
                              prior_validation=row.get('validation'), prior_evidence=row.get('evidence'))
        visiting.remove(name)
    visit('BusyBeaver.ZFC.Code254')
    return list(required.values()), dict(path=str(evidence_path), sha256=digest(evidence_path),
                                         status=evidence['status'], units=evidence.get('units'),
                                         cache=str(cache), cache_relocated=cache_override is not None,
                                         scope='Only the actual Code254 transitive project-source closure is reused. No fresh core/dependency rebuild is asserted.')


def dependency_libraries(root: Path, supplied: list[Path]) -> tuple[list[Path], dict]:
    foundation = root / 'lib/FormalizedFormalLogic-Foundation'
    fail(foundation.is_dir(), 'Dependency root lacks lib/FormalizedFormalLogic-Foundation.')
    fail(git(foundation, 'rev-parse', 'HEAD') == FOUNDATION_PIN, 'Foundation is not at the required pin.')
    fail(not git(foundation, 'status', '--porcelain', '--untracked-files=no'),
         'Foundation tracked source is dirty; provide the pinned clean dependency checkout.')
    manifest_path = root / 'lake-manifest.json'
    fail(manifest_path.is_file(), 'Dependency root needs its existing lake-manifest.json.')
    manifest = json.loads(manifest_path.read_text())
    package_dir = (root / manifest.get('packagesDir', '.lake/packages')).resolve()
    mathlib_rows = [p for p in manifest['packages'] if p['name'] == 'mathlib']
    fail(len(mathlib_rows) == 1, 'Dependency manifest must identify one Mathlib package.')
    mathlib_row = mathlib_rows[0]
    mathlib = package_dir / 'mathlib'
    fail(mathlib.is_dir(), 'Mathlib is missing; this checker never fetches it.')
    mathlib_pin = git(mathlib, 'rev-parse', 'HEAD')
    fail(mathlib_pin == mathlib_row['rev'], 'Mathlib checkout differs from its existing dependency manifest.')
    fail(not git(mathlib, 'status', '--porcelain', '--untracked-files=no'),
         'Mathlib tracked source is dirty; supply the existing clean built checkout.')
    if supplied:
        candidates = [p.resolve() for p in supplied]
        method = 'explicit ordered --library-path arguments'
    else:
        # Reading built directories avoids Lake config elaboration or package loading.
        candidates = [package_dir/p['name']/'.lake/build/lib/lean' for p in manifest['packages']]
        candidates.append(root/'.lake/build/lib/lean')
        candidates = [p.resolve() for p in candidates if p.is_dir()]
        method = 'read-only lake-manifest.json and existing .lake build directories; no Lake process'
    libraries = list(dict.fromkeys(candidates))
    fail(libraries and all(p.is_dir() for p in libraries), 'Every library path must already be a built directory.')
    providers = {}
    for module in ('Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Mathlib.Tactic.Ring'):
        relative = Path(module.replace('.', '/')).with_suffix('.olean')
        found = next((p/relative for p in libraries if (p/relative).is_file()), None)
        fail(found is not None, f'Missing prebuilt {module}; provide --library-path, without rebuilding here.')
        providers[module] = dict(path=str(found), sha256=digest(found))
    return libraries, dict(root=str(root), Foundation=dict(path=str(foundation), pin=FOUNDATION_PIN, tracked_clean=True),
                           Mathlib=dict(path=str(mathlib), pin=mathlib_pin, input_revision=mathlib_row.get('inputRev'), tracked_clean=True),
                           lake_manifest_sha256=digest(manifest_path), discovery=method,
                           providers=providers, cached_objects_reused=True, dependency_rebuild=False,
                           cache_provenance='Existing built checkout is supplied by the caller; the checker records object identities but does not rebuild or independently attest the whole dependency cache.')


def compiler_path(requested: Path | None) -> tuple[Path, str]:
    if requested:
        compiler = requested.expanduser().resolve()
    else:
        elan = Path(os.environ.get('ELAN_HOME', str(Path.home()/'.elan')))
        compiler = (elan/'toolchains/leanprover--lean4---v4.32.0/bin'/('lean.exe' if os.name == 'nt' else 'lean')).resolve()
    fail(compiler.is_absolute() and compiler.is_file(), 'Pass --lean with the real existing pinned4.32.0 compiler executable.')
    fail(compiler.name.lower() not in {'elan', 'elan.exe'}, 'Pass the real cached compiler, not an elan installation shim.')
    version = subprocess.check_output([str(compiler), '--version'], text=True).strip()
    fail(re.match(r'Lean \(version 4\.32\.0(?:,|\))', version) is not None, f'Wrong Lean version: {version}')
    return compiler, version


def audit_axioms(output: str) -> list[dict]:
    pattern = r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    probes = []
    for name, block in re.findall(pattern, output, re.S):
        axioms = [a.strip() for a in block.split(',') if a.strip()]
        fail(set(axioms) <= STANDARD_AXIOMS, f'Unexpected axioms for {name}: {axioms}')
        probes.append(dict(theorem=name, axioms=axioms))
    fail(len(probes) == len(PROBES) and {p['theorem'] for p in probes} == {PREFIX+n for n in PROBES},
         'Missing, duplicate or unexpected arithmetic axiom report.')
    return probes


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path)
    p.add_argument('--dependency-root', type=Path, required=True)
    p.add_argument('--core-evidence', type=Path, required=True)
    p.add_argument('--core-cache', type=Path, help='relocated source-matched cache when the JSON\'s cache location is unavailable')
    p.add_argument('--library-path', type=Path, action='append', default=[])
    p.add_argument('--lean', type=Path, help='real existing absolute4.32.0 compiler; no shim or installation')
    p.add_argument('--source', type=Path, help='candidate source override; normally the maintained ArithmeticCantor.lean')
    p.add_argument('--audit', type=Path, help='stored caller/axiom audit override')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    if not __debug__:
        p.error('Keep assertions enabled; do not use -O.')
    repo = a.repo.resolve() if a.repo else next((q for q in Path(__file__).resolve().parents if (q/'.git').exists()), None)
    if repo is None:
        p.error('Pass --repo when running outside the checkout.')
    root = a.dependency_root.resolve()
    source = a.source.resolve() if a.source else repo/SOURCE
    audit = a.audit.resolve() if a.audit else Path(__file__).with_name('arithmetic_cantor_audit.lean')
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-arithmetic-cantor-check-'))
    if any(work.is_relative_to(q) for q in (repo, root)) or (work.exists() and any(work.iterdir())):
        p.error('Use new/empty scratch outside both the source and dependency checkouts.')
    work.mkdir(parents=True, exist_ok=True)
    record = dict(status='RUNNING', scope='Fresh scoped arithmetic module/audit with explicitly reused checked core and prebuilt Foundation/Mathlib; no whole PA evaluator/trace endpoint.',
                  repo=str(repo), scratch=str(work), dependency_rebuild=False, downloads=False,
                  main_runner_or_umbrella_modified=False,
                  runner=dict(path=str(Path(__file__).resolve()),sha256=digest(Path(__file__).resolve())), commands=[])
    def save():
        (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    try:
        fail(source.is_file() and audit.is_file(), 'Arithmetic source/audit missing; provide --source/--audit overrides if testing before placement.')
        source_hash, audit_hash = digest(source), digest(audit)
        caller_count = len(re.findall(r'^example\b', audit.read_text(), re.M))
        fail(caller_count == 20, 'Expected the stored20-caller audit; review a changed audit explicitly.')
        compiler, version = compiler_path(a.lean)
        record['compiler'] = dict(path=str(compiler), version=version, toolchain=TOOLCHAIN)
        closure, prior = core_closure(repo, a.core_evidence.resolve(), a.core_cache)
        libraries, dependencies = dependency_libraries(root, a.library_path)
        record['core_evidence'] = prior; record['reused_core'] = closure; record['dependencies'] = dependencies
        cache = work/'cache'; cache.mkdir()
        for row in closure:
            target = cache/Path(row['module'].replace('.', '/')).with_suffix('.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            # Local read-only references: nothing under either checkout is written.
            target.symlink_to(row['olean'])
        snapshot = work/'sources/BusyBeaver/ZFC/ArithmeticCantor.lean'
        snapshot.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(source,snapshot)
        audit_snapshot = work/'arithmetic_cantor_audit.lean'; shutil.copyfile(audit,audit_snapshot)
        record['source'] = dict(path=str(source), sha256=source_hash, snapshot=str(snapshot))
        record['audit_source'] = dict(path=str(audit), sha256=audit_hash, snapshot=str(audit_snapshot), callers=caller_count)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,[cache,*libraries])), LEAN_NUM_THREADS='1')
        record['LEAN_PATH'] = env['LEAN_PATH']; save()
        def run(label, command):
            start=time.monotonic()
            result=subprocess.run(command,cwd=work,env=env,capture_output=True,text=True)
            output=result.stdout+result.stderr
            log=work/(label+'.log');log.write_text(output)
            row=dict(label=label,command=command,cwd=str(work),exit_code=result.returncode,
                     seconds=round(time.monotonic()-start,6),log=str(log),output=output)
            record['commands'].append(row);save()
            fail(result.returncode==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,
                 f'{label} failed; inspect {log}')
            print(label, 'PASS',row['seconds'],'seconds',flush=True)
            return output
        obj=cache/Path(MODULE.replace('.', '/')).with_suffix('.olean')
        run('source',[str(compiler),'--root='+str(work/'sources'),'-o',str(obj),str(snapshot)])
        output=run('audit',[str(compiler),str(audit_snapshot)])
        record['axiom_reports']=audit_axioms(output)
        fail(digest(source)==source_hash and digest(audit)==audit_hash, 'Source/audit changed during the check.')
        fail(all(digest(repo/row['path'])==row['source_sha256'] and digest(Path(row['olean']))==row['olean_sha256'] for row in closure),
             'A reused project source/object changed during the check.')
        record.update(status='PASS',fresh_source_and_audit_only=True,source_unchanged_after_check=True,
                      reused_core_unchanged_after_check=True,named_axiom_probes=len(record['axiom_reports']),
                      callers=caller_count,only_standard_axioms=True,new_arithmetic_assumptions=False,
                      module_object=dict(path=str(obj),sha256=digest(obj)),
                      linter_warnings=sum('warning:' in line for line in record['commands'][0]['output'].splitlines()))
        save();print('Evidence:',work,flush=True)
    except Exception as error:
        record.update(status='FAIL',error=str(error));save();raise


if __name__=='__main__':
    main()
