"""Fresh-check only Cantor and the bounded raw command-tail/repack graphs.

The shifted command-word codec is reused from a successful core integration.
Every reused source AND object must match that integration's recorded hashes.
Prebuilt Foundation/Mathlib dependencies are recorded and reused, never built,
installed, downloaded or updated. This is not the represented append/compiler
or the PA nonhalting/consistency equivalence.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

SOURCE = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandWord254.lean')
AUDIT = Path('Computability/BusyBeaver/Research/ZFC/arithmetic_command_word254_audit.lean')
HELPER = Path('Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py')
CANTOR_SOURCE = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCantor.lean')
CANTOR_AUDIT = Path('Computability/BusyBeaver/Research/ZFC/arithmetic_cantor_audit.lean')
MODULE = 'BusyBeaver.ZFC.ArithmeticCommandWord254'
PREFIX = 'SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254.'
SOURCE_SHA256 = 'bd6e666a96f95c4c2dae4a9cb13dbf9fc67aa1534606ccfe9ee20255d6a55b77'
AUDIT_SHA256 = '8ec1e54c8975b6d52ff96087149222bdb3ab206371805a44df1b10bc8c67d11e'
PROBES = ('first_le', 'second_le', 'second2_le', 'second3_le', 'tail_defined',
          'tailValue_le', 'short_output_bounds', 'long_output_bounds',
          'replace_defined', 'tailValue_nat', 'replaceValue_nat')
ROOTS = ('BusyBeaver.ZFC.CommandWord254', 'BusyBeaver.ZFC.Code254')


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path)
    p.add_argument('--dependency-root', type=Path, required=True)
    p.add_argument('--core-evidence', type=Path, required=True)
    p.add_argument('--core-cache', type=Path)
    p.add_argument('--library-path', type=Path, action='append', default=[])
    p.add_argument('--lean', type=Path)
    p.add_argument('--source', type=Path, help='explicit candidate override, recorded as such')
    p.add_argument('--audit', type=Path, help='explicit audit override, still requiring the exact 11/22 contract')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    if not __debug__:
        p.error('Keep assertions enabled; do not use -O.')
    repo = a.repo.resolve() if a.repo else next((q for q in Path(__file__).resolve().parents if (q/'.git').exists()), None)
    if repo is None:
        p.error('Pass --repo when the runner is outside the checkout.')
    root = a.dependency_root.resolve()
    helper = repo/HELPER
    spec = importlib.util.spec_from_file_location('command_word_cantor_helper', helper)
    if spec is None or spec.loader is None:
        p.error('Missing maintained Cantor helper.')
    h = importlib.util.module_from_spec(spec); spec.loader.exec_module(h)
    source = a.source.resolve() if a.source else repo/SOURCE
    audit = a.audit.resolve() if a.audit else repo/AUDIT
    evidence_path = a.core_evidence.resolve()
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-arithmetic-command-word-check-'))
    if any(work.is_relative_to(q) for q in (repo, root)) or (work.exists() and any(work.iterdir())):
        p.error('Use a new/empty scratch directory outside both checkouts.')
    work.mkdir(parents=True, exist_ok=True)
    record = dict(status='RUNNING', scope='Fresh Cantor plus bounded raw command-tail/repack graphs and audits; reused checked shifted-word codec. No represented append, proof compiler or internal PA equivalence.',
                  repo=str(repo), scratch=str(work), dependency_rebuild=False, downloads=False,
                  main_runner_or_umbrella_modified=False, commands=[])
    def save():
        (work/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    try:
        h.fail(source.is_file() and audit.is_file(), 'Arithmetic source/audit is missing.')
        source_hash, audit_hash = h.digest(source), h.digest(audit)
        h.fail(a.source is not None or source_hash == SOURCE_SHA256, 'Maintained arithmetic source changed; explicitly review/pass --source.')
        h.fail(a.audit is not None or audit_hash == AUDIT_SHA256, 'Maintained audit changed; explicitly review/pass --audit.')
        h.fail(h.lean_imports(source.read_text()) == [ROOTS[0], 'BusyBeaver.ZFC.ArithmeticCantor'], 'Unexpected arithmetic source imports.')
        h.fail(h.lean_imports(audit.read_text()) == [MODULE], 'Unexpected audit imports.')
        h.fail(h.lean_imports((repo/CANTOR_SOURCE).read_text()) == ['Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Mathlib.Tactic.Ring', 'BusyBeaver.ZFC.Code254'], 'Unexpected Cantor imports; review its provider closure before reuse.')
        h.fail(len(re.findall(r'^example\b', audit.read_text(), re.M)) == 22, 'Expected the stored 22-caller audit.')
        declared_probes = re.findall(r'^#print axioms\s+(\S+)\s*$', audit.read_text(), re.M)
        h.fail(declared_probes == [PREFIX+n for n in PROBES], 'Expected the exact ordered 11-probe contract.')
        compiler, version = h.compiler_path(a.lean)
        evidence = json.loads(evidence_path.read_text())
        h.fail(str(evidence.get('status', '')).startswith('PASS'), 'Core integration did not pass.')
        h.fail(isinstance(evidence.get('units'), int) and evidence['units'] >= 169, 'Need successful integration including the native command-word codec (169 or later).')
        for flag in ('all_source_identities_unchanged_after_check', 'all_object_identities_unchanged_after_check', 'all_reused_object_identities_unchanged_after_check'):
            h.fail(evidence.get(flag) is True, 'Missing successful core post-check: '+flag)
        h.fail(evidence.get('audit', {}).get('exit_code') == 0, 'Core caller/axiom audit failed.')
        h.fail(bool(evidence.get('fresh_checks')) and all(row.get('exit_code') == 0 for row in evidence['fresh_checks']), 'Core fresh checks failed or are absent.')
        h.fail(h.digest(compiler) == evidence.get('compiler', {}).get('sha256'), 'Compiler executable differs from the checked core compiler.')
        cache = a.core_cache.resolve() if a.core_cache else Path(evidence.get('cache', '')).resolve()
        h.fail(cache.is_dir(), 'Core cache is unavailable; supply a matching relocated --core-cache.')
        entries = {}
        for row in evidence.get('source_closure', []):
            path = Path(row['path'])
            h.fail(not path.is_absolute() and '..' not in path.parts and path.suffix == '.lean', 'Unsafe core source path.')
            if '/Lean/' not in path.as_posix():
                continue
            name = path.as_posix().split('/Lean/', 1)[1].removesuffix('.lean').replace('/', '.')
            h.fail(name not in entries, 'Duplicate core module '+name)
            h.fail(row.get('module', name) == name, 'Core module/path mismatch.')
            entries[name] = row
        reused, visiting = {}, set()
        def visit(name):
            if name in reused:
                return
            h.fail(name not in visiting and name in entries, 'Cycle or missing core module: '+name)
            visiting.add(name)
            row = entries[name]; src = repo/row['path']
            h.fail(src.is_file() and h.digest(src) == row['sha256'], 'Core source mismatch: '+str(src))
            for imported in h.lean_imports(src.read_text()):
                if imported in entries:
                    visit(imported)
                else:
                    h.fail(imported in {'Init', 'Std', 'Lean'} or imported.startswith(('Init.', 'Std.', 'Lean.')), 'Unexpected non-Std core dependency: '+imported)
            obj = cache/Path(name.replace('.', '/')).with_suffix('.olean')
            expected = row.get('olean_sha256')
            h.fail(isinstance(expected, str) and obj.is_file() and h.digest(obj) == expected, 'Core object differs from recorded successful integration: '+str(obj))
            h.fail(row.get('post_source_sha256', row['sha256']) == row['sha256'] and row.get('post_olean_sha256', expected) == expected, 'Core row post-check mismatch: '+name)
            reused[name] = dict(module=name, path=row['path'], source_sha256=row['sha256'], olean=str(obj.resolve()), olean_sha256=expected)
            visiting.remove(name)
        for name in ROOTS:
            visit(name)
        libraries, dependencies = h.dependency_libraries(root, a.library_path)
        dependency_sources = [Path(dependencies['Foundation']['path'])/'Foundation/FirstOrder/Arithmetic/IOpen/Basic.lean',
                              Path(dependencies['Mathlib']['path'])/'Mathlib/Tactic/Ring.lean']
        # These inputs/providers are identity-audited before AND after both fresh stages.
        tracked = [Path(__file__).resolve(), helper, repo/CANTOR_SOURCE, repo/CANTOR_AUDIT,
                   source, audit, evidence_path, compiler, root/'lake-manifest.json', *dependency_sources,
                   *(Path(row['path']) for row in dependencies['providers'].values()),
                   *(repo/row['path'] for row in reused.values()), *(Path(row['olean']) for row in reused.values())]
        tracked = list(dict.fromkeys(path.resolve() for path in tracked))
        inputs = [dict(path=str(path), sha256=h.digest(path)) for path in tracked]
        record.update(compiler=dict(path=str(compiler), version=version, sha256=h.digest(compiler), toolchain=h.TOOLCHAIN),
                      runner=dict(path=str(Path(__file__).resolve()), sha256=h.digest(Path(__file__).resolve())),
                      source=dict(path=str(source), sha256=source_hash, explicit_override=a.source is not None),
                      audit_source=dict(path=str(audit), sha256=audit_hash, explicit_override=a.audit is not None, callers=22),
                      core_evidence=dict(path=str(evidence_path), sha256=h.digest(evidence_path), units=evidence['units'], cache=str(cache), cache_relocated=a.core_cache is not None),
                      actual_import_roots=list(ROOTS), reused_core=list(reused.values()), reused_core_count=len(reused),
                      reused_objects_match_recorded_evidence=True, dependencies=dependencies, inputs=inputs)
        save()
        def run(label, command, env=None):
            start = time.monotonic()
            result = subprocess.run(command, cwd=work, env=env, capture_output=True, text=True)
            output = result.stdout+result.stderr
            log = work/(label+'.log'); log.write_text(output)
            row = dict(label=label, command=command, cwd=str(work), exit_code=result.returncode,
                       seconds=round(time.monotonic()-start, 6), log=str(log), output=output)
            record['commands'].append(row); save()
            h.fail(result.returncode == 0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output, label+' failed: '+str(log))
            print(label, 'PASS', row['seconds'], 'seconds', flush=True)
            return output
        cantor_work = work/'cantor'
        command = [sys.executable, '-B', str(helper), '--repo', str(repo), '--dependency-root', str(root),
                   '--core-evidence', str(evidence_path), '--core-cache', str(cache), '--lean', str(compiler), '--output', str(cantor_work)]
        for library in a.library_path:
            command += ['--library-path', str(library.resolve())]
        run('fresh_cantor', command)
        cantor_evidence_path = cantor_work/'verification.json'
        cantor = json.loads(cantor_evidence_path.read_text())
        h.fail(cantor.get('status') == 'PASS' and cantor.get('named_axiom_probes') == 27 and cantor.get('callers') == 20 and cantor.get('only_standard_axioms') is True, 'Fresh Cantor contract did not pass.')
        h.fail(cantor.get('compiler', {}).get('path') == str(compiler) and cantor['compiler'].get('version') == version, 'Fresh Cantor used a different compiler.')
        h.fail(cantor.get('source', {}).get('path') == str(repo/CANTOR_SOURCE) and cantor['source'].get('sha256') == h.digest(repo/CANTOR_SOURCE), 'Fresh Cantor source differs from the tracked maintained input.')
        h.fail(cantor.get('audit_source', {}).get('path') == str(repo/CANTOR_AUDIT) and cantor['audit_source'].get('sha256') == h.digest(repo/CANTOR_AUDIT), 'Fresh Cantor audit differs from the tracked maintained input.')
        for key in ('source', 'audit_source'):
            h.fail(h.digest(Path(cantor[key]['snapshot'])) == cantor[key]['sha256'], 'Fresh Cantor snapshot differs from its input: '+key)
        h.fail(cantor.get('dependencies') == dependencies, 'Fresh Cantor used different dependency pins/providers/libraries.')
        h.fail(cantor.get('LEAN_PATH') == os.pathsep.join(map(str, [cantor_work/'cache', *libraries])), 'Fresh Cantor used a different ordered library path.')
        for row in cantor['reused_core']:
            expected = reused.get(row['module'])
            h.fail(expected is not None and row['source_sha256'] == expected['source_sha256'] and row['olean_sha256'] == expected['olean_sha256'], 'Cantor reused an unmatched source/object: '+row['module'])
        fresh_cache = cantor_work/'cache'
        cantor_obj = Path(cantor['module_object']['path'])
        h.fail(cantor_obj.is_file() and not cantor_obj.is_symlink() and h.digest(cantor_obj) == cantor['module_object']['sha256'], 'Fresh Cantor object is absent, reused, or changed.')
        for row in reused.values():
            target = fresh_cache/Path(row['module'].replace('.', '/')).with_suffix('.olean')
            if target.exists():
                h.fail(h.digest(target) == row['olean_sha256'], 'Fresh overlay contains a conflicting core object: '+row['module'])
            else:
                target.parent.mkdir(parents=True, exist_ok=True); target.symlink_to(row['olean'])
        snapshot = work/'sources'/Path(MODULE.replace('.', '/')).with_suffix('.lean')
        snapshot.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(source, snapshot)
        audit_snapshot = work/'arithmetic_command_word254_audit.lean'; shutil.copyfile(audit, audit_snapshot)
        record['source']['snapshot'] = str(snapshot); record['audit_source']['snapshot'] = str(audit_snapshot)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [fresh_cache, *libraries])), LEAN_NUM_THREADS='1')
        record['LEAN_PATH'] = env['LEAN_PATH']
        obj = fresh_cache/Path(MODULE.replace('.', '/')).with_suffix('.olean')
        h.fail(not obj.exists(), 'The arithmetic module must be freshly compiled.')
        run('source', [str(compiler), '--root='+str(work/'sources'), '-o', str(obj), str(snapshot)], env)
        source_object_hash = h.digest(obj)
        record['object_immediately_after_source'] = dict(path=str(obj), sha256=source_object_hash)
        save()
        output = run('audit', [str(compiler), str(audit_snapshot)], env)
        reports = []
        pattern = r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
        for name, block in re.findall(pattern, output, re.S):
            axioms = [v.strip() for v in block.split(',') if v.strip()]
            h.fail(set(axioms) <= h.STANDARD_AXIOMS, 'Unexpected axiom: '+name)
            reports.append(dict(theorem=name, axioms=axioms))
        h.fail([row['theorem'] for row in reports] == [PREFIX+n for n in PROBES], 'Missing, duplicate or unexpected arithmetic axiom reports.')
        h.fail(h.digest(snapshot) == source_hash and h.digest(audit_snapshot) == audit_hash, 'Fresh source/audit snapshot changed.')
        for row in inputs:
            row['post_sha256'] = h.digest(Path(row['path']))
            h.fail(row['post_sha256'] == row['sha256'], 'Input/provider changed during check: '+row['path'])
        # Preserve both dependency pins and tracked-clean status after the fresh checks.
        for name in ('Foundation', 'Mathlib'):
            dep = dependencies[name]; path = Path(dep['path'])
            h.fail(h.git(path, 'rev-parse', 'HEAD') == dep['pin'] and not h.git(path, 'status', '--porcelain', '--untracked-files=no'), name+' changed during check.')
        h.fail(h.digest(cantor_obj) == cantor['module_object']['sha256'], 'Fresh Cantor object changed after checking ArithWord.')
        h.fail(h.digest(obj) == source_object_hash, 'Fresh ArithWord object changed after its source check.')
        for row in reused.values():
            target = fresh_cache/Path(row['module'].replace('.', '/')).with_suffix('.olean')
            h.fail(h.digest(target) == row['olean_sha256'], 'Reused overlay object changed: '+row['module'])
        new_warnings = sum('warning:' in line for row in record['commands'][1:] for line in row['output'].splitlines())
        record.update(status='PASS', axiom_reports=reports, named_axiom_probes=11, callers=22,
                      aggregate_named_axiom_probes=38, aggregate_callers=42, only_standard_axioms=True,
                      fresh_modules=['BusyBeaver.ZFC.ArithmeticCantor', MODULE], fresh_audits=2,
                      fresh_cantor=dict(evidence=str(cantor_evidence_path), evidence_sha256=h.digest(cantor_evidence_path), named_axiom_probes=27, callers=20,
                                        module_object=cantor['module_object'], source=cantor['source'], audit_source=cantor['audit_source']),
                      module_object=dict(path=str(obj), sha256=h.digest(obj)),
                      all_input_provider_identities_unchanged_after_check=True, fresh_objects_unchanged_after_check=True, all_core_objects_match_recorded_evidence_after_check=True,
                      all_dependency_pins_and_clean_status_unchanged_after_check=True,
                      linter_warnings=dict(cantor=cantor['linter_warnings'], arithmetic_command_word=new_warnings, total=cantor['linter_warnings']+new_warnings),
                      new_arithmetic_assumptions=False)
        save(); print('Evidence:', work/'verification.json', flush=True)
    except Exception as error:
        record.update(status='FAIL', error=str(error)); save(); raise


if __name__ == '__main__':
    main()
