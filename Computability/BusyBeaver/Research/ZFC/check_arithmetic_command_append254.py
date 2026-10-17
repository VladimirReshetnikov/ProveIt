"""Fresh-check the represented shifted-command append module and its audit.

Requires successful explicit arithmetic-command-word evidence and existing
pinned Foundation/Mathlib libraries. It matches every reused project source
and object, builds a complete project-provider overlay, then freshly checks
Append only. Run the narrow command-word checker first and pass its evidence
for a fresh three-module chain. Nothing is rebuilt, installed or downloaded
under either checkout. This is not PA consistency/proof transport.
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
import tempfile
import time

SOURCE = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandAppend254.lean')
AUDIT = Path('Computability/BusyBeaver/Research/ZFC/arithmetic_command_append254_audit.lean')
HELPER = Path('Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py')
MODULE = 'BusyBeaver.ZFC.ArithmeticCommandAppend254'
PREFIX = 'SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.'
SOURCE_SHA256 = 'bbe2560d7360b6776f773805aab3a1b5fe30278c4a9e32e15e5f58e65538352f'
AUDIT_SHA256 = 'e75e5075cf1fd971048cd2357aff62631f7033ff284733d8a1263b973831b026'
PROBES = ('step_defined', 'history_defined', 'history_defined_delta', 'history_zero',
          'history_succ', 'history_seq', 'history_length', 'append_defined',
          'append_defined_delta', 'znth_append_old', 'znth_append_last',
          'appendValue_zero', 'history_lookup_le', 'appendValue_succ',
          'appendValue_eq_zero', 'history_lookup', 'appendValue_nat',
          'history_lookup_nat', 'appendDef_nat', 'history_total', 'append_total',
          'totalitySentence_true', 'isigma1_proves_totality', 'peano_proves_totality')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path)
    p.add_argument('--command-word-evidence', type=Path, required=True)
    p.add_argument('--command-word-cache', type=Path, help='relocated matching project cache')
    p.add_argument('--dependency-root', type=Path, required=True)
    p.add_argument('--library-path', type=Path, action='append', default=[])
    p.add_argument('--lean', type=Path)
    p.add_argument('--source', type=Path, help='explicit reviewed source override')
    p.add_argument('--audit', type=Path, help='explicit audit override; exact24/30 contract required')
    p.add_argument('--output', type=Path)
    p.add_argument('--prepare-only', action='store_true', help='validate/capture inputs and construct overlay without compiling')
    a = p.parse_args()
    if not __debug__:
        p.error('Keep Python assertions enabled; do not use -O.')
    repo = a.repo.resolve() if a.repo else next((q for q in Path(__file__).resolve().parents if (q/'.git').exists()), None)
    if repo is None:
        p.error('Pass --repo when running outside the checkout.')
    root = a.dependency_root.resolve()
    helper = repo/HELPER
    spec = importlib.util.spec_from_file_location('append_cantor_helper', helper)
    if spec is None or spec.loader is None:
        p.error('Maintained Cantor helper is missing.')
    h = importlib.util.module_from_spec(spec); spec.loader.exec_module(h)
    source = a.source.resolve() if a.source else repo/SOURCE
    audit = a.audit.resolve() if a.audit else repo/AUDIT
    evidence_path = a.command_word_evidence.resolve()
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-arithmetic-command-append-check-'))
    if any(work.is_relative_to(q) for q in (repo, root)) or (work.exists() and any(work.iterdir())):
        p.error('Use a new/empty scratch output outside both checkouts.')
    work.mkdir(parents=True, exist_ok=True)
    record = dict(status='RUNNING', scope='Fresh represented append module/audit only; explicit checked Word/Cantor/native objects and existing pinned external libraries reused. No internal PA proof/consistency transport.',
                  repo=str(repo), scratch=str(work), dependency_rebuild=False, downloads=False,
                  main_runner_or_umbrella_modified=False, commands=[])
    def save():
        (work/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    try:
        h.fail(source.is_file() and audit.is_file(), 'Append source/audit is missing.')
        sh, ah = h.digest(source), h.digest(audit)
        h.fail(a.source is not None or sh == SOURCE_SHA256, 'Maintained source changed; explicitly review/pass --source.')
        h.fail(a.audit is not None or ah == AUDIT_SHA256, 'Maintained audit changed; explicitly review/pass --audit.')
        h.fail(h.lean_imports(source.read_text()) == ['BusyBeaver.ZFC.ArithmeticCommandWord254', 'Foundation.FirstOrder.Arithmetic.HFS.PRF'], 'Unexpected Append imports; review the provider closure.')
        h.fail(h.lean_imports(audit.read_text()) == [MODULE], 'Unexpected audit imports.')
        h.fail(re.findall(r'^#print axioms\s+(\S+)\s*$', audit.read_text(), re.M) == [PREFIX+n for n in PROBES], 'Expected exact ordered24-probe contract.')
        h.fail(len(re.findall(r'^example\b', audit.read_text(), re.M)) == 30, 'Expected stored30-caller audit.')
        base = json.loads(evidence_path.read_text())
        h.fail(base.get('status') == 'PASS' and base.get('aggregate_named_axiom_probes') == 38 and base.get('aggregate_callers') == 42 and base.get('only_standard_axioms') is True, 'Need successful explicit Cantor+command-word evidence.')
        for flag in ('all_input_provider_identities_unchanged_after_check', 'fresh_objects_unchanged_after_check', 'all_core_objects_match_recorded_evidence_after_check', 'all_dependency_pins_and_clean_status_unchanged_after_check'):
            h.fail(base.get(flag) is True, 'Missing successful prerequisite post-check: '+flag)
        h.fail(base.get('fresh_modules') == ['BusyBeaver.ZFC.ArithmeticCantor', 'BusyBeaver.ZFC.ArithmeticCommandWord254'], 'Unexpected prerequisite fresh-module scope.')
        compiler, version = h.compiler_path(a.lean)
        h.fail(h.digest(compiler) == base['compiler']['sha256'] and version == base['compiler']['version'], 'Compiler differs from prerequisite evidence.')
        libraries, dependencies = h.dependency_libraries(root, a.library_path)
        for name in ('Foundation', 'Mathlib'):
            h.fail(dependencies[name]['pin'] == base['dependencies'][name]['pin'], 'External dependency pin differs from prerequisite: '+name)
        for name, row in dependencies['providers'].items():
            h.fail(row['sha256'] == base['dependencies']['providers'][name]['sha256'], 'External provider object differs from prerequisite: '+name)
        h.fail(dependencies['lake_manifest_sha256'] == base['dependencies']['lake_manifest_sha256'], 'Dependency manifest differs from prerequisite.')
        cache = a.command_word_cache.resolve() if a.command_word_cache else Path(base['module_object']['path']).parents[2]
        h.fail(cache.is_dir(), 'Command-word project cache is unavailable; supply a matching relocated --command-word-cache.')
        entries = {}
        for row in base['reused_core']:
            path = Path(row['path'])
            h.fail(not path.is_absolute() and '..' not in path.parts and path.suffix == '.lean' and '/Lean/' in path.as_posix(), 'Unsafe prerequisite project source path.')
            module = path.as_posix().split('/Lean/', 1)[1].removesuffix('.lean').replace('/', '.')
            h.fail(module == row['module'] and module not in entries, 'Duplicate/mismatched prerequisite module.')
            entries[module] = dict(module=module, path=row['path'], source_sha256=row['source_sha256'], olean_sha256=row['olean_sha256'])
        for module, src, obj in (
            ('BusyBeaver.ZFC.ArithmeticCantor', base['fresh_cantor']['source'], base['fresh_cantor']['module_object']),
            ('BusyBeaver.ZFC.ArithmeticCommandWord254', base['source'], base['module_object'])):
            h.fail(module not in entries, 'Duplicate fresh arithmetic prerequisite.')
            path = Path('Computability/BusyBeaver/Lean')/Path(module.replace('.', '/')).with_suffix('.lean')
            entries[module] = dict(module=module, path=str(path), source_sha256=src['sha256'], olean_sha256=obj['sha256'])
        required, visiting = {}, set()
        external = set()
        def visit(module):
            if module in required:
                return
            h.fail(module not in visiting and module in entries, 'Missing prerequisite module or import cycle: '+module)
            visiting.add(module)
            row = entries[module]; src = repo/row['path']
            h.fail(src.is_file() and h.digest(src) == row['source_sha256'], 'Prerequisite source changed: '+str(src))
            for imported in h.lean_imports(src.read_text()):
                if imported in entries:
                    visit(imported)
                elif imported.startswith(('Foundation.', 'Mathlib.')):
                    external.add(imported)
                else:
                    h.fail(imported in {'Init', 'Std', 'Lean'} or imported.startswith(('Init.', 'Std.', 'Lean.')), 'Unrecorded project import: '+imported)
            obj = cache/Path(module.replace('.', '/')).with_suffix('.olean')
            h.fail(obj.is_file() and h.digest(obj) == row['olean_sha256'], 'Prerequisite object changed: '+str(obj))
            required[module] = dict(row, olean=str(obj.resolve()))
            visiting.remove(module)
        visit('BusyBeaver.ZFC.ArithmeticCommandWord254')
        h.fail(external == {'Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Mathlib.Tactic.Ring'}, 'Unexpected external prerequisite import closure.')
        providers = dict(dependencies['providers'])
        for module in ('Foundation.FirstOrder.Arithmetic.HFS.PRF', 'Foundation.FirstOrder.Arithmetic.HFS.Seq'):
            relative = Path(module.replace('.', '/')).with_suffix('.olean')
            obj = next((p/relative for p in libraries if (p/relative).is_file()), None)
            h.fail(obj is not None, 'Missing prebuilt provider: '+module)
            src = Path(dependencies['Foundation']['path'])/relative.with_suffix('.lean')
            h.fail(src.is_file(), 'Missing pinned provider source: '+str(src))
            providers[module] = dict(path=str(obj.resolve()), sha256=h.digest(obj), source=str(src), source_sha256=h.digest(src))
        # The two preexisting external providers were already bound by the
        # prerequisite; PRF/Seq caches are explicitly caller-supplied reuse.
        inputs = [Path(__file__).resolve(), helper, source, audit, evidence_path, compiler, root/'lake-manifest.json',
                  *(repo/row['path'] for row in required.values()), *(Path(row['olean']) for row in required.values()),
                  *(Path(row['path']) for row in providers.values()),
                  *(Path(row['source']) for row in providers.values() if 'source' in row)]
        for module in ('Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Mathlib.Tactic.Ring'):
            parent = Path(dependencies['Foundation']['path']) if module.startswith('Foundation.') else Path(dependencies['Mathlib']['path'])
            inputs.append(parent/Path(module.replace('.', '/')).with_suffix('.lean'))
        inputs = list(dict.fromkeys(path.resolve() for path in inputs))
        hashes = [dict(path=str(path), sha256=h.digest(path)) for path in inputs]
        overlay = work/'cache'; overlay.mkdir()
        for row in required.values():
            target = overlay/Path(row['module'].replace('.', '/')).with_suffix('.olean')
            target.parent.mkdir(parents=True, exist_ok=True); target.symlink_to(row['olean'])
        snapshot = work/'sources'/Path(MODULE.replace('.', '/')).with_suffix('.lean')
        snapshot.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(source, snapshot)
        audit_snapshot = work/'arithmetic_command_append254_audit.lean'; shutil.copyfile(audit, audit_snapshot)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [overlay, *libraries])), LEAN_NUM_THREADS='1')
        record.update(compiler=dict(path=str(compiler), version=version, sha256=h.digest(compiler), toolchain=h.TOOLCHAIN),
                      runner=dict(path=str(Path(__file__).resolve()), sha256=h.digest(Path(__file__).resolve())),
                      command_word_evidence=dict(path=str(evidence_path), sha256=h.digest(evidence_path), cache=str(cache), cache_relocated=a.command_word_cache is not None),
                      source=dict(path=str(source), sha256=sh, snapshot=str(snapshot), explicit_override=a.source is not None),
                      audit_source=dict(path=str(audit), sha256=ah, snapshot=str(audit_snapshot), explicit_override=a.audit is not None, callers=30),
                      reused_project=list(required.values()), reused_project_count=len(required),
                      dependencies=dependencies, providers=providers, inputs=hashes, LEAN_PATH=env['LEAN_PATH'],
                      provider_scope='Existing external cache objects are recorded/reused; no independent whole-cache build attestation or dependency rebuild.',
                      prepare_only=a.prepare_only)
        save()
        def postcheck():
            h.fail(h.digest(snapshot) == sh and h.digest(audit_snapshot) == ah, 'Fresh snapshots changed.')
            for row in hashes:
                row['post_sha256'] = h.digest(Path(row['path']))
                h.fail(row['post_sha256'] == row['sha256'], 'Input/provider changed: '+row['path'])
            for row in required.values():
                target = overlay/Path(row['module'].replace('.', '/')).with_suffix('.olean')
                h.fail(h.digest(target) == row['olean_sha256'], 'Overlay object changed: '+row['module'])
            for name in ('Foundation', 'Mathlib'):
                dep = dependencies[name]; path = Path(dep['path'])
                h.fail(h.git(path, 'rev-parse', 'HEAD') == dep['pin'] and not h.git(path, 'status', '--porcelain', '--untracked-files=no'), 'Dependency pin/clean status changed: '+name)
        if a.prepare_only:
            postcheck(); record.update(status='PREPARED_NOT_BUILT', all_input_provider_identities_unchanged_after_prepare=True)
            save(); print(work/'verification.json'); return
        def run(label, command):
            start = time.monotonic(); result = subprocess.run(command, cwd=work, env=env, capture_output=True, text=True)
            output = result.stdout+result.stderr; log = work/(label+'.log'); log.write_text(output)
            record['commands'].append(dict(label=label, command=command, cwd=str(work), exit_code=result.returncode,
                                           seconds=round(time.monotonic()-start, 6), log=str(log), output=output)); save()
            h.fail(result.returncode == 0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output, label+' failed: '+str(log))
            print(label, 'PASS', record['commands'][-1]['seconds'], 'seconds', flush=True)
            return output
        obj = overlay/Path(MODULE.replace('.', '/')).with_suffix('.olean')
        h.fail(not obj.exists(), 'Append must be freshly checked.')
        run('source', [str(compiler), '--root='+str(work/'sources'), '-o', str(obj), str(snapshot)])
        oh = h.digest(obj); record['object_immediately_after_source'] = dict(path=str(obj), sha256=oh); save()
        out = run('audit', [str(compiler), str(audit_snapshot)])
        probes = []
        for name, block in re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", out, re.S):
            axioms = [v.strip() for v in block.split(',') if v.strip()]
            h.fail(set(axioms) <= h.STANDARD_AXIOMS, 'Unexpected axiom: '+name)
            probes.append(dict(theorem=name, axioms=axioms))
        h.fail([row['theorem'] for row in probes] == [PREFIX+n for n in PROBES], 'Missing, duplicate or unexpected axiom reports.')
        postcheck(); h.fail(h.digest(obj) == oh, 'Fresh Append object changed after its source check.')
        record.update(status='PASS', named_axiom_probes=24, callers=30, axiom_reports=probes, only_standard_axioms=True,
                      module_object=dict(path=str(obj), sha256=oh), fresh_source_and_audit_only=True,
                      all_input_provider_identities_unchanged_after_check=True, all_reused_project_objects_match_evidence_after_check=True,
                      fresh_object_unchanged_after_check=True, dependency_pins_and_clean_status_unchanged_after_check=True,
                      linter_warnings=sum(row['output'].count('warning:') for row in record['commands']), new_arithmetic_assumptions=False)
        save(); print('Evidence:', work/'verification.json', flush=True)
    except Exception as error:
        record.update(status='FAIL', error=str(error)); save(); raise


if __name__ == '__main__':
    main()
