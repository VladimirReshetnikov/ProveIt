"""Fresh-check finite command-block circuits and their exact symbolic audit.

Requires explicit successful represented-Append evidence and existing pinned
Foundation/Mathlib libraries. Every reused project source/object and the four
explicit external providers are matched to that evidence before and after.
Only Blocks and its audit are freshly checked. No dependency is built, fetched
or updated. Runtime, compiler history and PA consistency transport are separate.
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

SOURCE = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandBlocks254.lean')
AUDIT = Path('Computability/BusyBeaver/Research/ZFC/arithmetic_command_blocks254_audit.lean')
HELPER = Path('Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py')
MODULE = 'BusyBeaver.ZFC.ArithmeticCommandBlocks254'
PREFIX = 'SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.'
SOURCE_SHA256 = '4009dd6e2bff2b376b0d03e09cc3f37ebeb8a1a1d91c948a2302b951b6871409'
AUDIT_SHA256 = 'bf15b7eb7586be4fae9fdff8ac0d90b1868429663d8c622546909901035d7084'
PROBES = ('Circuit.defined', 'Circuit.eval_pair_nat', 'Circuit.eval_append_nat',
          'Circuit.eval_consMp', 'Circuit.eval_consDrop', 'Circuit.eval_consNip',
          'Circuit.eval_consAx', 'Circuit.packed_nil', 'Circuit.packed_encode',
          'Circuit.eval_nips', 'Circuit.eval_discard', 'Circuit.eval_leaf',
          'Circuit.eval_bundleLeaf', 'Circuit.eval_genBlock', 'Circuit.eval_mpBlock')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path)
    p.add_argument('--append-evidence', type=Path, required=True)
    p.add_argument('--append-cache', type=Path, help='relocated matching project cache')
    p.add_argument('--dependency-root', type=Path, required=True)
    p.add_argument('--library-path', type=Path, action='append', default=[])
    p.add_argument('--lean', type=Path)
    p.add_argument('--source', type=Path, help='explicit reviewed source override')
    p.add_argument('--audit', type=Path, help='explicit audit override; exact15/25 contract required')
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
    spec = importlib.util.spec_from_file_location('blocks_cantor_helper', helper)
    if spec is None or spec.loader is None:
        p.error('Maintained Cantor helper is missing.')
    h = importlib.util.module_from_spec(spec); spec.loader.exec_module(h)
    source = a.source.resolve() if a.source else repo/SOURCE
    audit = a.audit.resolve() if a.audit else repo/AUDIT
    evidence_path = a.append_evidence.resolve()
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-arithmetic-command-blocks-check-'))
    if any(work.is_relative_to(q) for q in (repo, root)) or (work.exists() and any(work.iterdir())):
        p.error('Use a new/empty scratch output outside both checkouts.')
    work.mkdir(parents=True, exist_ok=True)
    record = dict(status='RUNNING', scope='Fresh finite command-block circuits/audit only; explicitly checked Append/Word/Cantor/native objects and existing pinned external libraries reused. No internal command execution, compiler history or PA proof/consistency transport.',
                  repo=str(repo), scratch=str(work), dependency_rebuild=False, downloads=False,
                  main_runner_or_umbrella_modified=False, commands=[])
    def save():
        (work/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    try:
        h.fail(source.is_file() and audit.is_file(), 'Blocks source/audit is missing.')
        sh, ah = h.digest(source), h.digest(audit)
        h.fail(a.source is not None or sh == SOURCE_SHA256, 'Maintained source changed; explicitly review/pass --source.')
        h.fail(a.audit is not None or ah == AUDIT_SHA256, 'Maintained audit changed; explicitly review/pass --audit.')
        h.fail(h.lean_imports(source.read_text()) == ['BusyBeaver.ZFC.ArithmeticCommandAppend254'], 'Unexpected Blocks imports; review the provider closure.')
        h.fail(h.lean_imports(audit.read_text()) == [MODULE], 'Unexpected audit imports.')
        h.fail(re.findall(r'^#print axioms\s+(\S+)\s*$', audit.read_text(), re.M) == [PREFIX+n for n in PROBES], 'Expected exact ordered15-probe contract.')
        h.fail(len(re.findall(r'^example\b', audit.read_text(), re.M)) == 25, 'Expected stored25-caller audit.')
        base = json.loads(evidence_path.read_text())
        h.fail(base.get('status') == 'PASS' and base.get('named_axiom_probes') == 24 and base.get('callers') == 30 and base.get('only_standard_axioms') is True, 'Need successful explicit represented-Append evidence.')
        for flag in ('all_input_provider_identities_unchanged_after_check', 'all_reused_project_objects_match_evidence_after_check', 'fresh_object_unchanged_after_check', 'dependency_pins_and_clean_status_unchanged_after_check', 'fresh_source_and_audit_only'):
            h.fail(base.get(flag) is True, 'Missing successful prerequisite post-check: '+flag)
        compiler, version = h.compiler_path(a.lean)
        h.fail(h.digest(compiler) == base['compiler']['sha256'] and version == base['compiler']['version'], 'Compiler differs from prerequisite evidence.')
        libraries, dependencies = h.dependency_libraries(root, a.library_path)
        for name in ('Foundation', 'Mathlib'):
            h.fail(dependencies[name]['pin'] == base['dependencies'][name]['pin'], 'External dependency pin differs from prerequisite: '+name)
        for name, row in dependencies['providers'].items():
            h.fail(row['sha256'] == base['dependencies']['providers'][name]['sha256'], 'External provider object differs from prerequisite: '+name)
        h.fail(dependencies['lake_manifest_sha256'] == base['dependencies']['lake_manifest_sha256'], 'Dependency manifest differs from prerequisite.')
        cache = a.append_cache.resolve() if a.append_cache else Path(base['module_object']['path']).parents[2]
        h.fail(cache.is_dir(), 'Append project cache is unavailable; supply a matching relocated --append-cache.')
        entries = {}
        for row in base['reused_project']:
            path = Path(row['path'])
            h.fail(not path.is_absolute() and '..' not in path.parts and path.suffix == '.lean' and '/Lean/' in path.as_posix(), 'Unsafe prerequisite project source path.')
            module = path.as_posix().split('/Lean/', 1)[1].removesuffix('.lean').replace('/', '.')
            h.fail(module == row['module'] and module not in entries, 'Duplicate/mismatched prerequisite module.')
            entries[module] = dict(module=module, path=row['path'], source_sha256=row['source_sha256'], olean_sha256=row['olean_sha256'])
        module = 'BusyBeaver.ZFC.ArithmeticCommandAppend254'
        h.fail(module not in entries, 'Duplicate fresh arithmetic prerequisite.')
        path = Path('Computability/BusyBeaver/Lean')/Path(module.replace('.', '/')).with_suffix('.lean')
        entries[module] = dict(module=module, path=str(path), source_sha256=base['source']['sha256'], olean_sha256=base['module_object']['sha256'])
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
        visit('BusyBeaver.ZFC.ArithmeticCommandAppend254')
        h.fail(external == {'Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Mathlib.Tactic.Ring', 'Foundation.FirstOrder.Arithmetic.HFS.PRF'}, 'Unexpected external prerequisite import closure.')
        providers = dict(dependencies['providers'])
        for module in ('Foundation.FirstOrder.Arithmetic.HFS.PRF', 'Foundation.FirstOrder.Arithmetic.HFS.Seq'):
            relative = Path(module.replace('.', '/')).with_suffix('.olean')
            obj = next((p/relative for p in libraries if (p/relative).is_file()), None)
            h.fail(obj is not None, 'Missing prebuilt provider: '+module)
            src = Path(dependencies['Foundation']['path'])/relative.with_suffix('.lean')
            h.fail(src.is_file(), 'Missing pinned provider source: '+str(src))
            providers[module] = dict(path=str(obj.resolve()), sha256=h.digest(obj), source=str(src), source_sha256=h.digest(src))
            h.fail(providers[module]['sha256'] == base['providers'][module]['sha256'] and providers[module]['source_sha256'] == base['providers'][module]['source_sha256'], 'Foundation PRF/Seq provider differs from explicit Append evidence: '+module)
        # All four explicit external providers are bound by the supplied Append
        # evidence; their whole external import closure is not freshly rebuilt.
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
        audit_snapshot = work/'arithmetic_command_blocks254_audit.lean'; shutil.copyfile(audit, audit_snapshot)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [overlay, *libraries])), LEAN_NUM_THREADS='1')
        record.update(compiler=dict(path=str(compiler), version=version, sha256=h.digest(compiler), toolchain=h.TOOLCHAIN),
                      runner=dict(path=str(Path(__file__).resolve()), sha256=h.digest(Path(__file__).resolve())),
                      append_evidence=dict(path=str(evidence_path), sha256=h.digest(evidence_path), cache=str(cache), cache_relocated=a.append_cache is not None),
                      source=dict(path=str(source), sha256=sh, snapshot=str(snapshot), explicit_override=a.source is not None),
                      audit_source=dict(path=str(audit), sha256=ah, snapshot=str(audit_snapshot), explicit_override=a.audit is not None, callers=25),
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
        h.fail(not obj.exists(), 'Blocks must be freshly checked.')
        run('source', [str(compiler), '-M4096', '--root='+str(work/'sources'), '-o', str(obj), str(snapshot)])
        oh = h.digest(obj); record['object_immediately_after_source'] = dict(path=str(obj), sha256=oh); save()
        out = run('audit', [str(compiler), '-M4096', str(audit_snapshot)])
        probes = []
        for name, block in re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", out, re.S):
            axioms = [v.strip() for v in block.split(',') if v.strip()]
            h.fail(set(axioms) <= h.STANDARD_AXIOMS, 'Unexpected axiom: '+name)
            probes.append(dict(theorem=name, axioms=axioms))
        h.fail([row['theorem'] for row in probes] == [PREFIX+n for n in PROBES], 'Missing, duplicate or unexpected axiom reports.')
        postcheck(); h.fail(h.digest(obj) == oh, 'Fresh Blocks object changed after its source check.')
        record.update(status='PASS', named_axiom_probes=15, callers=25, axiom_reports=probes, only_standard_axioms=True,
                      module_object=dict(path=str(obj), sha256=oh), fresh_source_and_audit_only=True,
                      all_input_provider_identities_unchanged_after_check=True, all_reused_project_objects_match_evidence_after_check=True,
                      fresh_object_unchanged_after_check=True, dependency_pins_and_clean_status_unchanged_after_check=True,
                      linter_warnings=sum(row['output'].count('warning:') for row in record['commands']), new_arithmetic_assumptions=False)
        save(); print('Evidence:', work/'verification.json', flush=True)
    except Exception as error:
        record.update(status='FAIL', error=str(error)); save(); raise


if __name__ == '__main__':
    main()
