"""Check only the unconditional proof-word row/history and stored audit.

Explicit successful Blocks and HistoryRecurrence evidence are required. Every
reused project source and object is matched before/after; a complete project
provider overlay chooses ONE known Cantor object (default Blocks) and records
any alternative fresh object with the same source. No hash equality between
those distinct objects is inferred. External libraries are prebuilt caller
inputs, never installed/downloaded/rebuilt. Runtime/compiler execution and
internal PA nonhalting/consistency transport remain separate.
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

ROOT = Path('Computability/BusyBeaver/Lean')
ROW = 'BusyBeaver.ZFC.ArithmeticProofWordRow254'
HISTORY = 'BusyBeaver.ZFC.ArithmeticProofWord254'
AUDIT = Path('Computability/BusyBeaver/Research/ZFC/arithmetic_proof_word254_audit.lean')
HELPER = Path('Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py')
ROW_SHA256 = '93320f2347dce7464e458ae12afb42c18449800c813f1365c65137c9aaeb4df3'
HISTORY_SHA256 = 'd0d83506af4b6eca83ef0ffd50bf1f41599d0f128908cab732216d9c44537bc7'
AUDIT_SHA256 = '2549e2dfb95bcb45f204e95eb1a68b2bf4164a8f53e11a07c3a47f3ff49c9dcd'
PROBES = tuple('SetTheory.BusyBeaver.ZFC.ArithmeticProofWordRow254.'+n for n in
               ('row_defined', 'row_defined_delta', 'row_total')) + tuple(
    'SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.'+n for n in (
        'positiveStep_defined', 'history_defined', 'history_defined_delta',
        'history_zero', 'history_succ', 'history_seq', 'history_length',
        'rawWord_defined', 'rawWord_defined_delta', 'rawWord_zero',
        'history_lookup_le', 'history_lookup', 'rawWord_succ',
        'compiledWord_defined', 'compiledWord_defined_delta',
        'compiledWord_invalid', 'compiledWord_valid', 'compiledWord_zero',
        'history_total', 'rawWord_total', 'compiledWord_total',
        'compiledWord_nat_gate', 'totalitySentence_true',
        'isigma1_proves_totality', 'peano_proves_totality'))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path)
    p.add_argument('--blocks-evidence', type=Path, required=True)
    p.add_argument('--recurrence-evidence', type=Path, required=True)
    p.add_argument('--blocks-cache', type=Path)
    p.add_argument('--recurrence-cache', type=Path)
    p.add_argument('--cantor-provider', choices=('blocks', 'recurrence'), default='blocks')
    p.add_argument('--dependency-root', type=Path, required=True)
    p.add_argument('--library-path', type=Path, action='append', default=[])
    p.add_argument('--lean', type=Path)
    p.add_argument('--row-source', type=Path)
    p.add_argument('--history-source', type=Path)
    p.add_argument('--audit', type=Path)
    p.add_argument('--output', type=Path)
    p.add_argument('--prepare-only', action='store_true')
    a = p.parse_args()
    if not __debug__:
        p.error('Keep Python assertions enabled; do not use -O.')
    repo = a.repo.resolve() if a.repo else next((q for q in Path(__file__).resolve().parents if (q/'.git').exists()), None)
    if repo is None:
        p.error('Pass --repo when the runner is outside the checkout.')
    helper = repo/HELPER
    spec = importlib.util.spec_from_file_location('proof_word_cantor_helper', helper)
    if spec is None or spec.loader is None:
        p.error('The maintained Cantor helper is missing.')
    h = importlib.util.module_from_spec(spec); spec.loader.exec_module(h)
    root = a.dependency_root.resolve()
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-arithmetic-proof-word-check-'))
    if any(work.is_relative_to(q) for q in (repo, root)) or (work.exists() and any(work.iterdir())):
        p.error('Use a new/empty scratch output outside both checkouts.')
    work.mkdir(parents=True, exist_ok=True)
    rec = dict(status='RUNNING', scope='Fresh unconditional12-word row/history plus one actual-validator gate; no structural compiler equality, execution or PA consistency transport.',
               repo=str(repo), scratch=str(work), dependency_rebuild=False, downloads=False,
               main_runner_or_umbrella_modified=False, commands=[])
    def save():
        (work/'verification.json').write_text(json.dumps(rec, indent=2)+'\n')
    try:
        sources = [a.row_source.resolve() if a.row_source else repo/ROOT/Path(ROW.replace('.', '/')).with_suffix('.lean'),
                   a.history_source.resolve() if a.history_source else repo/ROOT/Path(HISTORY.replace('.', '/')).with_suffix('.lean')]
        audit = a.audit.resolve() if a.audit else repo/AUDIT
        for source, expected, override in zip(sources, (ROW_SHA256, HISTORY_SHA256), (a.row_source, a.history_source)):
            h.fail(source.is_file() and (override is not None or h.digest(source) == expected), 'Source missing/changed; pass an explicitly reviewed source override: '+str(source))
        h.fail(audit.is_file() and (a.audit is not None or h.digest(audit) == AUDIT_SHA256), 'Audit missing/changed; explicitly review/pass --audit.')
        h.fail(h.lean_imports(sources[0].read_text()) == ['BusyBeaver.ZFC.ArithmeticCommandBlocks254'], 'Unexpected row imports.')
        h.fail(h.lean_imports(sources[1].read_text()) == [ROW, 'BusyBeaver.ZFC.ArithmeticHistoryRecurrence254'], 'Unexpected history imports.')
        h.fail(h.lean_imports(audit.read_text()) == [HISTORY], 'Unexpected audit imports.')
        h.fail(tuple(re.findall(r'^#print axioms\s+(\S+)\s*$', audit.read_text(), re.M)) == PROBES, 'Expected exact ordered28-probe contract.')
        h.fail(len(re.findall(r'^example\b', audit.read_text(), re.M)) == 21, 'Expected exact21-caller audit.')
        bp, rp = a.blocks_evidence.resolve(), a.recurrence_evidence.resolve()
        b, r = json.loads(bp.read_text()), json.loads(rp.read_text())
        h.fail(b.get('status') == r.get('status') == 'PASS', 'Both prerequisite checks must pass.')
        h.fail(b.get('named_axiom_probes') == 15 and b.get('callers') == 25 and b.get('only_standard_axioms') is True, 'Unexpected Blocks audit scope.')
        for flag in ('all_input_provider_identities_unchanged_after_check', 'all_reused_project_objects_match_evidence_after_check', 'fresh_object_unchanged_after_check', 'dependency_pins_and_clean_status_unchanged_after_check'):
            h.fail(b.get(flag) is True, 'Missing successful Blocks post-check: '+flag)
        h.fail(r.get('all_source_object_provider_postchecks') is True and r.get('only_standard_axioms') is True and r.get('all_actual_first_providers_match_prior_history') is True, 'Missing successful Recurrence source/provider audits.')
        h.fail(r.get('named_axiom_probes') == 11 and r.get('callers') == 12, 'Unexpected Recurrence audit scope.')
        compiler, version = h.compiler_path(a.lean)
        h.fail(h.digest(compiler) == b['compiler']['sha256'] == r['compiler']['sha256'] and version == b['compiler']['version'] == r['compiler']['version'], 'Compiler differs from checked prerequisites.')
        libraries, dependencies = h.dependency_libraries(root, a.library_path)
        for data in (b, r):
            for name in ('Foundation', 'Mathlib'):
                h.fail(data['dependencies'][name]['pin'] == dependencies[name]['pin'], 'Prerequisite dependency pin mismatch: '+name)
            h.fail(data['dependencies']['lake_manifest_sha256'] == dependencies['lake_manifest_sha256'], 'Prerequisite manifest mismatch.')
        bc = a.blocks_cache.resolve() if a.blocks_cache else Path(b['module_object']['path']).parents[2]
        rc = a.recurrence_cache.resolve() if a.recurrence_cache else Path(r['module_object']['path']).parents[2]
        h.fail(bc.is_dir() and rc.is_dir(), 'Prerequisite caches missing; supply relocated matching cache flags.')
        candidates = {}
        def add(module, source, source_hash, obj_hash, cache, origin, evidence):
            source = source.resolve(); obj = cache/Path(module.replace('.', '/')).with_suffix('.olean')
            h.fail(source.is_file() and h.digest(source) == source_hash, 'Prerequisite source mismatch: '+str(source))
            h.fail(obj.is_file() and h.digest(obj) == obj_hash, 'Prerequisite object mismatch: '+str(obj))
            row = dict(module=module, source=str(source), source_sha256=source_hash,
                       object=str(obj.resolve()), object_sha256=obj_hash, origin=origin, evidence=str(evidence))
            candidates.setdefault(module, []).append(row)
        for row in b['reused_project']:
            path = Path(row['path'])
            h.fail(not path.is_absolute() and '..' not in path.parts and path.suffix == '.lean' and '/Lean/' in path.as_posix(), 'Unsafe Blocks source path.')
            module = path.as_posix().split('/Lean/', 1)[1].removesuffix('.lean').replace('/', '.')
            h.fail(row['module'] == module, 'Blocks module/path mismatch.')
            add(module, repo/path, row['source_sha256'], row['olean_sha256'], bc, 'blocks', bp)
        add('BusyBeaver.ZFC.ArithmeticCommandBlocks254', repo/ROOT/'BusyBeaver/ZFC/ArithmeticCommandBlocks254.lean', b['source']['sha256'], b['module_object']['sha256'], bc, 'blocks', bp)
        for row in r['reused_modules']:
            module = row['module']
            if module in candidates:
                source = Path(candidates[module][0]['source'])
            else:
                h.fail(module.startswith('BusyBeaver.ZFC.'), 'Unfamiliar Recurrence-only project source; review mapping: '+module)
                source = repo/ROOT/Path(module.replace('.', '/')).with_suffix('.lean')
            add(module, source, row['source_sha256'], row['object_sha256'], rc, 'recurrence', rp)
        add('BusyBeaver.ZFC.ArithmeticHistoryRecurrence254', repo/ROOT/'BusyBeaver/ZFC/ArithmeticHistoryRecurrence254.lean', r['source']['sha256'], r['module_object']['sha256'], rc, 'recurrence', rp)
        chosen, alternatives = {}, []
        for module, rows in candidates.items():
            h.fail(len({row['source_sha256'] for row in rows}) == 1, 'Shared source differs between prerequisites: '+module)
            if len({row['object_sha256'] for row in rows}) > 1:
                h.fail(module == 'BusyBeaver.ZFC.ArithmeticCantor', 'Unexpected shared object conflict: '+module)
                selected = next(row for row in rows if row['origin'] == a.cantor_provider)
                alternatives.append(dict(module=module, chosen=selected, alternatives=[row for row in rows if row is not selected],
                                         scope='Exact same checked source, distinct fresh object bytes; no equality of these hashes is inferred.'))
            else:
                selected = rows[0]
            chosen[module] = selected
        required, visiting, external = {}, set(), set()
        def visit(module):
            if module in required:
                return
            h.fail(module not in visiting and module in chosen, 'Missing project prerequisite or import cycle: '+module)
            visiting.add(module); row = chosen[module]
            for imported in h.lean_imports(Path(row['source']).read_text()):
                if imported in chosen:
                    visit(imported)
                elif imported.startswith(('Foundation.', 'Mathlib.')):
                    external.add(imported)
                else:
                    h.fail(imported in {'Init', 'Std', 'Lean'} or imported.startswith(('Init.', 'Std.', 'Lean.')), 'Unrecorded project import: '+imported)
            required[module] = row; visiting.remove(module)
        visit('BusyBeaver.ZFC.ArithmeticCommandBlocks254')
        visit('BusyBeaver.ZFC.ArithmeticHistoryRecurrence254')
        h.fail(external == {'Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Foundation.FirstOrder.Arithmetic.HFS.PRF', 'Mathlib.Tactic.Ring'}, 'Unexpected external import boundary.')
        providers = {}
        iterations = {row['module']: row for row in r['iteration_providers']}
        for module in ('Foundation.FirstOrder.Arithmetic.IOpen.Basic', 'Mathlib.Tactic.Ring', 'Foundation.FirstOrder.Arithmetic.HFS.PRF', 'Foundation.FirstOrder.Arithmetic.HFS.Seq'):
            relative = Path(module.replace('.', '/')).with_suffix('.olean')
            obj = next((path/relative for path in libraries if (path/relative).is_file()), None)
            h.fail(obj is not None, 'Missing actual first external provider: '+module)
            parent = Path(dependencies['Foundation']['path']) if module.startswith('Foundation.') else Path(dependencies['Mathlib']['path'])
            source = parent/relative.with_suffix('.lean')
            row = dict(module=module, source=str(source), source_sha256=h.digest(source), object=str(obj.resolve()), object_sha256=h.digest(obj), actual_first_provider=True)
            h.fail(row['object_sha256'] == b['providers'][module]['sha256'], 'External provider differs from Blocks: '+module)
            if module in iterations:
                old = iterations[module]
                h.fail(row['object_sha256'] == old['object_sha256'] and row['source_sha256'] == old['source_sha256'], 'PRF/Seq differs from Recurrence: '+module)
            else:
                h.fail(row['object_sha256'] == r['dependencies']['providers'][module]['sha256'], 'External provider differs from Recurrence: '+module)
            providers[module] = row
        all_candidates = [row for rows in candidates.values() for row in rows]
        inputs = [Path(__file__).resolve(), helper, bp, rp, compiler, root/'lake-manifest.json', *sources, audit,
                  *(Path(row['source']) for row in all_candidates), *(Path(row['object']) for row in all_candidates),
                  *(Path(row['source']) for row in providers.values()), *(Path(row['object']) for row in providers.values())]
        inputs = list(dict.fromkeys(path.resolve() for path in inputs)); before = {str(path): h.digest(path) for path in inputs}
        overlay = work/'cache'; overlay.mkdir()
        for module, row in required.items():
            target = overlay/Path(module.replace('.', '/')).with_suffix('.olean')
            target.parent.mkdir(parents=True, exist_ok=True); target.symlink_to(row['object'])
        snapshots = []
        for module, source, override in zip((ROW, HISTORY), sources, (a.row_source, a.history_source)):
            target = work/'sources'/Path(module.replace('.', '/')).with_suffix('.lean')
            target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(source, target)
            snapshots.append(dict(module=module, path=str(source), sha256=h.digest(source), snapshot=str(target), explicit_override=override is not None))
        audit_snapshot = work/'arithmetic_proof_word254_audit.lean'; shutil.copyfile(audit, audit_snapshot)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [overlay, *libraries])), LEAN_NUM_THREADS='1')
        rec.update(compiler=dict(path=str(compiler), version=version, sha256=h.digest(compiler), toolchain=h.TOOLCHAIN),
                   runner=dict(path=str(Path(__file__).resolve()), sha256=h.digest(Path(__file__).resolve())),
                   prerequisites=[dict(path=str(bp), sha256=h.digest(bp), cache=str(bc), cache_relocated=a.blocks_cache is not None), dict(path=str(rp), sha256=h.digest(rp), cache=str(rc), cache_relocated=a.recurrence_cache is not None)],
                   source=snapshots, audit_source=dict(path=str(audit), sha256=h.digest(audit), snapshot=str(audit_snapshot), callers=21, explicit_override=a.audit is not None),
                   chosen_modules=list(required.values()), chosen_project_count=len(required), shared_object_alternatives=alternatives,
                   cantor_provider=a.cantor_provider, providers=list(providers.values()), dependencies=dependencies, before=before,
                   LEAN_PATH=env['LEAN_PATH'], prepare_only=a.prepare_only,
                   provider_scope='Exact explicitly supplied project source/object identities. Existing external caches are reused, not freshly rebuilt or independently attested as a whole.')
        save()
        def postcheck():
            after = {str(path): h.digest(path) for path in inputs}
            h.fail(after == before, 'A source/object/compiler/provider/evidence/input changed during checking.')
            for row in snapshots:
                h.fail(h.digest(Path(row['snapshot'])) == row['sha256'], 'Source snapshot changed.')
            h.fail(h.digest(audit_snapshot) == rec['audit_source']['sha256'], 'Audit snapshot changed.')
            for module, row in required.items():
                h.fail(h.digest(overlay/Path(module.replace('.', '/')).with_suffix('.olean')) == row['object_sha256'], 'Overlay object changed: '+module)
            for name in ('Foundation', 'Mathlib'):
                dep = dependencies[name]; path = Path(dep['path'])
                h.fail(h.git(path, 'rev-parse', 'HEAD') == dep['pin'] and not h.git(path, 'status', '--porcelain', '--untracked-files=no'), 'Dependency pin/clean state changed: '+name)
            for module, row in providers.items():
                relative = Path(module.replace('.', '/')).with_suffix('.olean')
                current = next((path/relative for path in libraries if (path/relative).is_file()), None)
                h.fail(current is not None and str(current.resolve()) == row['object'] and h.digest(current) == row['object_sha256'], 'Actual first provider changed: '+module)
            rec['after'] = after
        if a.prepare_only:
            postcheck(); rec.update(status='PREPARED_NOT_BUILT', all_input_provider_postchecks=True)
            save(); print(work/'verification.json'); return
        def run(label, command):
            start = time.monotonic(); result = subprocess.run(command, cwd=work, env=env, capture_output=True, text=True)
            output = result.stdout+result.stderr; log = work/(label+'.log'); log.write_text(output)
            rec['commands'].append(dict(label=label, command=command, cwd=str(work), exit_code=result.returncode, seconds=round(time.monotonic()-start, 6), log=str(log), output=output)); save()
            h.fail(result.returncode == 0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output, label+' failed: '+str(log))
            print(label, 'PASS', rec['commands'][-1]['seconds'], 'seconds', flush=True)
            return output
        fresh = []
        for row in snapshots:
            obj = overlay/Path(row['module'].replace('.', '/')).with_suffix('.olean')
            h.fail(not obj.exists(), 'Target must be freshly compiled: '+row['module'])
            run(row['module'].split('.')[-1], [str(compiler), '-M4096', '--root='+str(work/'sources'), '-o', str(obj), row['snapshot']])
            fresh.append(dict(module=row['module'], path=str(obj), sha256=h.digest(obj), source_sha256=row['sha256']))
            rec['objects_after_source'] = fresh.copy(); save()
        output = run('audit', [str(compiler), '-M4096', str(audit_snapshot)])
        reports = []
        for name, block in re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.S):
            axioms = [x.strip() for x in block.split(',') if x.strip()]
            h.fail(set(axioms) <= h.STANDARD_AXIOMS, 'Unexpected axiom: '+name)
            reports.append(dict(theorem=name, axioms=axioms))
        h.fail(tuple(row['theorem'] for row in reports) == PROBES, 'Missing, duplicate or unexpected axiom reports.')
        postcheck()
        h.fail(all(h.digest(Path(row['path'])) == row['sha256'] for row in fresh), 'Fresh object changed after its source check.')
        rec.update(status='PASS', fresh_modules=fresh, named_axiom_probes=28, callers=21, axiom_reports=reports,
                   only_standard_axioms=True, all_input_provider_postchecks=True, all_fresh_objects_unchanged_after_check=True,
                   dependency_pins_and_clean_status_unchanged_after_check=True,
                   warnings=sum(row['output'].count('warning:') for row in rec['commands']), new_arithmetic_assumptions=False)
        save(); print('Evidence:', work/'verification.json', flush=True)
    except Exception as error:
        rec.update(status='FAIL', error=str(error)); save(); raise


if __name__ == '__main__':
    main()
