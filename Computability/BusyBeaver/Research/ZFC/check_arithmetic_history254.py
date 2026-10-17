"""Check the represented C254 history and its all-input checker comparison.

Freshly check all five arithmetic modules and their stored audits. Reuse only
the source/object-matched core history closure and explicitly supplied pinned
Foundation/Mathlib cache. Record the PRF/Seq providers used by this extension.
No dependency download/build or whole-machine PA proof is performed.
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

RESEARCH = Path('Computability/BusyBeaver/Research/ZFC')
SOURCE = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticHistory254.lean')
MODULE = 'BusyBeaver.ZFC.ArithmeticHistory254'
PREFIX = 'SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.'
PROBES = ('positiveStep_defined', 'step_defined', 'stepValue_zero', 'stepValue_succ', 'history_defined', 'history_defined_delta', 'history_zero', 'history_succ', 'history_seq', 'history_length', 'value_defined', 'value_defined_delta', 'check_defined', 'checkValue_defined', 'checkValue_defined_delta', 'value_total', 'checkValue_total', 'checkValue_range', 'foundation_div_nat', 'foundation_rem_nat', 'numeral_twelve_eq_twelve', 'positiveStep_nat', 'stepValue_nat', 'znth_append_old', 'znth_append_last', 'znth_append', 'history_lookup_nat', 'value_nat', 'checkDef_nat', 'c254_iff_represented', 'history_total', 'value_zero', 'checkValue_zero', 'checkValue_nat', 'totalitySentence_true', 'isigma1_proves_totality', 'peano_proves_totality')
CALLERS = 44


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path)
    p.add_argument('--dependency-root', type=Path, required=True)
    p.add_argument('--core-evidence', type=Path, required=True)
    p.add_argument('--core-cache', type=Path)
    p.add_argument('--library-path', type=Path, action='append', default=[])
    p.add_argument('--lean', type=Path)
    p.add_argument('--source', type=Path)
    p.add_argument('--audit', type=Path)
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    if not __debug__:
        p.error('Keep assertions enabled; do not use -O.')
    script = Path(__file__).resolve()
    repo = a.repo.resolve() if a.repo else next((q for q in script.parents if (q/'.git').exists()), None)
    if repo is None:
        p.error('Pass --repo outside the checkout.')
    prerequisite = repo/RESEARCH/'check_arithmetic_row254.py'
    base_path = repo/RESEARCH/'check_arithmetic_cantor.py'
    spec = importlib.util.spec_from_file_location('checked_history_helpers', base_path)
    if spec is None or spec.loader is None:
        p.error('Maintained Cantor checker helpers are missing.')
    base = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(base)
    root = a.dependency_root.resolve()
    source = a.source.resolve() if a.source else repo/SOURCE
    audit = a.audit.resolve() if a.audit else script.with_name('arithmetic_history254_audit.lean')
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-arithmetic-history254-check-'))
    if any(work.is_relative_to(q) for q in (repo, root)) or (work.exists() and any(work.iterdir())):
        p.error('Use new/empty scratch outside source and dependency checkouts.')
    work.mkdir(parents=True, exist_ok=True)
    inputs = [script, source, audit]
    for stem, module in (('cantor', 'Cantor'), ('code254', 'Code254'),
                         ('templates254', 'Templates254'), ('row254', 'Row254')):
        inputs += [repo/SOURCE.parent/('Arithmetic'+module+'.lean'),
                   repo/RESEARCH/('arithmetic_'+stem+'_audit.lean'),
                   repo/RESEARCH/('check_arithmetic_'+stem+'.py')]
    record = dict(status='RUNNING', scope='Five fresh arithmetic modules/audits. Fixed represented history and Boolean checker in all IΣ1 models; comparison with the actual checker on all Nat inputs. No proof-code/trace transport endpoint.',
                  repo=str(repo), scratch=str(work), commands=[],
                  dependency_rebuild=False, downloads=False, main_runner_or_umbrella_modified=False)

    def save():
        (work/'verification.json').write_text(json.dumps(record, indent=2)+'\n')

    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    env.pop('PYTHONOPTIMIZE', None)

    def run(label, command):
        start = time.monotonic()
        result = subprocess.run(command, cwd=work, env=env, capture_output=True, text=True)
        output = result.stdout+result.stderr
        log = work/(label+'.log')
        log.write_text(output)
        record['commands'].append(dict(label=label, command=command, cwd=str(work), exit_code=result.returncode,
                                      seconds=round(time.monotonic()-start, 6), log=str(log), output=output))
        save()
        base.fail(result.returncode == 0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,
                  f'{label} failed; inspect {log}')
        print(label, 'PASS', record['commands'][-1]['seconds'], 'seconds', flush=True)
        return output

    save()
    try:
        base.fail(PROBES and CALLERS > 0, 'Stored audit needs an explicit reviewed probe/caller contract.')
        hashes = {str(q): base.digest(q) for q in inputs}
        record['inputs'] = hashes
        base.fail(re.findall(r'^#print axioms (.+)$', audit.read_text(), re.M) == [PREFIX+n for n in PROBES]
                  and len(re.findall(r'^example\b', audit.read_text(), re.M)) == CALLERS, 'Unexpected history audit.')
        base.fail(base.lean_imports(source.read_text()) == ['BusyBeaver.ZFC.ArithmeticRow254',
                  'Foundation.FirstOrder.Arithmetic.HFS.PRF'], 'Review changed history imports before checking.')
        command = [sys.executable, '-B', str(prerequisite), '--repo', str(repo), '--dependency-root', str(root),
                   '--core-evidence', str(a.core_evidence.resolve()), '--output', str(work/'row')]
        for flag, value in (('--core-cache', a.core_cache), ('--lean', a.lean)):
            if value is not None:
                command += [flag, str(value.resolve())]
        for value in a.library_path:
            command += ['--library-path', str(value.resolve())]
        run('row-prerequisite', command)
        prior = json.loads((work/'row/verification.json').read_text())
        base.fail(prior.get('status') == 'PASS' and prior['total_named_axiom_probes'] == 114
                  and prior['total_callers'] == 120 and prior['only_standard_axioms'], 'Incomplete row checks.')
        env.update(LEAN_PATH=prior['LEAN_PATH'], LEAN_NUM_THREADS='1')
        libraries = [Path(q) for q in env['LEAN_PATH'].split(os.pathsep)]
        cache = libraries[0]
        providers = []
        for module in ('Foundation.FirstOrder.Arithmetic.HFS.PRF', 'Foundation.FirstOrder.Arithmetic.HFS.Seq'):
            relative = Path(module.replace('.', '/'))
            src = root/'lib/FormalizedFormalLogic-Foundation'/relative.with_suffix('.lean')
            obj = next((q/relative.with_suffix('.olean') for q in libraries
                        if (q/relative.with_suffix('.olean')).is_file()), None)
            base.fail(src.is_file() and obj is not None, 'Missing prebuilt/source provider: '+module)
            providers.append(dict(module=module, source=str(src), source_sha256=base.digest(src),
                                  object=str(obj), object_sha256=base.digest(obj)))
        record.update(compiler=prior['compiler'], dependencies=prior['dependencies'],
                      core_evidence=prior['core_evidence'], reused_core=prior['reused_core'],
                      iteration_providers=providers, fresh_prerequisite=prior, LEAN_PATH=env['LEAN_PATH'])
        snapshot = work/'sources/BusyBeaver/ZFC/ArithmeticHistory254.lean'
        snapshot.parent.mkdir(parents=True)
        shutil.copyfile(source, snapshot)
        audit_copy = work/'arithmetic_history254_audit.lean'
        shutil.copyfile(audit, audit_copy)
        compiler = Path(prior['compiler']['path'])
        compiler_hash = base.digest(compiler)
        obj = cache/Path(MODULE.replace('.', '/')).with_suffix('.olean')
        run('source', [str(compiler), '--root='+str(work/'sources'), '-o', str(obj), str(snapshot)])
        output = run('audit', [str(compiler), str(audit_copy)])
        parsed = []
        for name, block in re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.S):
            axioms = [x.strip() for x in block.split(',') if x.strip()]
            base.fail(set(axioms) <= base.STANDARD_AXIOMS, 'Unexpected axioms: '+name)
            parsed.append(dict(theorem=name, axioms=axioms))
        base.fail(len(parsed) == len(PROBES) and {q['theorem'] for q in parsed} == {PREFIX+n for n in PROBES},
                  'Missing, duplicate, or unexpected history axiom report.')
        base.fail(all(base.digest(Path(q)) == h for q, h in hashes.items()), 'A source/audit/helper changed.')
        base.fail(all(base.digest(repo/q['path']) == q['source_sha256']
                      and base.digest(Path(q['olean'])) == q['olean_sha256'] for q in prior['reused_core']),
                  'A reused core source/object changed.')
        templates = prior['fresh_prerequisite']
        constructors = templates['fresh_prerequisite']
        for entry in (prior['module_object'], templates['module_object'], constructors['object'], constructors['cantor']['object']):
            base.fail(base.digest(Path(entry['path'])) == entry['sha256'], 'A fresh arithmetic prerequisite changed.')
        base.fail(all(base.digest(Path(q['source'])) == q['source_sha256']
                      and base.digest(Path(q['object'])) == q['object_sha256'] for q in providers),
                  'An iteration provider source/object changed.')
        base.fail(base.digest(compiler) == compiler_hash, 'Compiler changed.')
        record.update(status='PASS', source=dict(path=str(source), sha256=hashes[str(source)], snapshot=str(snapshot)),
                      audit_source=dict(path=str(audit), sha256=hashes[str(audit)], source=audit.read_text()),
                      module_object=dict(path=str(obj), sha256=base.digest(obj)), compiler_binary_sha256=compiler_hash,
                      axiom_reports=parsed, named_axiom_probes=len(PROBES), callers=CALLERS,
                      total_named_axiom_probes=114+len(PROBES), total_callers=120+CALLERS, only_standard_axioms=True,
                      fresh_modules=prior['fresh_modules']+[MODULE], fresh_stored_audits=5,
                      all_source_and_reused_object_identities_unchanged_after_check=True,
                      source_warning_count=record['commands'][1]['output'].count('warning:'))
        save()
        print('Evidence:', work, flush=True)
    except Exception as error:
        record.update(status='FAIL', error=str(error))
        save()
        raise


if __name__ == '__main__':
    main()
