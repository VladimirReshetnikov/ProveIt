"""Check the constructor/rho1 arithmetic package in a separate dependency lane.

Reuse check_arithmetic_cantor.py for pinned compiler/dependency discovery,
source-matched core cache validation and a fresh Cantor source/audit check.
Then compile only ArithmeticCode254 and its stored29-probe/27-caller audit in
that temporary cache. No core/Foundation/Mathlib dependency is rebuilt or
fetched; the Std-only runner and umbrella are not used or changed.
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
SOURCE = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCode254.lean')
MODULE = 'BusyBeaver.ZFC.ArithmeticCode254'
PREFIX = 'SetTheory.BusyBeaver.ZFC.ArithmeticCode254.'
PROBES = (
    'cantor_polybound', 'cantor_bounded', 'pair_le_tagged', 'tagged_components',
    'tagged_bounded', 'tagged_defined', 'wim_defined', 'wel_defined', 'wal_defined',
    'weq_defined', 'tagged_nat', 'wim_nat', 'wel_nat', 'wal_nat', 'weq_nat',
    'rho1_defined', 'rho1_nat', 'rho1Value_defined', 'rho1Value_nat',
    'rho1_input_bounds', 'row3_defined', 'row3_nat', 'codeWim_defined',
    'codeWel_defined', 'codeWal_defined', 'codeWeq_defined', 'codeRho1_defined',
    'codeRho1Value_defined', 'codeRow3_defined',
)


def load_base(repo: Path):
    path = repo/RESEARCH/'check_arithmetic_cantor.py'
    spec = importlib.util.spec_from_file_location('checked_cantor_helpers', path)
    if spec is None or spec.loader is None:
        raise ValueError('Maintained check_arithmetic_cantor.py is missing.')
    base = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(base)
    return base, path


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path)
    p.add_argument('--dependency-root', type=Path, required=True)
    p.add_argument('--core-evidence', type=Path, required=True)
    p.add_argument('--core-cache', type=Path)
    p.add_argument('--library-path', type=Path, action='append', default=[])
    p.add_argument('--lean', type=Path)
    p.add_argument('--source', type=Path, help='candidate ArithmeticCode254 source override')
    p.add_argument('--audit', type=Path, help='stored constructor/rho1 audit override')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    if not __debug__:
        p.error('Keep assertions enabled; do not use -O.')
    repo = a.repo.resolve() if a.repo else next((q for q in Path(__file__).resolve().parents if (q/'.git').exists()), None)
    if repo is None:
        p.error('Pass --repo when running outside the checkout.')
    base, base_path = load_base(repo)
    root = a.dependency_root.resolve()
    source = a.source.resolve() if a.source else repo/SOURCE
    audit = a.audit.resolve() if a.audit else Path(__file__).with_name('arithmetic_code254_audit.lean')
    cantor_source = repo/base.SOURCE
    cantor_audit = base_path.with_name('arithmetic_cantor_audit.lean')
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-arithmetic-code254-check-'))
    if any(work.is_relative_to(q) for q in (repo, root)) or (work.exists() and any(work.iterdir())):
        p.error('Use new/empty scratch outside both source and dependency checkouts.')
    work.mkdir(parents=True, exist_ok=True)
    record = dict(status='RUNNING', scope='Fresh Cantor and constructor/rho1 sources and stored audits, with cached core/Foundation/Mathlib. No full12-row/history/PA endpoint.',
                  repo=str(repo), scratch=str(work), runner=dict(path=str(Path(__file__).resolve()),sha256=base.digest(Path(__file__).resolve())),
                  shared_helper=dict(path=str(base_path),sha256=base.digest(base_path)),
                  dependency_rebuild=False,downloads=False,main_runner_or_umbrella_modified=False,commands=[])
    def save():
        (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    def run(label, command, env):
        start=time.monotonic()
        result=subprocess.run(command,cwd=work,env=env,capture_output=True,text=True)
        output=result.stdout+result.stderr;log=work/(label+'.log');log.write_text(output)
        row=dict(label=label,command=command,cwd=str(work),exit_code=result.returncode,
                 seconds=round(time.monotonic()-start,6),log=str(log),output=output)
        record['commands'].append(row);save()
        base.fail(result.returncode==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,
                  f'{label} failed; inspect {log}')
        print(label,'PASS',row['seconds'],'seconds',flush=True)
        return output
    try:
        base.fail(all(q.is_file() for q in (source,audit,cantor_source,cantor_audit)), 'Maintained/candidate arithmetic source or stored audit is missing.')
        hashes={str(q):base.digest(q) for q in (source,audit,cantor_source,cantor_audit,base_path)}
        base.fail(len(re.findall(r'^example\b',audit.read_text(),re.M))==27, 'Expected the stored27-caller constructor audit.')
        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
        cmd=[sys.executable,'-B',str(base_path),'--repo',str(repo),'--dependency-root',str(root),
             '--core-evidence',str(a.core_evidence.resolve()),'--output',str(work/'cantor'),
             '--source',str(cantor_source),'--audit',str(cantor_audit)]
        for flag,value in (('--core-cache',a.core_cache),('--lean',a.lean)):
            if value is not None:cmd.extend([flag,str(value.resolve())])
        for value in a.library_path:cmd.extend(['--library-path',str(value.resolve())])
        run('cantor-prerequisite',cmd,env)
        prior_path=work/'cantor/verification.json';prior=json.loads(prior_path.read_text())
        base.fail(prior.get('status')=='PASS' and prior.get('named_axiom_probes')==27 and prior.get('callers')==20,
                  'Fresh prerequisite did not complete its27 probes and20 callers.')
        record.update(compiler=prior['compiler'],dependencies=prior['dependencies'],core_evidence=prior['core_evidence'],
                      reused_core=prior['reused_core'],
                      fresh_prerequisite=dict(evidence=str(prior_path),sha256=base.digest(prior_path),
                          source=prior['source'],audit=prior['audit_source'],object=prior['module_object'],
                          named_axiom_probes=27,callers=20,only_standard_axioms=prior['only_standard_axioms']))
        env.update(LEAN_PATH=prior['LEAN_PATH'],LEAN_NUM_THREADS='1');record['LEAN_PATH']=env['LEAN_PATH']
        snapshot=work/'sources/BusyBeaver/ZFC/ArithmeticCode254.lean'
        snapshot.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,snapshot)
        audit_snapshot=work/'arithmetic_code254_audit.lean';shutil.copyfile(audit,audit_snapshot)
        record['source']=dict(path=str(source),sha256=hashes[str(source)],snapshot=str(snapshot))
        record['audit_source']=dict(path=str(audit),sha256=hashes[str(audit)],snapshot=str(audit_snapshot),callers=27)
        cache=Path(env['LEAN_PATH'].split(os.pathsep)[0]);obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean')
        compiler=prior['compiler']['path']
        run('source',[compiler,'--root='+str(work/'sources'),'-o',str(obj),str(snapshot)],env)
        output=run('audit',[compiler,str(audit_snapshot)],env)
        parsed=[]
        pattern=r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
        for name,block in re.findall(pattern,output,re.S):
            axioms=[q.strip() for q in block.split(',') if q.strip()]
            base.fail(set(axioms)<=base.STANDARD_AXIOMS,f'Unexpected axioms for {name}: {axioms}')
            parsed.append(dict(theorem=name,axioms=axioms))
        base.fail(len(parsed)==29 and {q['theorem'] for q in parsed}=={PREFIX+n for n in PROBES},
                  'Missing, duplicate or unexpected constructor/rho1 axiom report.')
        base.fail(all(base.digest(Path(path))==sha for path,sha in hashes.items()), 'An arithmetic source/audit/helper changed during the check.')
        base.fail(base.digest(Path(prior['module_object']['path']))==prior['module_object']['sha256'], 'Fresh Cantor object changed during the constructor check.')
        base.fail(all(base.digest(repo/q['path'])==q['source_sha256'] and base.digest(Path(q['olean']))==q['olean_sha256'] for q in prior['reused_core']),
                  'A reused core source/object changed during the constructor check.')
        record.update(status='PASS',axiom_reports=parsed,named_axiom_probes=29,callers=27,
                      total_named_axiom_probes=56,total_callers=47,only_standard_axioms=True,
                      fresh_modules=['BusyBeaver.ZFC.ArithmeticCantor',MODULE],fresh_stored_audits=2,
                      module_object=dict(path=str(obj),sha256=base.digest(obj)),new_arithmetic_assumptions=False,
                      all_source_and_reused_object_identities_unchanged_after_check=True,
                      linter_warnings=sum('warning:' in line for line in record['commands'][1]['output'].splitlines()))
        save();print('Evidence:',work,flush=True)
    except Exception as error:
        record.update(status='FAIL',error=str(error));save();raise


if __name__=='__main__':main()
