"""Check the fixed-template arithmetic package in a separate dependency lane.

Run the maintained constructor/rho1 checker first, which freshly checks Cantor
and constructor sources plus their stored audits. Then freshly check the fixed
rho2..8/C/G/full-bundle circuits and41-probe/36-caller audit in that same
scratch cache. Core, Foundation and Mathlib objects are explicitly reused;
no dependency is built/fetched and the Std-only runner/umbrella is untouched.
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
SOURCE = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticTemplates254.lean')
MODULE = 'BusyBeaver.ZFC.ArithmeticTemplates254'
PREFIX = 'SetTheory.BusyBeaver.ZFC.ArithmeticTemplates254.'
FUNCTIONS = tuple('rho'+str(n) for n in range(2,9))+('bundleC','bundleG','bundle')
PROBES = ('bounded_tagged_iff','Circuit.defined')+tuple(
    'Circuit.eval_'+n for n in ('im','el','al','eq','input0','input1','input2','input3','one'))+tuple(
    name for n in FUNCTIONS for name in (n+'_defined',n+'_nat','code'+n[0].upper()+n[1:]+'_defined'))


def load_prerequisite(repo: Path):
    path = repo/RESEARCH/'check_arithmetic_code254.py'
    spec = importlib.util.spec_from_file_location('checked_code254_helpers', path)
    if spec is None or spec.loader is None:
        raise ValueError('Maintained check_arithmetic_code254.py is missing.')
    code = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(code)
    base, base_path = code.load_base(repo)
    return code, path, base, base_path


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path)
    p.add_argument('--dependency-root', type=Path, required=True)
    p.add_argument('--core-evidence', type=Path, required=True)
    p.add_argument('--core-cache', type=Path)
    p.add_argument('--library-path', type=Path, action='append', default=[])
    p.add_argument('--lean', type=Path)
    p.add_argument('--source', type=Path, help='candidate ArithmeticTemplates254 source override')
    p.add_argument('--audit', type=Path, help='stored fixed-template audit override')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    if not __debug__:
        p.error('Keep assertions enabled; do not use -O.')
    repo = a.repo.resolve() if a.repo else next((q for q in Path(__file__).resolve().parents if (q/'.git').exists()), None)
    if repo is None:
        p.error('Pass --repo when running outside the checkout.')
    code, code_path, base, base_path = load_prerequisite(repo)
    root = a.dependency_root.resolve()
    source = a.source.resolve() if a.source else repo/SOURCE
    audit = a.audit.resolve() if a.audit else Path(__file__).with_name('arithmetic_templates254_audit.lean')
    code_source = repo/code.SOURCE
    code_audit = code_path.with_name('arithmetic_code254_audit.lean')
    cantor_source = repo/base.SOURCE
    cantor_audit = base_path.with_name('arithmetic_cantor_audit.lean')
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-arithmetic-templates254-check-'))
    if any(work.is_relative_to(q) for q in (repo, root)) or (work.exists() and any(work.iterdir())):
        p.error('Use new/empty scratch outside both source and dependency checkouts.')
    work.mkdir(parents=True, exist_ok=True)
    record = dict(status='RUNNING', scope='Fresh Cantor, constructor/rho1 and fixed-template sources/audits; exact positive rho1..8/C/G/full-bundle arithmetic graphs. Cached core/Foundation/Mathlib. No gated12-row/history/PA endpoint.',
                  repo=str(repo), scratch=str(work), runner=dict(path=str(Path(__file__).resolve()),sha256=base.digest(Path(__file__).resolve())),
                  prerequisite_checker=dict(path=str(code_path),sha256=base.digest(code_path)),
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
        inputs=(source,audit,code_source,code_audit,cantor_source,cantor_audit,code_path,base_path)
        base.fail(all(q.is_file() for q in inputs), 'Maintained/candidate arithmetic source, stored audit or helper is missing.')
        hashes={str(q):base.digest(q) for q in inputs}
        base.fail(len(PROBES)==41 and len(re.findall(r'^example\b',audit.read_text(),re.M))==36,
                  'Expected the stored41-probe/36-caller fixed-template audit.')
        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
        cmd=[sys.executable,'-B',str(code_path),'--repo',str(repo),'--dependency-root',str(root),
             '--core-evidence',str(a.core_evidence.resolve()),'--output',str(work/'constructors'),
             '--source',str(code_source),'--audit',str(code_audit)]
        for flag,value in (('--core-cache',a.core_cache),('--lean',a.lean)):
            if value is not None:cmd.extend([flag,str(value.resolve())])
        for value in a.library_path:cmd.extend(['--library-path',str(value.resolve())])
        run('constructor-prerequisite',cmd,env)
        prior_path=work/'constructors/verification.json';prior=json.loads(prior_path.read_text())
        base.fail(prior.get('status')=='PASS' and prior.get('named_axiom_probes')==29 and prior.get('callers')==27
                  and prior.get('total_named_axiom_probes')==56 and prior.get('total_callers')==47,
                  'Fresh prerequisite did not complete all56 probes and47 callers.')
        cantor=prior['fresh_prerequisite']
        base.fail(cantor['named_axiom_probes']==27 and cantor['callers']==20 and cantor['only_standard_axioms'],
                  'Fresh Cantor prerequisite metadata is incomplete.')
        record.update(compiler=prior['compiler'],dependencies=prior['dependencies'],core_evidence=prior['core_evidence'],
                      reused_core=prior['reused_core'],
                      fresh_prerequisite=dict(evidence=str(prior_path),sha256=base.digest(prior_path),
                          source=prior['source'],audit=prior['audit_source'],object=prior['module_object'],
                          total_named_axiom_probes=56,total_callers=47,only_standard_axioms=prior['only_standard_axioms'],
                          cantor=cantor))
        env.update(LEAN_PATH=prior['LEAN_PATH'],LEAN_NUM_THREADS='1');record['LEAN_PATH']=env['LEAN_PATH']
        snapshot=work/'sources/BusyBeaver/ZFC/ArithmeticTemplates254.lean'
        snapshot.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,snapshot)
        audit_snapshot=work/'arithmetic_templates254_audit.lean';shutil.copyfile(audit,audit_snapshot)
        record['source']=dict(path=str(source),sha256=hashes[str(source)],snapshot=str(snapshot))
        record['audit_source']=dict(path=str(audit),sha256=hashes[str(audit)],snapshot=str(audit_snapshot),callers=36)
        cache=Path(env['LEAN_PATH'].split(os.pathsep)[0]);obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean')
        compiler=prior['compiler']['path'];compiler_hash=base.digest(Path(compiler))
        record['compiler_binary_sha256']=compiler_hash
        run('source',[compiler,'--root='+str(work/'sources'),'-o',str(obj),str(snapshot)],env)
        output=run('audit',[compiler,str(audit_snapshot)],env)
        parsed=[]
        pattern=r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
        for name,block in re.findall(pattern,output,re.S):
            axioms=[q.strip() for q in block.split(',') if q.strip()]
            base.fail(set(axioms)<=base.STANDARD_AXIOMS,f'Unexpected axioms for {name}: {axioms}')
            parsed.append(dict(theorem=name,axioms=axioms))
        base.fail(len(parsed)==41 and {q['theorem'] for q in parsed}=={PREFIX+n for n in PROBES},
                  'Missing, duplicate or unexpected fixed-template axiom report.')
        base.fail(all(base.digest(Path(path))==sha for path,sha in hashes.items()), 'An arithmetic source/audit/helper changed during the check.')
        for entry in (prior['module_object'],cantor['object']):
            base.fail(base.digest(Path(entry['path']))==entry['sha256'], 'A fresh prerequisite object changed during the template check.')
        base.fail(all(base.digest(repo/q['path'])==q['source_sha256'] and base.digest(Path(q['olean']))==q['olean_sha256'] for q in prior['reused_core']),
                  'A reused core source/object changed during the template check.')
        base.fail(base.digest(Path(compiler))==compiler_hash, 'The compiler binary changed during the template check.')
        record.update(status='PASS',axiom_reports=parsed,named_axiom_probes=41,callers=36,
                      total_named_axiom_probes=97,total_callers=83,only_standard_axioms=True,
                      fresh_modules=prior['fresh_modules']+[MODULE],fresh_stored_audits=3,
                      module_object=dict(path=str(obj),sha256=base.digest(obj)),new_arithmetic_assumptions=False,
                      all_source_and_reused_object_identities_unchanged_after_check=True,
                      linter_warnings=sum('warning:' in line for line in record['commands'][1]['output'].splitlines()))
        save();print('Evidence:',work,flush=True)
    except Exception as error:
        record.update(status='FAIL',error=str(error));save();raise


if __name__=='__main__':main()
