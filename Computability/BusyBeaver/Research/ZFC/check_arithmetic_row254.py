"""Check the full C254 rule-row arithmetic graph after its three prerequisites.

Freshly check Cantor, constructors, templates, and the row plus stored audits.
Reuse source/object-matched Code254History and its project dependencies; reuse
the explicitly supplied pinned Foundation/Mathlib cache. No download, full core
rebuild, history representation, or internal PA proof is supplied.
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
SOURCE = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticRow254.lean')
MODULE = 'BusyBeaver.ZFC.ArithmeticRow254'
PREFIX = 'SetTheory.BusyBeaver.ZFC.ArithmeticRow254.'
PROBES = ('pred_add_one', 'pred_le', 'mpGate_defined', 'mp_defined', 'bounded_succ_iff', 'predecessor_witness', 'gen_defined', 'payload_fields', 'foundation_sub_nat', 'mpGate_nat', 'mpValue_nat', 'genValue_nat', 'pair_fields', 'payload_fields_flat', 'row_defined', 'rowKernel_nat', 'rowGraph_nat')
CALLERS = 37

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
    prerequisite = repo/RESEARCH/'check_arithmetic_templates254.py'
    spec = importlib.util.spec_from_file_location('checked_templates_helpers', prerequisite)
    if spec is None or spec.loader is None:
        p.error('Maintained template checker is missing.')
    templates = importlib.util.module_from_spec(spec); spec.loader.exec_module(templates)
    code, code_path, base, base_path = templates.load_prerequisite(repo)
    root = a.dependency_root.resolve()
    source = a.source.resolve() if a.source else repo/SOURCE
    audit = a.audit.resolve() if a.audit else script.with_name('arithmetic_row254_audit.lean')
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-arithmetic-row254-check-'))
    if any(work.is_relative_to(q) for q in (repo, root)) or (work.exists() and any(work.iterdir())):
        p.error('Use new/empty scratch outside source and dependency checkouts.')
    work.mkdir(parents=True, exist_ok=True)
    inputs = [script, source, audit, prerequisite, code_path, base_path]
    for name in ('ArithmeticCantor', 'ArithmeticCode254', 'ArithmeticTemplates254'):
        inputs.append(repo/SOURCE.parent/(name+'.lean'))
    inputs += [repo/RESEARCH/(name+'_audit.lean') for name in
               ('arithmetic_cantor','arithmetic_code254','arithmetic_templates254')]
    hashes = {str(q):base.digest(q) for q in inputs}
    record = dict(status='RUNNING', scope='Four fresh arithmetic modules and audits. Exact gated12-row graph with explicit child values, for all IOpen models and all Nat inputs. No history/outer-selector/PA proof.',
                  repo=str(repo), scratch=str(work), inputs=hashes, commands=[],
                  dependency_rebuild=False, downloads=False, main_runner_or_umbrella_modified=False)
    def save():
        (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1'); env.pop('PYTHONOPTIMIZE',None)
    def run(label, command):
        start=time.monotonic(); r=subprocess.run(command,cwd=work,env=env,capture_output=True,text=True)
        output=r.stdout+r.stderr; log=work/(label+'.log'); log.write_text(output)
        record['commands'].append(dict(label=label,command=command,cwd=str(work),exit_code=r.returncode,
                                      seconds=round(time.monotonic()-start,6),log=str(log),output=output))
        save(); base.fail(r.returncode==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,
                         f'{label} failed; inspect {log}')
        print(label,'PASS',record['commands'][-1]['seconds'],'seconds',flush=True)
        return output
    save()
    try:
        base.fail(PROBES and CALLERS > 0, 'The maintained audit must have an explicit probe/caller contract.')
        base.fail(re.findall(r'^#print axioms (.+)$',audit.read_text(),re.M)==[PREFIX+n for n in PROBES]
                  and len(re.findall(r'^example\b',audit.read_text(),re.M))==CALLERS, 'Unexpected stored row audit.')
        command=[sys.executable,'-B',str(prerequisite),'--repo',str(repo),'--dependency-root',str(root),
                 '--core-evidence',str(a.core_evidence.resolve()),'--output',str(work/'templates')]
        for flag,value in (('--core-cache',a.core_cache),('--lean',a.lean)):
            if value is not None: command += [flag,str(value.resolve())]
        for value in a.library_path: command += ['--library-path',str(value.resolve())]
        run('template-prerequisite',command)
        prior_path=work/'templates/verification.json'; prior=json.loads(prior_path.read_text())
        base.fail(prior.get('status')=='PASS' and prior['total_named_axiom_probes']==97
                  and prior['total_callers']==83 and prior['only_standard_axioms'], 'Incomplete prerequisite checks.')
        env.update(LEAN_PATH=prior['LEAN_PATH'],LEAN_NUM_THREADS='1')
        cache=Path(env['LEAN_PATH'].split(os.pathsep)[0])
        evidence=json.loads(a.core_evidence.read_text())
        core_cache=a.core_cache.resolve() if a.core_cache else Path(evidence['cache'])
        rows={q['path'].split('/Lean/',1)[1].removesuffix('.lean').replace('/','.'):q
              for q in evidence['source_closure']}
        reused={q['module']:dict(q) for q in prior['reused_core']}
        visiting=set()
        def visit(module):
            base.fail(module not in visiting, 'Core dependency cycle.')
            row=rows[module]; path=repo/row['path']
            obj=core_cache/Path(module.replace('.','/')).with_suffix('.olean')
            base.fail(base.digest(path)==row['sha256'] and base.digest(obj)==row['olean_sha256'],
                      f'Core source/object differs from successful evidence: {module}')
            if module in reused:
                base.fail(reused[module]['olean_sha256']==row['olean_sha256'], 'Prerequisite core object mismatch.')
                return
            visiting.add(module)
            for imported in base.lean_imports(path.read_text()):
                if imported in rows: visit(imported)
                else: base.fail(imported in {'Init','Std','Lean'} or imported.startswith(('Init.','Std.','Lean.')),
                                'Unexpected external import in history closure.')
            target=cache/Path(module.replace('.','/')).with_suffix('.olean')
            base.fail(not target.exists(), 'Unexpected existing history object in arithmetic cache.')
            target.parent.mkdir(parents=True,exist_ok=True); target.symlink_to(obj.resolve())
            reused[module]=dict(module=module,path=row['path'],source_sha256=row['sha256'],
                                olean=str(target),olean_sha256=row['olean_sha256'])
            visiting.remove(module)
        # Validate every reused core object against its recorded successful hash,
        # then add exactly the actual history closure, never a stub.
        for module in list(reused): visit(module)
        visit('BusyBeaver.ZFC.Code254History')
        record.update(compiler=prior['compiler'], dependencies=prior['dependencies'],
                      core_evidence=dict(path=str(a.core_evidence.resolve()),sha256=base.digest(a.core_evidence)),
                      reused_core=list(reused.values()), fresh_prerequisite=prior, LEAN_PATH=env['LEAN_PATH'])
        snapshot=work/'sources/BusyBeaver/ZFC/ArithmeticRow254.lean';snapshot.parent.mkdir(parents=True)
        shutil.copyfile(source,snapshot); audit_copy=work/'arithmetic_row254_audit.lean';shutil.copyfile(audit,audit_copy)
        compiler=Path(prior['compiler']['path']);compiler_hash=base.digest(compiler)
        obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean')
        run('source',[str(compiler),'--root='+str(work/'sources'),'-o',str(obj),str(snapshot)])
        output=run('audit',[str(compiler),str(audit_copy)])
        parsed=[]
        for name,block in re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",output,re.S):
            axioms=[x.strip() for x in block.split(',') if x.strip()]
            base.fail(set(axioms)<=base.STANDARD_AXIOMS,'Unexpected axioms: '+name)
            parsed.append(dict(theorem=name,axioms=axioms))
        base.fail(len(parsed)==len(PROBES) and {q['theorem'] for q in parsed}=={PREFIX+n for n in PROBES},
                  'Missing, duplicate, or unexpected row axiom report.')
        base.fail(all(base.digest(Path(q))==h for q,h in hashes.items()), 'A source/audit/helper changed.')
        base.fail(all(base.digest(repo/q['path'])==q['source_sha256'] and base.digest(Path(q['olean']))==q['olean_sha256']
                      for q in reused.values()), 'A reused core source/object changed.')
        for entry in (prior['module_object'],prior['fresh_prerequisite']['object'],prior['fresh_prerequisite']['cantor']['object']):
            base.fail(base.digest(Path(entry['path']))==entry['sha256'],'A fresh arithmetic prerequisite changed.')
        base.fail(base.digest(compiler)==compiler_hash,'Compiler changed.')
        record.update(status='PASS',source=dict(path=str(source),sha256=hashes[str(source)],snapshot=str(snapshot)),
                      audit_source=dict(path=str(audit),sha256=hashes[str(audit)],source=audit.read_text()),
                      module_object=dict(path=str(obj),sha256=base.digest(obj)),compiler_binary_sha256=compiler_hash,
                      axiom_reports=parsed,named_axiom_probes=len(PROBES),callers=CALLERS,
                      total_named_axiom_probes=97+len(PROBES),total_callers=83+CALLERS,only_standard_axioms=True,
                      fresh_modules=prior['fresh_modules']+[MODULE],fresh_stored_audits=4,
                      all_source_and_reused_object_identities_unchanged_after_check=True,
                      source_warning_count=record['commands'][1]['output'].count('warning:'))
        save();print('Evidence:',work,flush=True)
    except Exception as error:
        record.update(status='FAIL',error=str(error));save();raise

if __name__=='__main__': main()
