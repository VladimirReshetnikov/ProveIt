#!/usr/bin/env python3
"""Bounded, serial exact246 table source/audit check over one selected Core object.

No dependency builds, downloads, version calls, Mathlib or Foundation providers.
The compiler is inherited by exact identity from a successful existing record.
--prepare-only performs no proof compilation. Source and audit use default Lean
proof limits, one thread, Lean's 4096 MiB limit and a shared 120-second budget.
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
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
EVIDENCE_REL = 'Computability/BusyBeaver/Research/ZFC/results/arithmetic-bootstrap-perm252-verification.json'
CORE_REL = 'Computability/BusyBeaver/Lean/BusyBeaver/Core.lean'
CORE_OBJECT = Path('/tmp/zfc-native91-integration-yduvdh8f/BusyBeaver/Core.olean')
PINS = {'source': 'cb2e5e91150fa40a864ecbe216c7c1c0d21a0bf70f8e9d78b3acdb2a0f046864', 'audit': '2cda7a47d7a000510a9a138382ceb408c31f5eb0fd28934968e7e7775b89527e', 'evidence': '28e997b53772ce9edc13d762950a2fdfc3aa012339232d0ceb91433451841c84', 'core_source': '436336133fa107c62eb00322333ec9451a0705964bd2b62fce3f44ce848672a6', 'core_object': '2c18d0fc971038cdd3cf5998857f56a88ea1cf33cd11f90f6794866fcc2e1148', 'compiler': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550', 'canonical': '89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc', 'old': '303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee', 'renumbering': 'afdba6b5a23a06193977379d9ccfda2748d89da3c3e20faa2f42250a263f9968', 'init': 'd2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'}

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def need(condition, message):
    if not condition: raise RuntimeError(message)
def imports(path): return re.findall(r'^import\s+(\S+)\s*$',path.read_text(),re.M)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=REPO)
    ap.add_argument('--source',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TablePrefix246.lean')
    ap.add_argument('--audit',type=Path,default=HERE/'table_prefix246_audit.lean')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prepare-only',action='store_true')
    a=ap.parse_args()
    repo=a.repo.resolve(); source=a.source.resolve(); audit=a.audit.resolve(); work=a.output.resolve()
    need(not work.exists() or not any(work.iterdir()),'Use new/empty external output.')
    need(not work.is_relative_to(repo),'Output must be outside maintained checkout.')
    evidence=repo/EVIDENCE_REL; core=repo/CORE_REL
    files={'source':source,'audit':audit,'evidence':evidence,'core_source':core,'core_object':CORE_OBJECT,
        'canonical':HERE/'candidate-prefix246/zfc_prefix246.tm','old':HERE/'candidate-prefix246/zfc_prefix246_old.tm',
        'renumbering':HERE/'candidate-prefix246/renumbering.json'}
    for name,path in files.items():need(path.is_file() and sha(path)==PINS[name],'Changed '+name)
    prior=json.loads(evidence.read_text())
    need(prior['status']=='PASS' and prior['all_input_provider_postchecks'] and
        prior['all_fresh_objects_unchanged_after_audit'] and prior['only_standard_axioms'],
        'Selected Core record must be a complete PASS.')
    compiler=Path(prior['compiler']['path'])
    need(compiler.is_absolute() and sha(compiler)==PINS['compiler'],'Wrong compiler binary.')
    need(prior['compiler']['sha256']==PINS['compiler'],'Wrong inherited compiler record.')
    core_rows=[r for r in prior['reused_modules'] if r['module']=='BusyBeaver.Core']
    need(len(core_rows)==1 and core_rows[0]['source_sha256']==PINS['core_source'] and
        core_rows[0]['object_sha256']==PINS['core_object'],'Selected Core binding differs.')
    first=[r for r in prior['actual_first_providers'] if r['module']=='BusyBeaver.Core']
    need(len(first)==1 and Path(first[0]['resolved']).resolve()==CORE_OBJECT.resolve() and
        first[0]['sha256']==PINS['core_object'],'Selected actual Core object differs.')
    need(imports(core)==[] and imports(source)==['BusyBeaver.Core'] and
        imports(audit)==['BusyBeaver.ZFC.TablePrefix246'],'Import closure changed.')
    text=source.read_text(); audit_text=audit.read_text()
    need(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text),'Forbidden source proof shortcut.')
    need(not re.search(r'set_option\s+max(Heartbeats|RecDepth)',text+audit_text),'Use default proof limits.')
    names=re.findall(r'^theorem (\w+)',text,re.M)
    probes=re.findall(r'^#print axioms (.+)$',audit_text,re.M)
    need(len(names)==47 and probes==['SetTheory.BusyBeaver.ZFC.'+n for n in names] and
        len(re.findall(r'^example\b',audit_text,re.M))==47,'Audit contract changed.')
    # Exact source pin plus a separate parser binds each emitted literal row.
    pattern=r'^  \(\((true|false), \.(left|right), (\d+)\), \((true|false), \.(left|right), (\d+)\)\),? -- (\d+); old(\d+)$'
    emitted=re.findall(pattern,text,re.M); need(len(emitted)==246,'Missing emitted table row.')
    actual={}
    for w0,d0,t0,w1,d1,t1,q,old in emitted:
        for b,(w,d,t) in enumerate([(w0,d0,t0),(w1,d1,t1)]):
            need((int(q),b) not in actual,'Duplicate emitted action.')
            actual[int(q),b]=(int(w=='true'),'R' if d=='right' else 'L',int(t))
    expected={}
    for line in files['canonical'].read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();expected[int(q),int(b)]=(int(w),d,int(t))
    need(actual==expected and len(actual)==492,'Emitted actions differ from frozen canonical table.')
    work.mkdir(parents=True,exist_ok=True)
    cache=work/'cache'; (cache/'BusyBeaver/ZFC').mkdir(parents=True)
    (cache/'BusyBeaver/Core.olean').symlink_to(CORE_OBJECT.resolve())
    src=work/'sources/BusyBeaver/ZFC/TablePrefix246.lean';src.parent.mkdir(parents=True)
    shutil.copyfile(source,src); audited=work/'Audit.lean';shutil.copyfile(audit,audited)
    init=compiler.parent.parent/'lib/lean/Init.olean'
    need(init.is_file() and sha(init)==PINS['init'],'Missing/changed implicit Init toolchain provider.')
    all_inputs=list(dict.fromkeys([Path(__file__).resolve(),HERE/'generate_table_prefix246.py',*files.values(),compiler,init]))
    before={str(p):sha(p) for p in all_inputs}
    record=dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING',
        scope='Exact prefix246 finite table and incoming graph only; no runtime or consistency endpoint.',
        source=dict(path=str(source),sha256=sha(source),snapshot=str(src)),
        audit=dict(path=str(audit),sha256=sha(audit),snapshot=str(audited)),
        compiler=prior['compiler'],compiler_version_query_performed=False,
        selected_parent=dict(path=str(evidence),sha256=sha(evidence)),
        reused_modules=[dict(module='BusyBeaver.Core',source=str(core),source_sha256=sha(core),
            object=str(CORE_OBJECT.resolve()),object_sha256=sha(CORE_OBJECT))],
        actual_first_providers=[dict(module='BusyBeaver.Core',actual_first=str(cache/'BusyBeaver/Core.olean'),
            resolved=str(CORE_OBJECT.resolve()),sha256=sha(CORE_OBJECT))],
        toolchain_providers=[dict(module='Init',object=str(init),object_sha256=sha(init),
            scope='Implicit supplied toolchain boundary; not rebuilt.')],
        exact_project_import_closure=True,dependency_build=False,downloads=False,
        LEAN_PATH=str(cache),limits=dict(threads=1,memory_mebibytes=4096,
            shared_wall_seconds=120,proof_limits='Lean defaults'),
        before=before,commands=[],fresh_modules=[],generated_literal_actions_checked=492)
    def save():(work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    def post():
        record['after']={str(p):sha(p) for p in all_inputs}
        need(record['after']==before,'An input/provider changed.')
        need(sha(src)==PINS['source'] and sha(audited)==PINS['audit'],'Snapshot changed.')
        record['all_input_provider_postchecks']=True
    save()
    if a.prepare_only:post();save();print(work/'verification.json');return
    env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
    env.pop('PYTHONOPTIMIZE',None)
    deadline=time.monotonic()+120
    def run(label,command):
        began=time.monotonic(); remaining=deadline-began;need(remaining>0,'Shared wall budget exhausted.')
        log=work/(label+'.log')
        try:
            r=subprocess.run(command,cwd=work,env=env,capture_output=True,text=True,
                timeout=remaining)
        except subprocess.TimeoutExpired as error:
            def decoded(x):return x.decode(errors='replace') if isinstance(x,bytes) else (x or '')
            output=decoded(error.stdout)+decoded(error.stderr);log.write_text(output)
            record['commands'].append(dict(label=label,command=command,cwd=str(work),
                exit_code=None,timed_out=True,seconds=time.monotonic()-began,log=str(log),output=output));save()
            raise
        output=r.stdout+r.stderr;log.write_text(output)
        record['commands'].append(dict(label=label,command=command,cwd=str(work),
            exit_code=r.returncode,seconds=time.monotonic()-began,log=str(log),output=output));save()
        need(r.returncode==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,
            label+' failed; inspect '+str(log))
        return output
    try:
        obj=cache/'BusyBeaver/ZFC/TablePrefix246.olean'
        source_log=run('source',[str(compiler),'-j1','-M4096','--root='+str(work/'sources'),'-o',str(obj),str(src)])
        need(obj.is_file() and not obj.is_symlink(),'Fresh source object missing.')
        fresh=dict(module='BusyBeaver.ZFC.TablePrefix246',path=str(obj),sha256=sha(obj),source_sha256=sha(src))
        record['fresh_modules']=[fresh];record['source_object_recorded_before_audit']=True;save()
        audit_log=run('audit',[str(compiler),'-j1','-M4096',str(audited)])
        reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",audit_log,re.S)
        need([n for n,_ in reports]==probes,'Missing or reordered axiom reports.')
        actual_axiom_sets=[dict(name=n,axioms=[x.strip() for x in block.split(',') if x.strip()])
            for n,block in reports]
        expected_axiom_sets=[dict(name=n,axioms=[] if i<6 else ['propext'])
            for i,n in enumerate(probes)]
        record['actual_axiom_sets']=actual_axiom_sets
        record['expected_axiom_sets']=expected_axiom_sets;save()
        need(actual_axiom_sets==expected_axiom_sets,'Unexpected exact axiom distribution.')
        need(sha(obj)==fresh['sha256'],'Fresh object changed during audit.')
        post();record.update(status='PASS',named_axiom_probes=47,callers=47,no_axioms=False,
            only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,
            warnings=dict(source=source_log.count('warning:'),audit=audit_log.count('warning:')))
    except Exception as error:
        record.update(status='FAIL',error=str(error))
        try:post()
        except Exception as post_error:record['postcheck_error']=str(post_error)
        save();raise
    save();print(work/'verification.json')

if __name__=='__main__':main()
