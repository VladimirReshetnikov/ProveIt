#!/usr/bin/env python3
"""Check exact routing245 fast lookup using the checked table and Core providers.

No dependency build, download, compiler-version query or proof-limit changes.
Source and audit share 120 seconds, serial -j1 and -M4096. --prepare-only
records a fresh isolated import cache and snapshots without invoking Lean.
Historical cached providers are required; this is not a clean-checkout build.
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
MODULE = 'BusyBeaver.ZFC.FastTableRouting245'
TABLE_MODULE = 'BusyBeaver.ZFC.TableRouting245'
PARENT_REL = 'Computability/BusyBeaver/Research/ZFC/results/table-routing245-verification.json'
PROBES = ['SetTheory.BusyBeaver.ZFC.FastTableRouting245.'+n
          for n in ['fast_transition_eq','fastMachine_eq']]
PINS = {
    'source': 'bcacf9874bf3439c538c8544a724caac2f817e52b58eaaf07f0806666d4dde64',
    'audit': 'b85452b8993b269c3b9bd767b4bf518ca73c0f87b41f679f6af144350ae194e1',
    'generator': 'b4e9c43c8098ac1ed9035fb047b62ff59bc6fc0191a89d113e51bc4195b2cc77',
    'canonical': '17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13',
    'parent': 'bb53b70f1a775b915d9b335a4ce1378c8350f771aca6aa007c0227989fd87281',
    'table_source': 'a00da51f6c813bdbb9ff573ba75a0a6cb1e7f1eb9d630758b5b1bfed4a5b673b',
    'table_object': '4dc4e2697143378811e5d6be4de65527df37534abcc97baa91d3d23665cc3b6b',
    'parent_audit': 'c31149ed1cc480deb84737f18f82212742f5abc296062aa3f6a7cded4e788796',
    'core_source': '436336133fa107c62eb00322333ec9451a0705964bd2b62fce3f44ce848672a6',
    'core_object': '2c18d0fc971038cdd3cf5998857f56a88ea1cf33cd11f90f6794866fcc2e1148',
    'compiler': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    'init': 'd2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e',
}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def imports(path):
    return re.findall(r'^import\s+(\S+)\s*$',path.read_text(),re.M)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=REPO)
    ap.add_argument('--source',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/FastTableRouting245.lean')
    ap.add_argument('--audit',type=Path,default=HERE/'fast_table_routing245_audit.lean')
    ap.add_argument('--generator',type=Path,default=HERE/'generate_fast_routing245.py')
    ap.add_argument('--canonical',type=Path)
    ap.add_argument('--parent',type=Path)
    ap.add_argument('--table-source',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prepare-only',action='store_true')
    a = ap.parse_args()
    repo,work = a.repo.resolve(),a.output.resolve()
    need(not work.is_relative_to(repo) and (not work.exists() or not any(work.iterdir())),
         'Use new/empty external output.')
    files = dict(source=a.source.resolve(),audit=a.audit.resolve(),generator=a.generator.resolve(),
        canonical=(a.canonical or repo/'Computability/BusyBeaver/Research/ZFC/candidate-routing245/zfc_routing245.tm').resolve(),
        parent=(a.parent or repo/PARENT_REL).resolve(),
        table_source=(a.table_source or repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TableRouting245.lean').resolve())
    for key,path in files.items():
        need(path.is_file() and sha(path)==PINS[key], 'Changed '+key)
    source,audit = files['source'],files['audit']
    prior = json.loads(files['parent'].read_text())
    need(prior['status']=='PASS' and prior['named_axiom_probes']==64 and prior['callers']==64 and
         prior['only_standard_axioms'] is True and prior['all_input_provider_postchecks'] is True and
         prior['all_fresh_objects_unchanged_after_audit'] is True and prior['before']==prior['after'],
         'Selected table parent is not a complete PASS.')
    need([r['label'] for r in prior['commands']]==['source','audit'] and
         all(r['exit_code']==0 and not r.get('timed_out',False) for r in prior['commands']),
         'Selected parent source/audit failed.')
    need(prior['source_object_recorded_before_audit'] is True and
         prior['source']['sha256']==PINS['table_source'] and prior['audit']['sha256']==PINS['parent_audit'],
         'Selected parent lacks its pre-audit binding.')
    need(len(prior['reused_modules'])==len(prior['fresh_modules'])==1 and
         prior['reused_modules'][0]['module']=='BusyBeaver.Core' and
         prior['fresh_modules'][0]['module']==TABLE_MODULE, 'Unexpected selected project closure.')
    core,fresh = prior['reused_modules'][0],prior['fresh_modules'][0]
    need(core['source_sha256']==PINS['core_source'] and core['object_sha256']==PINS['core_object'] and
         fresh['source_sha256']==PINS['table_source'] and fresh['sha256']==PINS['table_object'],
         'Parent source/object pair differs.')
    need(prior['source_pass_object']==dict(fresh,source_command_index=0), 'Parent source-pass object differs.')
    first = prior['fresh_first_provider_before_audit']
    need(first['module']==TABLE_MODULE and first['sha256']==PINS['table_object'] and
         Path(first['actual_first']).resolve()==Path(first['resolved']).resolve()==Path(fresh['path']).resolve(),
         'Parent fresh first provider differs.')
    parent_core = prior['actual_first_providers']
    need(len(parent_core)==1 and parent_core[0]['module']=='BusyBeaver.Core' and
         parent_core[0]['sha256']==PINS['core_object'] and
         Path(parent_core[0]['resolved']).resolve()==Path(core['object']).resolve(),
         'Parent selected a different Core provider.')
    files.update(core_source=Path(core['source']).resolve(),core_object=Path(core['object']).resolve(),
        table_object=Path(fresh['path']).resolve(),
        parent_source_snapshot=Path(prior['source']['snapshot']).resolve(),
        parent_audit=Path(prior['audit']['snapshot']).resolve(),
        compiler=Path(prior['compiler']['path']).resolve())
    files['init'] = files['compiler'].parent.parent/'lib/lean/Init.olean'
    for key,path in files.items():
        expected = PINS['table_source'] if key=='parent_source_snapshot' else PINS[key]
        need(path.is_file() and sha(path)==expected, 'Changed '+key)
        need(not path.is_relative_to(work), 'Input is inside output: '+key)
    need(prior['compiler']['sha256']==PINS['compiler'], 'Compiler identity differs.')
    need(len(prior['toolchain_providers'])==1 and prior['toolchain_providers'][0]['module']=='Init' and
         prior['toolchain_providers'][0]['object_sha256']==PINS['init'], 'Init boundary differs.')
    selected = [dict(module='BusyBeaver.Core',source=str(files['core_source']),source_sha256=PINS['core_source'],
                    object=str(files['core_object']),object_sha256=PINS['core_object']),
                dict(module=TABLE_MODULE,source=str(files['table_source']),source_sha256=PINS['table_source'],
                    object=str(files['table_object']),object_sha256=PINS['table_object'])]
    need(imports(files['core_source'])==[] and imports(files['table_source'])==['BusyBeaver.Core'] and
         imports(source)==[TABLE_MODULE] and imports(audit)==[MODULE], 'Project import closure changed.')
    st,at = source.read_text(),audit.read_text()
    need(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',st), 'Forbidden source proof shortcut.')
    need(not re.search(r'\b(sorry|admit|native_decide)\b',at), 'Forbidden audit proof shortcut.')
    need(not re.search(r'\bset_option\b',st+at), 'Use default proof options.')
    need(re.findall(r'^theorem (\w+)',st,re.M)==['fast_transition_eq','fastMachine_eq'] and
         re.findall(r'^#print axioms (.+)$',at,re.M)==PROBES and
         len(re.findall(r'^example\b',at,re.M))==4, 'Exact 2-probe/4-caller contract changed.')
    tree = st.split('def fastTree : TransitionTree 245 :=\n',1)[1].split('\ndef fastMachine',1)[0]
    need(tree.count('.leaf ')==245 and tree.count('.branch')==244, 'Tree census differs.')
    rows,start = {},None
    for line in files['canonical'].read_text().splitlines():
        if line.startswith('#! start '):
            need(start is None,'Duplicate start declaration.');start=int(line.split()[-1])
        if not line or line.startswith('#'):
            continue
        q,b,w,d,t = line.split();q,b,w,t = map(int,(q,b,w,t))
        need((q,b) not in rows and b in (0,1) and w in (0,1) and d in ('L','R') and 0<=t<=245,
             'Invalid canonical action.')
        rows[q,b] = w,d,t
    need(start==0 and set(rows)=={(q,b) for q in range(245) for b in (0,1)}, 'Canonical census differs.')
    work.mkdir(parents=True,exist_ok=True)
    cache = work/'cache';actual = []
    for row in selected:
        dest = cache/Path(row['module'].replace('.','/')).with_suffix('.olean')
        dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(row['object']))
        actual.append(dict(module=row['module'],actual_first=str(dest),resolved=str(dest.resolve()),sha256=sha(dest)))
    snap = work/'sources'/Path(MODULE.replace('.','/')).with_suffix('.lean')
    snap.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,snap)
    aud = work/'Audit.lean';shutil.copyfile(audit,aud)
    inputs = list(dict.fromkeys([Path(__file__).resolve(),*files.values()]))
    before = {str(p):sha(p) for p in inputs}
    record = dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING',prepare_only=a.prepare_only,
        scope='Exact routing245 balanced lookup and all-state/whole-machine equality; no bootstrap, interpreter or consistency endpoint.',
        source=dict(path=str(source),sha256=sha(source),snapshot=str(snap)),
        audit=dict(path=str(audit),sha256=sha(audit),snapshot=str(aud)),
        compiler=dict(prior['compiler'],path=str(files['compiler'])),compiler_version_query_performed=False,
        parent_evidence=[dict(path=str(files['parent']),sha256=sha(files['parent']))],
        reused_modules=selected,actual_first_providers=actual,
        toolchain_providers=[dict(module='Init',object=str(files['init']),object_sha256=sha(files['init']),
            scope='Supplied implicit toolchain boundary; not rebuilt.')],
        exact_project_import_closure=True,project_module_count=2,external_boundary_count=0,
        actual_direct_tool_imports=[],LEAN_PATH=str(cache),before=before,commands=[],fresh_modules=[],
        dependency_build=False,downloads=False,
        limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),
        expected_named_axiom_probes=2,expected_callers=4,canonical_actions=490,tree_leaves=245,tree_branches=244)
    def save():
        (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    def post():
        record['after'] = {str(p):sha(p) for p in inputs}
        need(record['after']==before, 'Input/provider changed.')
        need(sha(snap)==PINS['source'] and sha(aud)==PINS['audit'], 'Source/audit snapshot changed.')
        for row in selected:
            dest = cache/Path(row['module'].replace('.','/')).with_suffix('.olean')
            need(dest.is_symlink() and dest.resolve()==Path(row['object']) and sha(dest)==row['object_sha256'],
                 'Actual first provider changed: '+row['module'])
        need(not (cache/'Init.olean').exists(), 'Implicit Init shadowed.')
        record['all_input_provider_postchecks'] = True
    save()
    try:
        if a.prepare_only:
            post();save();print(work/'verification.json');return
        compiler = files['compiler']
        env = dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',
                   LEAN_SYSROOT=str(compiler.parent.parent),PYTHONDONTWRITEBYTECODE='1')
        env.pop('PYTHONOPTIMIZE',None)
        deadline = time.monotonic()+120
        def run(label,command):
            began = time.monotonic();remaining = deadline-began
            need(remaining>0, 'Shared 120-second wall budget exhausted.')
            log = work/(label+'.log')
            try:
                result = subprocess.run(command,cwd=work,env=env,capture_output=True,text=True,timeout=remaining)
            except subprocess.TimeoutExpired as error:
                def decoded(x):
                    return x.decode(errors='replace') if isinstance(x,bytes) else (x or '')
                output = decoded(error.stdout)+decoded(error.stderr);log.write_text(output)
                record['commands'].append(dict(label=label,command=command,cwd=str(work),exit_code=None,
                    timed_out=True,seconds=time.monotonic()-began,log=str(log),output=output));save();raise
            output = result.stdout+result.stderr;log.write_text(output)
            record['commands'].append(dict(label=label,command=command,cwd=str(work),exit_code=result.returncode,
                seconds=time.monotonic()-began,log=str(log),output=output));save()
            need(result.returncode==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,
                 label+' failed; inspect '+str(log))
            return output
        obj = cache/Path(MODULE.replace('.','/')).with_suffix('.olean')
        source_log = run('source',[str(compiler),'-j1','-M4096','--root='+str(work/'sources'),'-o',str(obj),str(snap)])
        need(obj.is_file() and not obj.is_symlink(), 'Fresh source object missing.')
        fresh = dict(module=MODULE,path=str(obj),sha256=sha(obj),source_sha256=sha(snap))
        record['fresh_modules'] = [fresh]
        record['source_pass_object'] = dict(fresh,source_command_index=0)
        record['source_object_recorded_before_audit'] = True
        record['fresh_first_provider_before_audit'] = dict(module=MODULE,actual_first=str(obj),
            resolved=str(obj.resolve()),sha256=sha(obj))
        save()
        audit_log = run('audit',[str(compiler),'-j1','-M4096',str(aud)])
        reports = re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",audit_log,re.S)
        need([name for name,_ in reports]==PROBES, 'Missing/reordered axiom reports.')
        axioms = [dict(name=name,axioms=[x.strip() for x in block.split(',') if x.strip()]) for name,block in reports]
        expected = [dict(name=PROBES[0],axioms=[]),dict(name=PROBES[1],axioms=['Quot.sound'])]
        record.update(actual_axiom_sets=axioms,expected_axiom_sets=expected);save()
        need(axioms==expected, 'Unexpected exact axiom distribution; inspect actual reports.')
        need(obj.is_file() and not obj.is_symlink() and sha(obj)==fresh['sha256'], 'Fresh object changed during audit.')
        post()
        record.update(status='PASS',named_axiom_probes=2,callers=4,only_standard_axioms=True,
            all_fresh_objects_unchanged_after_audit=True,
            warnings=dict(source=source_log.count('warning:'),audit=audit_log.count('warning:')))
    except Exception as error:
        record.update(status='FAIL',error=str(error))
        try:
            post()
        except Exception as post_error:
            record['postcheck_error'] = str(post_error)
        save();raise
    save();print(work/'verification.json')

if __name__=='__main__':
    main()
