#!/usr/bin/env python3
"""Serial exact certificate block checks, each with one report and two callers.

Requires a separately frozen complete Data PASS, then reuses its exact nine
project providers plus Init. Each block source/audit shares120 seconds,
-j1 -M4096, default proof limits. Prepare-only performs
no compiler/version/build call. Each unit proves only its selected block with full-certificate successor
lookup. Even all95 PASS records need the separate final assembly theorem;
this guard makes no source-halting equivalence, binary or PA claim.
Historical exact object caches must already exist.
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

HERE=Path(__file__).resolve().parent
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
DATA_MODULE='BusyBeaver.ZFC.BisimRouting245Data'
PINS={'generator': 'c96215e31c69e67d80e8488dce8c1f41ac9aa7dd53327d8734aa2cb067553d73', 'boundary': '656013953bceb83a01d470c2a7cf9f87438ea194daa6c12c3683f9a9c64a1b71', 'manifest': '58b9ab9a9d3c46be42cf2ef7fe1f1c19d70300a69bedebcb7d3c762c78b79d8c', 'certificate': '228eb4833868bd8e48b8c35a1bc5af96db2fba742c583df4b8fde8e2daf68c1f', 'compiler': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550', 'init': 'd2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e', 'pilot_parent': '4598ab1e2160d49e8774e0f71cf883b4766198342cdb088c6f6e27b630fa174f', 'parent': None}
BASE_PROJECTS=['BusyBeaver.ZFC.RegisterPath', 'BusyBeaver.ZFC.RMDag', 'BusyBeaver.ZFC.RMEquiv', 'BusyBeaver.ZFC.RMBisim', 'BusyBeaver.ZFC.Prog254', 'BusyBeaver.ZFC.ActualTree254', 'BusyBeaver.ZFC.ProgramRouting245', 'BusyBeaver.ZFC.BisimRouting245Pilot']
PROJECTS=BASE_PROJECTS+[DATA_MODULE]

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def need(condition,message):
    if not condition:raise RuntimeError(message)
def imports(path):return [name for line in re.findall(r'^import\s+([^\n]+)$',path.read_text(),re.M) for name in line.split()]

def run_unit(args, unit, work):
    module=unit['module'];index=int(unit['key'][5:]);lo,hi=32*index,min(32*index+32,3013)
    names=['checked'];probes=['SetTheory.BusyBeaver.ZFC.'+module.rsplit('.',1)[1]+'.checked']
    need(unit['key']==f'chunk{index:03}' and 0<=index<95 and module=='BusyBeaver.ZFC.BisimRouting245Chunk'+f'{index:03}' and
         unit['interval']==[lo,hi] and unit['direct_imports']==[DATA_MODULE] and
         unit['named_probes']==1 and unit['typed_callers']==2 and unit['prerequisites']==['data'], 'Malformed unit descriptor.')
    repo=args.repo.resolve()
    need(not work.is_relative_to(repo) and not work.exists(), 'Use a new external unit output.')
    files={key:Path(unit[key]['path']).resolve() for key in ('source','audit','inventory')}
    files.update({key:getattr(args,key).resolve() for key in ('generator','boundary','manifest','parent')})
    files['certificate']=(args.certificate or repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/68-route245-certificate-register_bisimulation.json').resolve()
    expected=dict(PINS,**{key:unit[key]['sha256']for key in ('source','audit','inventory')})
    for key,path in files.items():need(path.is_file() and sha(path)==expected[key], 'Changed '+key)
    source,audit=files['source'],files['audit']
    boundary=json.loads(files['boundary'].read_text());prior=json.loads(files['parent'].read_text())
    need(prior['status']=='PASS' and prior['prepare_only'] is False and
         (prior['named_axiom_probes'],prior['callers'])==(4,5) and prior['only_standard_axioms'] is True and
         prior['all_input_provider_postchecks'] is True and prior['all_fresh_objects_unchanged_after_audit'] is True and
         prior['source_object_recorded_before_audit'] is True and prior['before']==prior['after'], 'Incomplete Data parent.')
    need([row['label'] for row in prior['commands']]==['source','audit'] and
         all(row['exit_code']==0 and not row.get('timed_out',False) for row in prior['commands']), 'Parent command failure.')
    saved=dict(prior['source_pass_object']);saved.pop('source_command_index',None)
    need(len(prior['fresh_modules'])==1 and saved==prior['fresh_modules'][0] and saved['module']==DATA_MODULE,
         'Parent fresh Data source-pass binding.')
    need(boundary['parent']['sha256']==PINS['pilot_parent'] and boundary['project_count']==8 and
         [row['module'] for row in boundary['selected_projects']]==BASE_PROJECTS and
         prior['parent_evidence'][0]['sha256']==PINS['pilot_parent'], 'Frozen Pilot ancestry differs.')
    candidates={row['module']:row for row in prior['reused_modules']}
    actual_parent={row['module']:row for row in prior['actual_first_providers']}
    need(len(candidates)==len(prior['reused_modules'])==8 and len(actual_parent)==8 and
         set(candidates)==set(actual_parent)==set(BASE_PROJECTS), 'Parent eight-provider closure differs.')
    for row in boundary['selected_projects']:
        provider=candidates[row['module']]
        need(all(provider[key]==row[key]for key in ('source','source_sha256','object','object_sha256')), 'Ancestor identity differs.')
    snapshot=Path(prior['source']['snapshot']).resolve()
    need(sha(snapshot)==saved['source_sha256']==prior['source']['sha256'], 'Data source snapshot changed.')
    files['data_source_snapshot']=snapshot
    selected=[]
    for name in PROJECTS:
        is_fresh=name==DATA_MODULE
        if is_fresh:
            provider=dict(module=name,source=prior['source']['path'],source_sha256=prior['source']['sha256'],
                          object=saved['path'],object_sha256=saved['sha256'])
            first=prior['fresh_first_provider_before_audit']
        else:
            provider=candidates[name];first=actual_parent[name]
        for key in ('source','object'):
            path=Path(provider[key]).resolve()
            need(path.is_file() and sha(path)==provider[key+'_sha256'], 'Current provider changed '+name+'/'+key)
            if not (is_fresh and key=='object'):
                need(prior['before'][provider[key]]==prior['after'][provider[key]]==provider[key+'_sha256'], 'Parent input binding '+name+'/'+key)
            files[name+'.'+key]=path
        need(first['module']==name and first['sha256']==provider['object_sha256'] and
             Path(first['actual_first']).resolve()==Path(first['resolved']).resolve()==Path(provider['object']).resolve(),
             'Selected actual first provider '+name)
        selected.append(provider)
    files['compiler']=Path(prior['compiler']['path']).resolve();files['init']=files['compiler'].parent.parent/'lib/lean/Init.olean'
    need(prior['compiler']['sha256']==boundary['compiler']['sha256']==PINS['compiler'] and sha(files['compiler'])==PINS['compiler'], 'Compiler changed.')
    need(prior['toolchain_providers']==boundary['toolchain_providers'] and len(boundary['toolchain_providers'])==1,
         'Exact Init boundary differs.')
    tool=boundary['toolchain_providers'][0]
    need(tool['module']=='Init' and tool['object_sha256']==PINS['init'] and
         Path(tool['object']).resolve()==files['init'] and sha(files['init'])==PINS['init'], 'Init changed.')
    for key,path in files.items():need(not path.is_relative_to(work), 'Input lies in output '+key)
    by_name={row['module']:row for row in selected};seen=set();external=set();closure=[]
    def visit(name):
        if name in seen:return
        seen.add(name)
        if name not in by_name:external.add(name);return
        for child in imports(Path(by_name[name]['source'])):visit(child)
        closure.append(name)
    direct=[DATA_MODULE]
    for name in direct:visit(name)
    need(sorted(closure)==sorted(PROJECTS) and external=={'Init'} and
         imports(source)==direct and imports(audit)==[module], 'Exact nine-project/Init closure differs.')
    st,at=source.read_text(),audit.read_text()
    need(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',st) and
         not re.search(r'\b(sorry|admit|native_decide)\b',at), 'Forbidden proof shortcut.')
    need(re.findall(r'^set_option ([^\n]+)$',st+at,re.M)==['autoImplicit false'], 'Keep default proof limits.')
    need(re.findall(r'^theorem (\w+)',st,re.M)==names and
         re.findall(r'^#print axioms (.+)$',at,re.M)==[module.rsplit('.',1)[1]+'.checked'] and
         len(re.findall(r'^example\b',at,re.M))==2, 'Exact one-probe/two-caller contract changed.')
    inventory=json.loads(files['inventory'].read_text());manifest=json.loads(files['manifest'].read_text())
    units=[row for row in manifest['units']if row['key']=='data'];need(len(units)==1,'Missing/duplicate Data unit.')
    data=units[0]
    need(data['source']['sha256']==prior['source']['sha256'] and data['audit']['sha256']==prior['audit']['sha256'], 'Data manifest/parent differs.')
    for key in ('source','audit','generator'):need(inventory[key]['sha256']==expected[key], 'Inventory binding '+key)
    need(inventory['plain_certificate']['sha256']==PINS['certificate'] and
         inventory['pilot_source']['sha256']==boundary['selected_projects'][-1]['source_sha256'] and
         inventory['stage']=='chunk' and inventory['module']==module and
         inventory['full_certificate_pairs']==3013 and inventory['block_count']==95 and
         inventory['block_index']==index and inventory['block_range']==[lo,hi] and
         inventory['named_probes']==1 and inventory['typed_callers']==2 and
         inventory['source_direct_imports']==direct and inventory['full_certificate_for_successor_lookup'] is True,
         'Chunk inventory scope differs.')
    need(manifest['generator']['sha256']==PINS['generator'] and manifest['pilot_record']['sha256']==PINS['pilot_parent'] and
         manifest['certificate']['sha256']==PINS['certificate'] and manifest['full_certificate_pairs']==3013 and
         manifest['future_chunk_count']==95, 'Manifest bindings/scope differ.')
    work.mkdir(parents=True,exist_ok=True);cache=work/'cache';actual=[]
    for row in selected:
        dest=cache/Path(row['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        dest.symlink_to(Path(row['object']).resolve());actual.append(dict(module=row['module'],actual_first=str(dest),resolved=str(dest.resolve()),sha256=sha(dest)))
    snap=work/'sources'/Path(module.replace('.','/')).with_suffix('.lean');snap.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,snap);aud=work/'Audit.lean';shutil.copyfile(audit,aud)
    inputs=list(dict.fromkeys([Path(__file__).resolve(),*files.values()]));before={str(p):sha(p) for p in inputs}
    record=dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING',prepare_only=args.prepare_only,
        scope=f'Exact full-certificate entry checks for indices[{lo},{hi}) only; complete source-halting equivalence still requires all95 blocks and final assembly. No binary or PA endpoint.',
        source=dict(path=str(source),sha256=sha(source),snapshot=str(snap)),audit=dict(path=str(audit),sha256=sha(audit),snapshot=str(aud)),
        compiler=dict(prior['compiler'],path=str(files['compiler'])),compiler_version_query_performed=False,
        parent_evidence=[dict(path=str(files[k]),sha256=sha(files[k])) for k in ('parent',)],
        selected_boundary=dict(path=str(files['boundary']),sha256=sha(files['boundary'])),
        reused_modules=selected,actual_first_providers=actual,toolchain_providers=boundary['toolchain_providers'],
        exact_project_import_closure=True,project_module_count=9,external_project_boundaries=['Init'],external_boundary_count=1,
        actual_direct_tool_imports=['Init'],LEAN_PATH=str(cache),before=before,commands=[],fresh_modules=[],
        dependency_build=False,downloads=False,
        limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),
        expected_named_axiom_probes=1,expected_callers=2,full_certificate_pairs=3013,structural_block_count=95,block_index=index,block_interval=[lo,hi],
        allowed_axioms=['propext','Classical.choice','Quot.sound'],axiom_policy='Record actual named distribution; standard axioms only.')
    def save():
        (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    def post():
        record['after'] = {str(p):sha(p) for p in inputs}
        need(record['after']==before, 'Input/provider changed.')
        need(sha(snap)==expected['source'] and sha(aud)==expected['audit'], 'Source/audit snapshot changed.')
        for row in selected:
            dest = cache/Path(row['module'].replace('.','/')).with_suffix('.olean')
            need(dest.is_symlink() and dest.resolve()==Path(row['object']) and sha(dest)==row['object_sha256'],
                 'Actual first provider changed: '+row['module'])
        need(not (cache/'Init.olean').exists(), 'Implicit Init shadowed.')
        record['all_input_provider_postchecks'] = True
    save()
    try:
        if args.prepare_only:
            post();save();return record
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
        obj = cache/Path(module.replace('.','/')).with_suffix('.olean')
        source_log = run('source',[str(compiler),'-j1','-M4096','--root='+str(work/'sources'),'-o',str(obj),str(snap)])
        need(obj.is_file() and not obj.is_symlink(), 'Fresh source object missing.')
        fresh = dict(module=module,path=str(obj),sha256=sha(obj),source_sha256=sha(snap))
        record['fresh_modules'] = [fresh]
        record['source_pass_object'] = dict(fresh,source_command_index=0)
        record['source_object_recorded_before_audit'] = True
        record['fresh_first_provider_before_audit'] = dict(module=module,actual_first=str(obj),
            resolved=str(obj.resolve()),sha256=sha(obj))
        save()
        audit_log = run('audit',[str(compiler),'-j1','-M4096',str(aud)])
        reports = re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",audit_log,re.S)
        need([name for name,_ in reports]==probes, 'Missing/reordered axiom reports.')
        axioms = [dict(name=name,axioms=[x.strip() for x in block.split(',') if x.strip()]) for name,block in reports]
        record['actual_axiom_sets']=axioms;save()
        need(all(set(row['axioms'])<=set(record['allowed_axioms']) for row in axioms),
             'Unexpected axiom; inspect actual named reports.')
        need(obj.is_file() and not obj.is_symlink() and sha(obj)==fresh['sha256'], 'Fresh object changed during audit.')
        post()
        record.update(status='PASS',named_axiom_probes=1,callers=2,only_standard_axioms=True,
            all_fresh_objects_unchanged_after_audit=True,
            warnings=dict(source=source_log.count('warning:'),audit=audit_log.count('warning:')))
    except Exception as error:
        record.update(status='FAIL',error=str(error))
        try:
            post()
        except Exception as post_error:
            record['postcheck_error'] = str(post_error)
        save();raise
    save();return record

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=REPO)
    ap.add_argument('--generator',type=Path,default=HERE/'generate_production.py')
    ap.add_argument('--boundary',type=Path,default=HERE/'data-boundary.json')
    ap.add_argument('--manifest',type=Path,default=HERE/'units-v1.json')
    ap.add_argument('--certificate',type=Path)
    ap.add_argument('--parent',type=Path,default=HERE/'data-run1/verification.json')
    ap.add_argument('--start',type=int,default=0)
    ap.add_argument('--count',type=int,default=1)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prepare-only',action='store_true')
    args=ap.parse_args()
    need(isinstance(PINS['parent'],str) and re.fullmatch(r'[0-9a-f]{64}',PINS['parent']),
         'Blocked: separately freeze an actual complete Data PASS before any chunk preparation/run.')
    need(0<=args.start<95 and 1<=args.count<=95-args.start,'Choose a nonempty interval within95 blocks.')
    work=args.output.resolve();repo=args.repo.resolve()
    need(not work.is_relative_to(repo) and (not work.exists() or not any(work.iterdir())), 'Use new/empty external batch output.')
    manifest=args.manifest.resolve();need(sha(manifest)==PINS['manifest'],'Changed manifest.')
    payload=json.loads(manifest.read_text());need(payload['schema']=='routing245-source-bisim-units-v1','Manifest schema differs.')
    units={unit['key']:unit for unit in payload['units']}
    need(len(units)==len(payload['units']),'Duplicate manifest unit keys.')
    keys=[f'chunk{index:03}'for index in range(args.start,args.start+args.count)]
    need(all(key in units for key in keys),'Selected units have not been emitted into the frozen manifest.')
    work.mkdir(parents=True,exist_ok=True)
    batch=dict(status='RUNNING',prepare_only=args.prepare_only,guard=dict(path=str(Path(__file__).resolve()),sha256=sha(Path(__file__))),
        manifest=dict(path=str(manifest),sha256=sha(manifest)),parent=dict(path=str(args.parent.resolve()),sha256=PINS['parent']),
        selected_units=keys,completed_units=[],failed_unit=None,shared_wall_seconds_per_unit=120,serial=True,
        compiler_version_query_performed=False,dependency_build=False,downloads=False,
        scope='Independent selected block checks only. No final assembly or binary/PA endpoint.')
    def save_batch():(work/'batch.json').write_text(json.dumps(batch,indent=2)+'\n')
    save_batch()
    try:
        for key in keys:
            result=run_unit(args,units[key],work/key)
            need(result['status']==('PREPARED_NOT_BUILT'if args.prepare_only else 'PASS'),'Incomplete unit is not accepted.')
            record=work/key/'verification.json'
            batch['completed_units'].append(dict(key=key,status=result['status'],path=str(record),sha256=sha(record)))
            save_batch()
        batch['status']='PREPARED_NOT_BUILT'if args.prepare_only else 'PASS'
    except Exception as error:
        batch.update(status='FAIL',failed_unit=key,error=str(error));save_batch();raise
    save_batch();print(work/'batch.json')

if __name__=='__main__':
    main()
