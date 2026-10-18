#!/usr/bin/env python3
"""Complete source-program bisimulation assembly, five reports/six callers.

Requires exact complete Data and all95 chunk PASS records. Reuses104 project
providers plus Init, with each current source/object and parent snapshot bound.
Final source/audit share120 seconds, -j1 -M4096 and default proof limits.
Prepare-only performs no compiler/version/build call. The conclusion concerns
arbitrary register files at empty source-program pointers, not a binary or PA
endpoint. Failed/partial chunks are never admitted as providers.
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
PINS={'generator': 'c96215e31c69e67d80e8488dce8c1f41ac9aa7dd53327d8734aa2cb067553d73', 'boundary': '656013953bceb83a01d470c2a7cf9f87438ea194daa6c12c3683f9a9c64a1b71', 'manifest': 'a7a408f6d0d865d48e11b73adb6c4f58fb71b1311cf0a60b8b2e567753a1bb87', 'certificate': '228eb4833868bd8e48b8c35a1bc5af96db2fba742c583df4b8fde8e2daf68c1f', 'compiler': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550', 'init': 'd2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e', 'pilot_parent': '4598ab1e2160d49e8774e0f71cf883b4766198342cdb088c6f6e27b630fa174f', 'parent': '64d0932251e46f3541cd5ccfa691452e199db7d8a4a66e9529ef96afc1bc9993', 'unit': 'cd1e2616b8fc4a30dce51ae1c29039aa3c0def16cd461fdffebed2b946b60fc8', 'parents': None}
BASE_PROJECTS=['BusyBeaver.ZFC.RegisterPath', 'BusyBeaver.ZFC.RMDag', 'BusyBeaver.ZFC.RMEquiv', 'BusyBeaver.ZFC.RMBisim', 'BusyBeaver.ZFC.Prog254', 'BusyBeaver.ZFC.ActualTree254', 'BusyBeaver.ZFC.ProgramRouting245', 'BusyBeaver.ZFC.BisimRouting245Pilot']
COMMON_PROJECTS=BASE_PROJECTS+[DATA_MODULE]
CHUNK_MODULES=[f'BusyBeaver.ZFC.BisimRouting245Chunk{index:03}'for index in range(95)]
PROJECTS=COMMON_PROJECTS+CHUNK_MODULES
MODULE='BusyBeaver.ZFC.BisimRouting245'
NAMES=['all_ok','initial_programs','all_ok_programs','program_halts_iff','program_nonhalting_iff']
PROBES=['SetTheory.BusyBeaver.ZFC.BisimRouting245.'+name for name in NAMES]

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def need(condition,message):
    if not condition:raise RuntimeError(message)
def imports(path):return [name for line in re.findall(r'^import\s+([^\n]+)$',path.read_text(),re.M) for name in line.split()]

def complete_parent(record, module, probes, callers):
    need(record['status']=='PASS' and record['prepare_only'] is False and
         (record['named_axiom_probes'],record['callers'])==(probes,callers) and record['only_standard_axioms'] is True and
         record['all_input_provider_postchecks'] is True and record['all_fresh_objects_unchanged_after_audit'] is True and
         record['source_object_recorded_before_audit'] is True and record['before']==record['after'], 'Incomplete parent '+module)
    need([row['label'] for row in record['commands']]==['source','audit'] and
         all(row['exit_code']==0 and not row.get('timed_out',False) for row in record['commands']), 'Parent command failure '+module)
    saved=dict(record['source_pass_object']);saved.pop('source_command_index',None)
    need(len(record['fresh_modules'])==1 and saved==record['fresh_modules'][0] and saved['module']==module and
         saved['source_sha256']==record['source']['sha256'], 'Parent fresh source-pass binding '+module)
    return saved

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=REPO)
    ap.add_argument('--generator',type=Path,default=HERE/'generate_production.py')
    ap.add_argument('--boundary',type=Path,default=HERE/'data-boundary.json')
    ap.add_argument('--manifest',type=Path,default=HERE/'units-v2.json')
    ap.add_argument('--unit',type=Path,default=HERE/'final-unit.json')
    ap.add_argument('--parents',type=Path,default=HERE/'final-parents.json')
    ap.add_argument('--certificate',type=Path)
    ap.add_argument('--parent',type=Path,default=HERE/'data-run1/verification.json')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prepare-only',action='store_true')
    args=ap.parse_args()
    need(isinstance(PINS['parents'],str) and re.fullmatch(r'[0-9a-f]{64}',PINS['parents']),
         'Blocked: freeze an exact index of all95 actual complete chunk PASS records first.')
    repo,work=args.repo.resolve(),args.output.resolve()
    need(not work.is_relative_to(repo) and (not work.exists() or not any(work.iterdir())), 'Use new/empty external output.')
    files={key:getattr(args,key).resolve() for key in ('generator','boundary','manifest','parent','unit','parents')}
    files['certificate']=(args.certificate or repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/68-route245-certificate-register_bisimulation.json').resolve()
    for key,path in files.items():need(path.is_file() and sha(path)==PINS[key], 'Changed '+key)
    unit=json.loads(files['unit'].read_text())
    files.update({key:Path(unit[key]['path']).resolve()for key in ('source','audit','inventory')})
    expected=dict(PINS,**{key:unit[key]['sha256']for key in ('source','audit','inventory')})
    for key in ('source','audit','inventory'):need(sha(files[key])==expected[key], 'Changed '+key)
    source,audit=files['source'],files['audit']
    boundary=json.loads(files['boundary'].read_text());prior=json.loads(files['parent'].read_text())
    saved=complete_parent(prior,DATA_MODULE,4,5)
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
    for name in COMMON_PROJECTS:
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
    manifest=json.loads(files['manifest'].read_text());units={row['key']:row for row in manifest['units']}
    need(manifest['schema']=='routing245-source-bisim-units-v1' and len(units)==len(manifest['units'])==96 and
         set(units)=={'data'}|{f'chunk{index:03}'for index in range(95)}, 'Complete frozen unit manifest differs.')
    need(manifest['generator']['sha256']==PINS['generator'] and manifest['pilot_record']['sha256']==PINS['pilot_parent'] and
         manifest['certificate']['sha256']==PINS['certificate'] and manifest['full_certificate_pairs']==3013 and
         manifest['future_chunk_count']==95 and manifest['remaining_chunks_emitted'] is True, 'Manifest identity/scope differs.')
    need(units['data']['source']['sha256']==prior['source']['sha256'] and
         units['data']['audit']['sha256']==prior['audit']['sha256'], 'Data parent/manifest differs.')
    index=json.loads(files['parents'].read_text())
    need(index['schema']=='routing245-bisim-final-parents-v1' and index['data']['sha256']==PINS['parent'] and
         index['manifest']['sha256']==PINS['manifest'] and
         [row['key']for row in index['chunks']]==[f'chunk{number:03}'for number in range(95)], 'Parent index is incomplete/reordered.')
    common_by_name={row['module']:row for row in selected};chunk_evidence=[]
    for number,entry in enumerate(index['chunks']):
        key=entry['key'];descriptor=units[key];name=CHUNK_MODULES[number]
        record_path=Path(entry['record']['path']).resolve()
        need(sha(record_path)==entry['record']['sha256'],'Chunk record changed '+key)
        record=json.loads(record_path.read_text());fresh=complete_parent(record,name,1,2)
        need(record['parent_evidence']==[dict(path=str(files['parent']),sha256=PINS['parent'])] and
             record['project_module_count']==9 and record['external_project_boundaries']==['Init'] and
             record['block_index']==number and record['block_interval']==[32*number,min(32*number+32,3013)], 'Chunk parent/interval differs '+key)
        need(record['source']['sha256']==descriptor['source']['sha256'] and
             record['audit']['sha256']==descriptor['audit']['sha256'] and descriptor['module']==name,
             'Chunk source/audit differs '+key)
        need(record['actual_axiom_sets'] and len(record['actual_axiom_sets'])==1 and
             record['actual_axiom_sets'][0]['name']=='SetTheory.BusyBeaver.ZFC.'+name.rsplit('.',1)[1]+'.checked' and
             set(record['actual_axiom_sets'][0]['axioms'])<={'propext','Classical.choice','Quot.sound'}, 'Chunk named audit differs '+key)
        reused={row['module']:row for row in record['reused_modules']}
        actual={row['module']:row for row in record['actual_first_providers']}
        need(len(reused)==len(record['reused_modules'])==9 and len(actual)==9 and
             set(reused)==set(actual)==set(COMMON_PROJECTS),'Chunk common-provider census differs '+key)
        for common_name,provider in common_by_name.items():
            row=reused[common_name];first=actual[common_name]
            need(all(row[field]==provider[field]for field in ('source','source_sha256','object','object_sha256')),
                 'Chunk common-provider identity differs '+key+'/'+common_name)
            for field in ('source','object'):
                need(record['before'][row[field]]==record['after'][row[field]]==row[field+'_sha256'], 'Chunk common input binding differs.')
            need(first['module']==common_name and first['sha256']==row['object_sha256'] and
                 Path(first['actual_first']).resolve()==Path(first['resolved']).resolve()==Path(row['object']).resolve(),
                 'Chunk common actual-first provider differs.')
        need(record['compiler']['sha256']==PINS['compiler'] and Path(record['compiler']['path']).resolve()==files['compiler'] and
             record['toolchain_providers']==boundary['toolchain_providers'], 'Chunk compiler/Init differs.')
        for role in ('source','audit'):
            path=Path(record[role]['path']).resolve();snapshot_path=Path(record[role]['snapshot']).resolve()
            need(path==Path(descriptor[role]['path']).resolve() and sha(path)==descriptor[role]['sha256'] and
                 sha(snapshot_path)==descriptor[role]['sha256'] and
                 record['before'][record[role]['path']]==record['after'][record[role]['path']]==descriptor[role]['sha256'],
                 'Chunk current source/audit/snapshot binding differs '+key+'/'+role)
            files[key+'.'+role]=path;files[key+'.'+role+'_snapshot']=snapshot_path
        provider=dict(module=name,source=record['source']['path'],source_sha256=record['source']['sha256'],
                      object=fresh['path'],object_sha256=fresh['sha256'])
        first=record['fresh_first_provider_before_audit'];obj=Path(provider['object']).resolve()
        need(obj.is_file() and not Path(provider['object']).is_symlink() and sha(obj)==provider['object_sha256'] and
             first['module']==name and first['sha256']==provider['object_sha256'] and
             Path(first['actual_first']).resolve()==Path(first['resolved']).resolve()==obj,'Chunk fresh provider changed '+key)
        files[key+'.record']=record_path;files[key+'.object']=obj;selected.append(provider)
        chunk_evidence.append(dict(key=key,path=str(record_path),sha256=sha(record_path)))
    need(len(selected)==104 and [row['module']for row in selected]==PROJECTS,'Exact104 provider census differs.')
    for key,path in files.items():need(not path.is_relative_to(work), 'Input lies in output '+key)
    by_name={row['module']:row for row in selected};seen=set();external=set();closure=[]
    def visit(name):
        if name in seen:return
        seen.add(name)
        if name not in by_name:external.add(name);return
        for child in imports(Path(by_name[name]['source'])):visit(child)
        closure.append(name)
    for name in CHUNK_MODULES:visit(name)
    need(sorted(closure)==sorted(PROJECTS) and external=={'Init'} and
         imports(source)==CHUNK_MODULES and imports(audit)==[MODULE], 'Exact104-project/Init closure differs.')
    st,at=source.read_text(),audit.read_text()
    need(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',st) and
         not re.search(r'\b(sorry|admit|native_decide)\b',at), 'Forbidden proof shortcut.')
    need(re.findall(r'^set_option ([^\n]+)$',st+at,re.M)==['autoImplicit false'], 'Keep default proof limits.')
    need(re.findall(r'^theorem (\w+)',st,re.M)==NAMES and
         re.findall(r'^#print axioms (.+)$',at,re.M)==['BisimRouting245.'+name for name in NAMES] and
         len(re.findall(r'^example\b',at,re.M))==6, 'Exact five-probe/six-caller contract changed.')
    inventory=json.loads(files['inventory'].read_text())
    for role in ('source','audit','generator'):need(inventory[role]['sha256']==expected[role], 'Final inventory binding '+role)
    need(unit['module']==MODULE and unit['manifest_v2']['sha256']==PINS['manifest'] and
         unit['generator']['sha256']==PINS['generator'] and unit['direct_imports']==CHUNK_MODULES and
         unit['named_probes']==5 and unit['typed_callers']==6 and unit['required_successful_chunk_units']==95 and
         unit['expected_imported_project_providers']==104, 'Final unit scope differs.')
    need(inventory['stage']=='final' and inventory['module']==MODULE and inventory['named_probes']==5 and
         inventory['typed_callers']==6 and inventory['source_direct_imports']==CHUNK_MODULES and
         inventory['plain_certificate']['sha256']==PINS['certificate'] and inventory['full_certificate_pairs']==3013 and
         inventory['block_count']==95, 'Final inventory scope differs.')
    work.mkdir(parents=True,exist_ok=True);cache=work/'cache';actual=[]
    for row in selected:
        dest=cache/Path(row['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        dest.symlink_to(Path(row['object']).resolve());actual.append(dict(module=row['module'],actual_first=str(dest),resolved=str(dest.resolve()),sha256=sha(dest)))
    snap=work/'sources'/Path(MODULE.replace('.','/')).with_suffix('.lean');snap.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,snap);aud=work/'Audit.lean';shutil.copyfile(audit,aud)
    inputs=list(dict.fromkeys([Path(__file__).resolve(),*files.values()]));before={str(p):sha(p) for p in inputs}
    record=dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING',prepare_only=args.prepare_only,
        scope='Complete source-program halting/nonhalting equivalence for arbitrary registers at empty pointers, assembling all95 exact blocks. No binary-machine or PA consistency endpoint.',
        source=dict(path=str(source),sha256=sha(source),snapshot=str(snap)),audit=dict(path=str(audit),sha256=sha(audit),snapshot=str(aud)),
        compiler=dict(prior['compiler'],path=str(files['compiler'])),compiler_version_query_performed=False,
        parent_evidence=[dict(path=str(files[k]),sha256=sha(files[k])) for k in ('parent',)],
        selected_boundary=dict(path=str(files['boundary']),sha256=sha(files['boundary'])),
        reused_modules=selected,actual_first_providers=actual,toolchain_providers=boundary['toolchain_providers'],
        exact_project_import_closure=True,project_module_count=104,external_project_boundaries=['Init'],external_boundary_count=1,
        actual_direct_tool_imports=['Init'],LEAN_PATH=str(cache),before=before,commands=[],fresh_modules=[],
        dependency_build=False,downloads=False,
        limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),
        expected_named_axiom_probes=5,expected_callers=6,full_certificate_pairs=3013,structural_block_count=95,chunk_parent_evidence=chunk_evidence,
        allowed_axioms=['propext','Classical.choice','Quot.sound'],axiom_policy='Record actual five named distributions; standard axioms only.')
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
        record['actual_axiom_sets']=axioms;save()
        need(all(set(row['axioms'])<=set(record['allowed_axioms']) for row in axioms),
             'Unexpected axiom; inspect actual named reports.')
        need(obj.is_file() and not obj.is_symlink() and sha(obj)==fresh['sha256'], 'Fresh object changed during audit.')
        post()
        record.update(status='PASS',named_axiom_probes=5,callers=6,only_standard_axioms=True,
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
