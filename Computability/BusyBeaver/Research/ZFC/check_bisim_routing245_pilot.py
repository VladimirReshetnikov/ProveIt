#!/usr/bin/env python3
"""Bounded source-bisimulation pilot over the exact full3013-entry certificate.

Seven finite checks only: initial segment and six indexed entries. No allC,
halting-equivalence, binary-simulation or consistency claim. Reuse exact seven
project providers plus Init, no builds/downloads/version query. Source/audit
share120 seconds with -j1 -M4096 and default proof limits. Prepare-only runs
no compiler. Required historical object caches are not rebuilt here.
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
REPO=HERE.parents[3]
MODULE='BusyBeaver.ZFC.BisimRouting245Pilot'
PROGRAM_MODULE='BusyBeaver.ZFC.ProgramRouting245'
PINS={'source': 'b7b061dffcdaddf856eabbf6a2cc826e22431bbbc74d0d9e8704167bbe1801b1', 'audit': 'be0ddb7bd937fd303c5e3cdcd88e620bea9271bcd7adfef7732358d77f8cbf41', 'generator': 'ea4d3905c824d4b6efac23318905da92e0c8ebb64ac1dcd133a78b27cbb70a1b', 'inventory': 'f51878517375f301f59d7e32209201c954eae5218210be5cac2183921f4f9569', 'boundary': '55768fb8b83a52c9d229a2aef24abb3f4d94c05c3ede70ab1355a40bbcce629d', 'certificate': '228eb4833868bd8e48b8c35a1bc5af96db2fba742c583df4b8fde8e2daf68c1f', 'binary_parent': '6f23d1ff40845704cc58fbd59e98388b1c2e5b9b42aeb519ef03e62796cdf6f2', 'program_parent': '1efd9f64fc8067e85518fc9968752a9a10f78cdeb4f24aa8dd9e8c58d2a53c71', 'compiler': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550', 'init': 'd2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'}
PROJECTS=['BusyBeaver.ZFC.RegisterPath', 'BusyBeaver.ZFC.RMDag', 'BusyBeaver.ZFC.RMEquiv', 'BusyBeaver.ZFC.RMBisim', 'BusyBeaver.ZFC.Prog254', 'BusyBeaver.ZFC.ActualTree254', 'BusyBeaver.ZFC.ProgramRouting245']
NAMES=['initial_ok','entry0000_ok','entry0090_ok','entry0103_ok','entry0329_ok','entry0791_ok','entry3012_ok']
PROBES=['SetTheory.BusyBeaver.ZFC.BisimRouting245Pilot.'+n for n in NAMES]

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def need(c,m):
    if not c:raise RuntimeError(m)
def imports(path):return [x for line in re.findall(r'^import\s+([^\n]+)$',path.read_text(),re.M) for x in line.split()]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=REPO)
    ap.add_argument('--source',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BisimRouting245Pilot.lean')
    ap.add_argument('--audit',type=Path,default=HERE/'bisim_routing245_pilot_audit.lean')
    ap.add_argument('--generator',type=Path,default=HERE/'bisim-routing245-pilot/provenance/prepare_pilot.py')
    ap.add_argument('--inventory',type=Path,default=HERE/'bisim-routing245-pilot/source-inventory.json')
    ap.add_argument('--boundary',type=Path,default=HERE/'bisim-routing245-pilot/dependency-boundary-plan.json')
    ap.add_argument('--certificate',type=Path)
    ap.add_argument('--binary-parent',type=Path)
    ap.add_argument('--program-parent',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prepare-only',action='store_true')
    a=ap.parse_args();repo,work=a.repo.resolve(),a.output.resolve()
    need(not work.is_relative_to(repo) and (not work.exists() or not any(work.iterdir())), 'Use new/empty external output.')
    files=dict(source=a.source.resolve(),audit=a.audit.resolve(),generator=a.generator.resolve(),
        inventory=a.inventory.resolve(),boundary=a.boundary.resolve(),
        certificate=(a.certificate or repo/'Computability/BusyBeaver/Research/ZFC/bisim-routing245-pilot/register-bisimulation.json').resolve(),
        binary_parent=(a.binary_parent or repo/'Computability/BusyBeaver/Research/ZFC/results/prefix246-binary-verification.json').resolve(),
        program_parent=(a.program_parent or repo/'Computability/BusyBeaver/Research/ZFC/results/program-routing245-verification.json').resolve())
    for key,path in files.items():need(path.is_file() and sha(path)==PINS[key], 'Changed '+key)
    source,audit=files['source'],files['audit'];boundary=json.loads(files['boundary'].read_text())
    parents={key:json.loads(files[key].read_text()) for key in ('binary_parent','program_parent')}
    for key,prior in parents.items():
        expected=(9,9) if key=='binary_parent' else (11,13)
        need(prior['status']=='PASS' and prior['prepare_only'] is False and
             (prior['named_axiom_probes'],prior['callers'])==expected and prior['only_standard_axioms'] is True and
             prior['all_input_provider_postchecks'] is True and prior['all_fresh_objects_unchanged_after_audit'] is True and
             prior['source_object_recorded_before_audit'] is True and prior['before']==prior['after'], 'Incomplete parent '+key)
        need([r['label'] for r in prior['commands']]==['source','audit'] and
             all(r['exit_code']==0 and not r.get('timed_out',False) for r in prior['commands']), 'Parent command failure '+key)
        saved=dict(prior['source_pass_object']);saved.pop('source_command_index',None)
        need(len(prior['fresh_modules'])==1 and saved==prior['fresh_modules'][0], 'Parent source-pass binding '+key)
    need([p['sha256'] for p in boundary['parent_records']]==[PINS['binary_parent'],PINS['program_parent']] and
         boundary['project_count']==7 and [r['module'] for r in boundary['selected_projects']]==PROJECTS,
         'Frozen selected parent/provider boundary differs.')
    binary,program=parents['binary_parent'],parents['program_parent']
    candidates={r['module']:r for r in binary['reused_modules']};actual={r['module']:r for r in binary['actual_first_providers']}
    need(len(candidates)==len(binary['reused_modules']) and len(actual)==len(binary['actual_first_providers']), 'Duplicate binary providers.')
    common={r['module']:r for r in program['reused_modules']}
    need(set(common)==set(PROJECTS[:4]), 'Program shared-four closure changed.')
    for name,row in common.items():
        need(all(row[k]==candidates[name][k] for k in ('source_sha256','object_sha256')), 'Parents disagree on '+name)
    chosen=boundary['selected_projects'];selected=[]
    for row in chosen:
        name=row['module'];is_new=name==PROGRAM_MODULE
        prior=program if is_new else binary
        need(row['selected_parent_record']['sha256']==PINS['program_parent' if is_new else 'binary_parent'], 'Wrong selected parent '+name)
        if is_new:
            fresh=program['fresh_modules'][0]
            need(fresh['module']==name and fresh['source_sha256']==program['source']['sha256'], 'Wrong fresh program.')
            p=dict(module=name,source=program['source']['path'],source_sha256=program['source']['sha256'],
                   object=fresh['path'],object_sha256=fresh['sha256'])
            first=program['fresh_first_provider_before_audit']
            snapshot=Path(program['source']['snapshot'])
            need(sha(snapshot)==p['source_sha256'], 'Program source snapshot changed.')
            files['program_source_snapshot']=snapshot.resolve()
        else:p=candidates[name];first=actual[name]
        for key in ('source_sha256','object_sha256'):need(p[key]==row[key], 'Selected identity '+name+'/'+key)
        for key in ('source','object'):
            path=Path(p[key]).resolve()
            need(path==Path(row[key]).resolve() and path.is_file() and sha(path)==row[key+'_sha256'], 'Current provider changed '+name+'/'+key)
            if not (is_new and key=='object'):
                need(prior['before'][p[key]]==prior['after'][p[key]]==row[key+'_sha256'], 'Parent input binding '+name+'/'+key)
            files[name+'.'+key]=path
        need(first==row['actual_parent_provider'] and first['sha256']==row['object_sha256'] and
             Path(first['actual_first']).resolve()==Path(first['resolved']).resolve()==Path(row['object']).resolve(),
             'Selected actual first provider '+name)
        selected.append(p)
    files['compiler']=Path(binary['compiler']['path']).resolve();files['init']=files['compiler'].parent.parent/'lib/lean/Init.olean'
    need(binary['compiler']['sha256']==program['compiler']['sha256']==boundary['compiler']['sha256']==PINS['compiler'] and
         sha(files['compiler'])==PINS['compiler'], 'Compiler identity changed.')
    for prior in parents.values():
        tool=[r for r in prior['toolchain_providers'] if r['module']=='Init']
        need(len(tool)==1 and tool[0]['object_sha256']==PINS['init'] and
             Path(tool[0]['object']).resolve()==files['init'], 'Parent Init differs.')
    need(len(boundary['toolchain_providers'])==1 and boundary['toolchain_providers'][0]['module']=='Init' and
         boundary['toolchain_providers'][0]['object_sha256']==PINS['init'] and sha(files['init'])==PINS['init'], 'Init changed.')
    for key,path in files.items():need(not path.is_relative_to(work), 'Input lies in output '+key)
    by_name={r['module']:r for r in selected};seen=set();external=set();closure=[]
    def visit(name):
        if name in seen:return
        seen.add(name)
        if name not in by_name:external.add(name);return
        for child in imports(Path(by_name[name]['source'])):visit(child)
        closure.append(name)
    direct=['BusyBeaver.ZFC.ActualTree254',PROGRAM_MODULE]
    for name in direct:visit(name)
    need(sorted(closure)==sorted(PROJECTS)==boundary['exact_dfs_project_modules'] and external=={'Init'} and
         imports(source)==direct==boundary['source_direct_imports'] and imports(audit)==[MODULE], 'Exact seven-project/Init closure differs.')
    st,at=source.read_text(),audit.read_text()
    need(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',st) and
         not re.search(r'\b(sorry|admit|native_decide)\b',at), 'Forbidden proof shortcut.')
    need(re.findall(r'^set_option ([^\n]+)$',st+at,re.M)==['autoImplicit false'], 'Keep default proof limits.')
    need(re.findall(r'^theorem (\w+)',st,re.M)==NAMES and
         re.findall(r'^#print axioms (.+)$',at,re.M)==['BisimRouting245Pilot.'+n for n in NAMES] and
         len(re.findall(r'^example\b',at,re.M))==7, 'Exact7/7 pilot contract changed.')
    inventory=json.loads(files['inventory'].read_text());certificate=json.loads(files['certificate'].read_text())
    for k,target in [('source','source'),('audit','audit'),('emitter','generator'),('certificate','certificate')]:
        need(inventory[k]['sha256']==PINS[target], 'Inventory binding '+k)
    need(certificate['start_pair']==0 and len(certificate['entries'])==3013 and
         inventory['pilot_indices']==[0,90,103,329,791,3012] and inventory['lean_segment_fuel']==1000 and
         inventory['full_certificate_pairs']==3013 and inventory['full_successor_references']==6024,
         'Full certificate/pilot scope differs.')
    literals=[tuple(map(int,row)) for row in re.findall(r'\.leaf \((\d+), (\d+), (\d+), (\d+)\)',st)]
    expected=[]
    for i,(old_bits,new_bits,j,k) in enumerate(certificate['entries']):
        if j is None or k is None:
            need(i==90 and j is None and k is None,'Unexpected halt adaptation.');j=k=0
        expected.append((int('1'+old_bits,2),int('1'+new_bits,2),j,k))
    need(literals==expected and len(literals)==3013,'Exact full certificate entries differ.')
    work.mkdir(parents=True,exist_ok=True);cache=work/'cache';actual=[]
    for row in selected:
        dest=cache/Path(row['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        dest.symlink_to(Path(row['object']).resolve());actual.append(dict(module=row['module'],actual_first=str(dest),resolved=str(dest.resolve()),sha256=sha(dest)))
    snap=work/'sources'/Path(MODULE.replace('.','/')).with_suffix('.lean');snap.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,snap);aud=work/'Audit.lean';shutil.copyfile(audit,aud)
    inputs=list(dict.fromkeys([Path(__file__).resolve(),*files.values()]));before={str(p):sha(p) for p in inputs}
    record=dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING',prepare_only=a.prepare_only,
        scope='Full3013-entry data with initial segment and six indexed finite checks only; no allC, halting equivalence, binary or consistency endpoint.',
        source=dict(path=str(source),sha256=sha(source),snapshot=str(snap)),audit=dict(path=str(audit),sha256=sha(audit),snapshot=str(aud)),
        compiler=dict(binary['compiler'],path=str(files['compiler'])),compiler_version_query_performed=False,
        parent_evidence=[dict(path=str(files[k]),sha256=sha(files[k])) for k in ('binary_parent','program_parent')],
        selected_boundary=dict(path=str(files['boundary']),sha256=sha(files['boundary'])),
        reused_modules=selected,actual_first_providers=actual,toolchain_providers=boundary['toolchain_providers'],
        exact_project_import_closure=True,project_module_count=7,external_project_boundaries=['Init'],external_boundary_count=1,
        actual_direct_tool_imports=['Init'],LEAN_PATH=str(cache),before=before,commands=[],fresh_modules=[],
        dependency_build=False,downloads=False,
        limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),
        expected_named_axiom_probes=7,expected_callers=7,full_certificate_pairs=3013,pilot_indices=[0,90,103,329,791,3012],
        allowed_axioms=['propext','Classical.choice','Quot.sound'],axiom_policy='Record actual seven named distributions; standard axioms only.')
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
        record['actual_axiom_sets']=axioms;save()
        need(all(set(row['axioms'])<=set(record['allowed_axioms']) for row in axioms),
             'Unexpected axiom; inspect actual named reports.')
        need(obj.is_file() and not obj.is_symlink() and sha(obj)==fresh['sha256'], 'Fresh object changed during audit.')
        post()
        record.update(status='PASS',named_axiom_probes=7,callers=7,only_standard_axioms=True,
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
