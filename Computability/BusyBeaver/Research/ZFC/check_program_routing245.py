#!/usr/bin/env python3
"""Bounded exact routing245 register-program decoder/source-tree identity check.

Reuses exactly RegisterPath, RMDag, RMEquiv and RMBisim selected from the
checked BinaryPrefix246 endpoint, plus Init. No dependency build, download,
version query or raised proof limits. Shared120 seconds, -j1 and -M4096.
--prepare-only produces provenance snapshots without invoking Lean.
The identified historical object caches are required, not rebuilt here.
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
MODULE = 'BusyBeaver.ZFC.ProgramRouting245'
PARENT_REL = 'Computability/BusyBeaver/Research/ZFC/results/prefix246-binary-verification.json'
PINS = {'source': '060a95566e6162b845b3ee734b4134aefeeb3e9c079de705c2d094ca9119ef0b', 'audit': 'be532c16bdd69352d54bab98bb734eb21f276808ae8399e90b010e1890f9b0fa', 'generator': '6f0826a4388120972accee6c721087521b40cbd14e3fcb82a1057e73fb2e29dc', 'inventory': '1eb5ed5b2a330c5e31eb1cce6e048cdcfff759c396c25dc4210faf42c7abb8a8', 'certificate': '3beba79cc5d1d7f9e3fae6d18c22115b6ef73c29d5d3e69ba17a460fd4065db3', 'boundary': '9ff81e17d1d17e81035d7d743621d5204d4bc7ae5dbef8b46051beb96628d424', 'plain_input': 'f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745', 'original_program': '6e564bd1ba179b2d39fccc3b8c86a681ec0dd6529df9cfa2522500eef140cfde', 'parent': '6f23d1ff40845704cc58fbd59e98388b1c2e5b9b42aeb519ef03e62796cdf6f2', 'compiler': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550', 'init': 'd2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'}
SHORT_PROBES = ['ProgramRouting245.program_root', 'ProgramRouting245.program_nnodes', 'ProgramRouting245.nodes_default', 'TreeRouting245.tree_eq_fuel', 'TreeRouting245.tree_eq', 'TreeRouting245.walk_eq_tree', 'TreeRouting245.step_eq_tree', 'TreeRouting245.leaf_count', 'TreeRouting245.node_count', 'TreeRouting245.depth_eq', 'TreeRouting245.halt_count']
PROBES = ['SetTheory.BusyBeaver.ZFC.'+n for n in SHORT_PROBES]
PROJECTS = ['BusyBeaver.ZFC.RegisterPath','BusyBeaver.ZFC.RMDag','BusyBeaver.ZFC.RMEquiv','BusyBeaver.ZFC.RMBisim']

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def need(condition,message):
    if not condition:
        raise RuntimeError(message)

def imports(path):
    return [name for line in re.findall(r'^import\s+([^\n]+)$',path.read_text(),re.M) for name in line.split()]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=REPO)
    ap.add_argument('--source',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProgramRouting245.lean')
    ap.add_argument('--audit',type=Path,default=HERE/'program_routing245_audit.lean')
    ap.add_argument('--generator',type=Path,default=HERE/'program-routing245/provenance/prepare_source.py')
    ap.add_argument('--inventory',type=Path,default=HERE/'program-routing245/source-inventory.json')
    ap.add_argument('--certificate',type=Path,default=HERE/'program-routing245/program-data.json')
    ap.add_argument('--boundary',type=Path,default=HERE/'program-routing245/dependency-boundary-plan.json')
    ap.add_argument('--plain-input',type=Path)
    ap.add_argument('--original-program',type=Path)
    ap.add_argument('--parent',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prepare-only',action='store_true')
    a=ap.parse_args();repo,work=a.repo.resolve(),a.output.resolve()
    need(not work.is_relative_to(repo) and (not work.exists() or not any(work.iterdir())),
         'Use new/empty external output.')
    files=dict(source=a.source.resolve(),audit=a.audit.resolve(),generator=a.generator.resolve(),
        inventory=a.inventory.resolve(),certificate=a.certificate.resolve(),boundary=a.boundary.resolve(),
        plain_input=(a.plain_input or repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/68-route245-certificate-sites_logical.json').resolve(),
        original_program=(a.original_program or repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Prog254.lean').resolve(),
        parent=(a.parent or repo/PARENT_REL).resolve())
    for key,path in files.items():
        need(path.is_file() and sha(path)==PINS[key], 'Changed '+key)
    source,audit=files['source'],files['audit']
    boundary=json.loads(files['boundary'].read_text());prior=json.loads(files['parent'].read_text())
    need(prior['status']=='PASS' and prior['prepare_only'] is False and
         prior['named_axiom_probes']==9 and prior['callers']==9 and prior['only_standard_axioms'] is True and
         prior['all_input_provider_postchecks'] is True and prior['all_fresh_objects_unchanged_after_audit'] is True and
         prior['source_object_recorded_before_audit'] is True and prior['before']==prior['after'],
         'Selected Binary246 parent must be a complete actual PASS.')
    need([row['label'] for row in prior['commands']]==['source','audit'] and
         all(row['exit_code']==0 and not row.get('timed_out',False) for row in prior['commands']),
         'Parent ordered commands are not successful.')
    need(prior['source_pass_object']==prior['fresh_modules'][0], 'Parent pre-audit binding changed.')
    need(boundary['parent_record']['sha256']==PINS['parent'] and boundary['project_count']==4 and
         boundary['selected_import_closure']==PROJECTS and boundary['source_direct_import']==PROJECTS[-1] and
         boundary['direct_external_libraries']==[], 'Frozen boundary plan changed.')
    candidates={row['module']:row for row in prior['reused_modules']}
    need(len(candidates)==len(prior['reused_modules']), 'Duplicate parent project providers.')
    actual={row['module']:row for row in prior['actual_first_providers']}
    need(len(actual)==len(prior['actual_first_providers']), 'Duplicate parent first providers.')
    chosen=boundary['selected_projects'];need([row['module'] for row in chosen]==PROJECTS,'Selected modules differ.')
    selected=[]
    for row in chosen:
        name=row['module'];p=candidates[name];first=actual[name]
        for key in ('source_sha256','object_sha256'):
            need(p[key]==row[key], 'Parent identity differs: '+name+'/'+key)
        for key in ('source','object'):
            path=Path(p[key]).resolve()
            need(path==Path(row[key]).resolve() and path.is_file() and sha(path)==row[key+'_sha256'],
                 'Current selected provider changed: '+name+'/'+key)
            need(prior['before'][p[key]]==prior['after'][p[key]]==row[key+'_sha256'],
                 'Parent before/after mismatch: '+name+'/'+key)
            files[name+'.'+key]=path
        need(first==row['actual_parent_provider'] and first['sha256']==row['object_sha256'] and
             Path(first['actual_first']).resolve()==Path(first['resolved']).resolve()==Path(row['object']).resolve(),
             'Parent actual first provider differs: '+name)
        selected.append({key:p[key] for key in ('module','source','source_sha256','object','object_sha256')})
    files['compiler']=Path(prior['compiler']['path']).resolve()
    files['init']=files['compiler'].parent.parent/'lib/lean/Init.olean'
    need(prior['compiler']['sha256']==boundary['compiler']['sha256']==PINS['compiler'] and
         sha(files['compiler'])==PINS['compiler'], 'Compiler changed.')
    init_rows=[row for row in prior['toolchain_providers'] if row['module']=='Init']
    need(len(init_rows)==1 and len(boundary['toolchain_boundaries'])==1 and
         init_rows[0]==boundary['toolchain_boundaries'][0] and
         init_rows[0]['object_sha256']==PINS['init'] and sha(files['init'])==PINS['init'] and
         Path(init_rows[0]['object']).resolve()==files['init'], 'Selected Init boundary changed.')
    for key,path in files.items():
        need(not path.is_relative_to(work), 'Input is inside output: '+key)
    # Independently follow the imports; never inherit the larger Binary246 closure.
    by_name={row['module']:row for row in selected};seen=set();external=set();closure=[]
    def walk(name):
        if name in seen:return
        seen.add(name)
        if name not in by_name:
            external.add(name);return
        for child in imports(Path(by_name[name]['source'])):walk(child)
        closure.append(name)
    walk(PROJECTS[-1])
    need(closure==PROJECTS and external=={'Init'} and imports(source)==[PROJECTS[-1]] and
         imports(audit)==[MODULE], 'Exact four-project/Init import boundary changed.')
    st,at=source.read_text(),audit.read_text()
    need(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',st), 'Forbidden source shortcut.')
    need(not re.search(r'\b(sorry|admit|native_decide)\b',at), 'Forbidden audit shortcut.')
    need(re.findall(r'^set_option ([^\n]+)$',st+at,re.M)==['autoImplicit false'], 'Keep default proof limits.')
    need(re.findall(r'^#print axioms (.+)$',at,re.M)==SHORT_PROBES and
         len(re.findall(r'^example\b',at,re.M))==13 and
         re.findall(r'^theorem (\w+)',st,re.M)==[n.split('.')[-1] for n in SHORT_PROBES],
         'Exact11-probe/13-caller public contract changed.')
    need(re.findall(r'^private theorem row(\d+)_eq',st,re.M)==[f'{i:03}' for i in range(203)] and
         re.findall(r'^private theorem node(\d+)_eq',st,re.M)==[f'{i:03}' for i in range(203)],
         'Private203-row/203-node census differs.')
    inventory=json.loads(files['inventory'].read_text());cert=json.loads(files['certificate'].read_text())
    for key,target in (('source','source'),('audit','audit'),('generator','generator'),('plain_input','plain_input'),
                       ('original_program','original_program'),('parser_certificate','certificate')):
        need(inventory[key]['sha256']==PINS[target], 'Inventory binding differs: '+key)
    need(cert['root']==202 and cert['nnodes']==len(cert['rows'])==len(cert['heights'])==203 and
         cert['heights'][-1]==51 and len(cert['ordered_sites'])==6460 and
         cert['ordered_sites']==json.loads(files['plain_input'].read_text()) and
         cert['full_internal_node_count']==6459 and cert['full_leaf_count']==6460 and
         cert['changed_paths_against_Prog254']==6241, 'Pinned parser certificate census differs.')
    work.mkdir(parents=True,exist_ok=True)
    cache=work/'cache';actual=[]
    for row in selected:
        dest=cache/Path(row['module'].replace('.','/')).with_suffix('.olean')
        dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(row['object']).resolve())
        actual.append(dict(module=row['module'],actual_first=str(dest),resolved=str(dest.resolve()),sha256=sha(dest)))
    snap=work/'sources'/Path(MODULE.replace('.','/')).with_suffix('.lean')
    snap.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,snap)
    aud=work/'Audit.lean';shutil.copyfile(audit,aud)
    inputs=list(dict.fromkeys([Path(__file__).resolve(),*files.values()]));before={str(p):sha(p) for p in inputs}
    record=dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING',prepare_only=a.prepare_only,
        scope='Exact203-node routing245 register decoder, arbitrary sufficient fuel, complete consumed-pointer leaf semantics; no original-program halting equivalence, binary simulation or consistency endpoint.',
        source=dict(path=str(source),sha256=sha(source),snapshot=str(snap)),
        audit=dict(path=str(audit),sha256=sha(audit),snapshot=str(aud)),
        compiler=dict(prior['compiler'],path=str(files['compiler'])),compiler_version_query_performed=False,
        parent_evidence=[dict(path=str(files['parent']),sha256=sha(files['parent']))],
        selected_boundary=dict(path=str(files['boundary']),sha256=sha(files['boundary'])),
        reused_modules=selected,actual_first_providers=actual,toolchain_providers=[dict(init_rows[0])],
        exact_project_import_closure=True,project_module_count=4,external_project_boundaries=['Init'],
        external_boundary_count=1,actual_direct_tool_imports=['Init'],
        LEAN_PATH=str(cache),before=before,commands=[],fresh_modules=[],dependency_build=False,downloads=False,
        limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),
        expected_named_axiom_probes=11,expected_callers=13,private_row_lemma_count=203,private_node_lemma_count=203,
        allowed_axioms=['propext','Classical.choice','Quot.sound'],
        axiom_policy='Record actual named distributions and gate only standard axioms; no empty-set assumption.')
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
        record.update(status='PASS',named_axiom_probes=11,callers=13,only_standard_axioms=True,
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
