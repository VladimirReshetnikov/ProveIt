#!/usr/bin/env python3
"""Guarded fresh-base extension. Default --check never invokes Lean or writes outputs."""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

if not __debug__:
    raise SystemExit('refusing optimized Python')
sys.path.insert(0,str(Path(__file__).resolve().parent))
from guards import SUFFIXES, capture_input, capture_output, check_guard, digest, reject_project_fallbacks, scan
from owned import run as run_owned

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
TASK=ROOT/'Computability/DiophantineConsistency'
PLAN=TASK/'research/current14-printed-port-extension-plan'
BASE_PACKET=TASK/'research/current14-standard-fresh-rebuild-preflight'
BASE_DIR=Path('/tmp/current14-standard-fresh-build-20261104')
BASE_STATE=BASE_DIR/'state.json'
WATCHDOG=BASE_PACKET/'run-observation.json'
SNAP=Path('/tmp/current14-standard-fresh-source-20261104')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL=LEAN.resolve().parent.parent/'lib/lean'
OUT=Path('/tmp/current14-printed-port-extension-20261104')
PINS={
    SNAP/'manifest.json':'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',
    PLAN/'kernel-manifest.json':'4809f9cb3572bb0bdc47b22fd6a0c0e277c215d7aa322fd1847e8e63152fd6b2',
    PLAN/'masks-manifest.json':'7e6d83edfa707b63e1ad1f6070cad00d01859929dca4a9459063af5e0932a8ff',
    PLAN/'result.json':'cb1817489d0ea7ca5cb3f805acd857a7e22e68659fc664e03b8360d70f4f231c',
    PROVIDER:'7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6',
    LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
}
NEW_EXTERNAL_PINS={
    'Mathlib.Analysis.SpecialFunctions.Pow.Real':'a5d5ea7762c34422200b8549a96342c0b6a89b65e30f5daa8111a9c85026fab3',
    'Mathlib.NumberTheory.Wilson':'efc470ee0cac8b655fde9ba867e213688d1df6ba306a4096ed70b5118c0d9229',
    'Mathlib.Tactic':'55ee2345729e8a4d379de3bce14ea18b14fbfdc259cf2653fadf4bf3a46876d8',
}
MIN_FREE=4_000_000_000
MODULE_TIMEOUT=1800
def need(condition,message):
    if not condition:raise ValueError(message)
def read(path):return json.loads(Path(path).read_text())
def pinned():
    for path,expected in PINS.items():need(path.is_file() and digest(path)==expected,('pin mismatch',str(path)))
def guards_at(stems):
    out={}
    for stem in stems:
        for path,entry in scan(stem).items():
            if path in out and out[path]!=entry:raise ValueError(('guard conflict',path))
            out[path]=entry
    return out
def logical_name(path,root):
    rel=path.relative_to(root)
    need(str(rel).endswith('.olean'),('non-olean dependency',str(path)))
    return str(rel)[:-6].replace('/','.')
def base_gate():
    # Check terminal evidence before looking at or creating extension outputs.
    need(WATCHDOG.is_file() and BASE_STATE.is_file(),'base evidence missing')
    wd=read(WATCHDOG)
    need(wd.get('status')=='PASS' and wd.get('exit')==0 and wd.get('build_status')=='PASS',
         ('base watchdog has not completed successfully',wd.get('status'),wd.get('exit')))
    need(wd.get('build_source_status')=='CURRENT_AT_FINAL_CHECK' and wd.get('build_source_drift')==[],
         'base was not source-current at its final check')
    need(wd.get('snapshot_sha256')==PINS[SNAP/'manifest.json'] and wd.get('provider_sha256')==PINS[PROVIDER],
         'base watchdog pins differ')
    need(wd.get('runner_sha256')=='790a4b13f96f5cd544981aab6bdc7ae9e573a32f14195505551e191f0ee0a212' and
         wd.get('driver_sha256')=='8170bd401b1821666fffc2a55f8dd908e473d32c71797661a5acd85a32d0dc56',
         'base watchdog runner or driver differs')
    need(wd.get('build_state_sha256')==digest(BASE_STATE),'base state differs from watchdog')
    state=read(BASE_STATE)
    need(state.get('status')=='PASS' and state.get('source_status')=='CURRENT_AT_FINAL_CHECK' and state.get('workspace_source_drift')==[],
         'base state is not a source-current PASS')
    need(state.get('manifest_sha256')==PINS[SNAP/'manifest.json'] and state.get('provider_receipt_sha256')==PINS[PROVIDER],
         'base state pins differ')
    need(state.get('lean_sha256')==PINS[LEAN] and Path(state.get('package_overlay',''))==PKG,
         'base compiler or package overlay differs')
    need(state.get('driver_sha256')==wd['driver_sha256'],'base driver differs from watchdog')
    manifest=read(SNAP/'manifest.json')
    need(digest(ROOT/'lakefile.toml')==manifest['lakefile_sha256'] and
         digest(ROOT/'lean-toolchain')==manifest['lean_toolchain_sha256'],'base Lake configuration or toolchain file drift')
    names=manifest['order']; records=state.get('records',[]); outputs=state.get('outputs',{})
    need(len(names)==1000 and len(records)==1000 and set(outputs)==set(names), 'incomplete base rows')
    need([r.get('module') for r in records]==names and all(r.get('exit')==0 for r in records),'base row order or exit failure')
    need(manifest['target']=='DiophantineConsistency.IPRAStandardCurrentEndpointChecks' and names[-1]==manifest['target'],'wrong base target')
    for rec in records:
        name=rec['module'];row=manifest['sources'][name]
        src=SNAP/row['snapshot_path'];workspace=ROOT/row['workspace_path']
        need(src==SNAP/'src'/(name.replace('.','/')+'.lean') and
             all(not (SNAP/'src'/parent).is_symlink() for parent in src.relative_to(SNAP/'src').parents) and
             not (SNAP/'src').is_symlink() and src.is_file() and not src.is_symlink() and digest(src)==row['sha256'] and
             workspace.is_file() and digest(workspace)==row['sha256'] and rec['source_sha256']==row['sha256'],
             ('base source drift',name))
        obj=BASE_DIR/'lib'/(name.replace('.','/')+'.olean')
        stem=Path(str(obj)[:-6])
        need(set(outputs[name])=={str(stem)+suffix for suffix in SUFFIXES},('incomplete base output guards',name))
        expected=outputs[name].get(str(obj))
        need(isinstance(expected,dict) and obj.is_file() and not obj.is_symlink() and
             expected['sha256']==rec['object_sha256'] and digest(obj)==rec['object_sha256'],('base object mismatch',name))
        log=Path(rec['log']);need(log.is_file() and digest(log)==rec['log_sha256'],('base log mismatch',name))
        text=log.read_text()
        need(not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',text),('base rejected log',name))
        if name==manifest['target']:
            reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
            expected_names=['DiophantineConsistency.IPRAStandardTheory.leibniz',
                            'DiophantineConsistency.IPRAStandardTheory.provable_iff',
                            'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_consistency',
                            'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_translated_consistency']
            need([n for n,_ in reports]==expected_names and [r for _,r in reports]==rec['axiom_reports'],
                 'base endpoint axiom reports differ from log')
        declared=set(row['imports']);actual=set(rec['direct_inputs'])
        need(declared<=actual and not actual-declared-{'Init'},('base recorded import mismatch',name))
        for module,info in rec['direct_inputs'].items():
            kind=info['kind'];location=Path(info['path'])
            if module in manifest['sources']:
                need(kind=='project' and location==BASE_DIR/'lib'/(module.replace('.','/')+'.olean'),
                     ('wrong base project provider',name,module))
            else:
                allowed={'package':PKG,'toolchain':TOOL}
                need(kind in allowed and location==allowed[kind]/(module.replace('.','/')+'.olean'),
                     ('wrong base external provider',name,module))
            entry=state.get('guarded_companions',{}).get(info['path'])
            need(isinstance(entry,dict) and entry.get('sha256')==info['sha256'],('missing base direct input guard',name,module))
    reports=records[-1].get('axiom_reports',[])
    need(len(reports)==4 and all(not ({x.strip() for x in rep.split(',') if x.strip()}-
          {'propext','Classical.choice','Quot.sound'}) for rep in reports),'unexpected base endpoint axiom reports')
    need('guarded_companions' in state,'base input guards missing')
    check_guard(state['guarded_companions'])
    for guard in outputs.values():check_guard(guard)
    return wd,state,manifest
def provider_gate():
    pr=read(PROVIDER);need(pr.get('status')=='BUILT' and pr.get('exit_code')==0,'Foundation provider is not built')
    foundation=Path(pr['root'])/'.lake/build/lib/lean/Foundation'
    need((PKG/'Foundation').resolve(strict=True)==foundation.resolve(strict=True),'Foundation overlay changed')
    check_guard(pr['declared_external_guard'])
    for rel,expected in pr['foundation_artifacts'].items():
        path=foundation/rel
        need(path.is_file() and not path.is_symlink() and digest(path)==expected,('Foundation changed',rel))
    actual={str(p.relative_to(foundation)) for p in foundation.rglob('*') if p.is_file() or p.is_symlink()}
    need(actual==set(pr['foundation_artifacts']),'Foundation inventory changed')
    return pr
def source_plan(base):
    plan=read(PLAN/'result.json');k=read(PLAN/'kernel-manifest.json');m=read(PLAN/'masks-manifest.json')
    need(plan['status']=='SOURCE_PLAN_ONLY','wrong plan status')
    rows=dict(k['sources'])
    for name,row in m['sources'].items():
        if name in rows:need(rows[name]['sha256']==row['sha256'] and rows[name]['imports']==row['imports'],('extension snapshot conflict',name))
        rows[name]=row
    shared=set(rows)&set(base['sources']);order=plan['extra_project_build_order']
    need(len(rows)==84 and len(shared)==23 and len(order)==len(set(order))==61 and set(order)==set(rows)-shared,'extension counts differ')
    for name,row in rows.items():
        source=ROOT/row['workspace_path']
        need(source.is_file() and digest(source)==row['sha256'],('extension source drift',name))
        if name in shared:
            old=base['sources'][name]
            need(row['sha256']==old['sha256'] and row['imports']==old['imports'],('base/extension source conflict',name))
    seen=set(base['sources'])
    for name in order:
        need(all(d not in rows or d in seen for d in rows[name]['imports']),('extension order error',name))
        seen.add(name)
    external=sorted({d for name in order for d in rows[name]['imports'] if d not in seen}|{'Init'})
    new=sorted((set(k['external_modules'])|set(m['external_modules']))-set(base['external_modules']))
    need(new==plan['new_declared_external_modules']==['Mathlib.Analysis.SpecialFunctions.Pow.Real','Mathlib.NumberTheory.Wilson','Mathlib.Tactic'],
         'new external set differs')
    need(set(new)<=set(external),'new externals not required by extension')
    return rows,order,external,new
def preflight():
    pinned();wd,state,base=base_gate();pr=provider_gate();rows,order,external,new=source_plan(base)
    tops={n.split('.')[0] for n in set(base['sources'])|set(rows)}
    reject_project_fallbacks((PKG,TOOL),tops)
    stems=[root/(name.replace('.','/')) for name in external for root in (PKG,TOOL)]
    external_guard=guards_at(stems)
    need(set(new)==set(NEW_EXTERNAL_PINS),'new external pins differ')
    for name,expected in NEW_EXTERNAL_PINS.items():
        path=PKG/(name.replace('.','/')+'.olean')
        need(path.is_file() and digest(path)==expected,('new external object drift',name))
    for name in external:
        need(any((root/(name.replace('.','/')+'.olean')).is_file() for root in (PKG,TOOL)),('external object missing',name))
    free=shutil.disk_usage('/tmp').free;need(free>=MIN_FREE,'less than 4 GB free')
    pinned();need(digest(BASE_STATE)==wd['build_state_sha256'],'base state changed during preflight')
    check_guard(external_guard)
    return {'watchdog':wd,'base':state,'manifest':base,'provider':pr,'rows':rows,'order':order,
            'external':external,'new_external':new,'external_guard':external_guard,'tops':tops,'free':free}

def run_module(cmd,env,log,report):
    with log.open('x') as f:
        return run_owned(cmd,cwd=OUT/'src',env=env,stdout=f,stderr=subprocess.STDOUT,
                         timeout=MODULE_TIMEOUT,disk_check=lambda:shutil.disk_usage('/tmp').free>=MIN_FREE,
                         report=report)

def run_deps(src,env,logs,index,name,report):
    prefix=f'{index:03d}-'+name.replace('.','_')+'.deps'
    out=logs/(prefix+'.stdout');err=logs/(prefix+'.stderr')
    with out.open('x') as stdout, err.open('x') as stderr:
        code,seconds,receipt=run_owned([str(LEAN),'--deps',str(src)],cwd=ROOT,env=env,
            stdout=stdout,stderr=stderr,timeout=300,
            disk_check=lambda:shutil.disk_usage('/tmp').free>=MIN_FREE,report=report)
    return code,out.read_text(),err.read_text(),seconds,receipt,out,err

def execute(ctx):
    need(not OUT.exists(),'refusing existing extension output')
    processes=subprocess.run(['ps','-eo','pid=,stat=,comm='],check=True,text=True,stdout=subprocess.PIPE).stdout
    need(not any(len(x)==3 and x[2]=='lean' and not x[1].startswith('Z') for x in (line.split() for line in processes.splitlines())),
         'Lean slot is not free')
    OUT.mkdir();overlay=OUT/'lib';overlay.mkdir();sources=OUT/'src';sources.mkdir();logs=OUT/'logs';logs.mkdir()
    state={'status':'RUNNING','base_state_sha256':digest(BASE_STATE),'watchdog_sha256':digest(WATCHDOG),
           'driver_sha256':digest(__file__),'guards_sha256':digest(HERE/'guards.py'),
           'owned_sha256':digest(HERE/'owned.py'),
           'manifest_sha256':PINS[SNAP/'manifest.json'],'provider_sha256':PINS[PROVIDER],
           'records':[],'scope':'61-module extension of one authenticated base; external transitive, dynamic and between-check ancestry inherited.'}
    def save():
        tmp=OUT/'state.tmp';tmp.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');tmp.replace(OUT/'state.json')
    save()
    def report(message):
        state['owned_process_event']=message;save()
        print(message,flush=True)
    try:
        # Place all base companions in one project namespace by symlink, never
        # mutating the base or combining it with another project provider.
        base_overlay_guard={}
        for name,guard in ctx['base']['outputs'].items():
            for path,expected in guard.items():
                orig=Path(path);need(orig.is_relative_to(BASE_DIR/'lib'),('base path escaped',path))
                dst=overlay/orig.relative_to(BASE_DIR/'lib')
                base_overlay_guard[str(dst)]=expected
                if expected is None:continue
                dst.parent.mkdir(parents=True,exist_ok=True)
                need(not os.path.lexists(dst),('duplicate base output',str(dst)))
                dst.symlink_to(orig)
        check_guard(base_overlay_guard)
        external_tops={name.split('.')[0] for name in ctx['external']}
        need(not external_tops.intersection(ctx['tops']),'external/project namespace overlap')
        reject_project_fallbacks((overlay,),external_tops)
        overlay_external_guard=guards_at([overlay/(name.replace('.','/')) for name in ctx['external']])
        staged={}
        for name in ctx['order']:
            row=ctx['rows'][name];src=ROOT/row['workspace_path'];dest=sources/(name.replace('.','/')+'.lean')
            need(digest(src)==row['sha256'],('extension source before copy',name))
            dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes())
            need(digest(dest)==row['sha256'] and digest(src)==row['sha256'],('extension source copy drift',name))
            staged[name]=dest
        fresh={};env=dict(os.environ,LEAN_PATH=str(overlay)+':'+str(PKG),LEAN_NUM_THREADS='1')
        for var in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(var,None)
        all_project=set(ctx['manifest']['sources'])|set(ctx['rows'])
        for index,name in enumerate(ctx['order']):
            state.update(phase='compile',index=index,module=name);save()
            check_guard(overlay_external_guard);reject_project_fallbacks((overlay,),external_tops)
            row=ctx['rows'][name];src=staged[name]
            need(digest(src)==row['sha256'] and digest(ROOT/row['workspace_path'])==row['sha256'],('extension source drift',name))
            dep_code,dep_stdout,dep_stderr,dep_seconds,dep_receipt,dep_out,dep_err=run_deps(src,env,logs,index,name,report)
            need(dep_code==0 and not dep_stderr,('deps failed',name,dep_code,dep_stderr))
            direct={};inputs={}
            for line in dep_stdout.splitlines():
                path=Path(line);need(path.is_absolute() and path.is_file(),('unavailable import',name,line))
                if path.is_relative_to(overlay):
                    module=logical_name(path,overlay);kind='project'
                    need(module in all_project,('unknown project import',module))
                    need(module in ctx['manifest']['sources'] or module in fresh,('extension dependency not yet built',module))
                elif path.is_relative_to(PKG):module=logical_name(path,PKG);kind='package'
                elif path.is_relative_to(TOOL):module=logical_name(path,TOOL);kind='toolchain'
                else:raise ValueError(('import outside allowed roots',name,line))
                need(module not in direct,('duplicate import',module))
                if module.split('.')[0]=='Foundation':
                    need(kind=='package' and path.resolve().is_relative_to(Path(ctx['provider']['root'])/'.lake/build/lib/lean/Foundation'),
                         ('Foundation provider changed',module))
                direct[module]={'path':str(path),'kind':kind,'sha256':digest(path)}
                observed_guard=capture_input(path,direct[module]['sha256'])
                if kind=='project':
                    expected_guard=({key:base_overlay_guard[key] for key in observed_guard}
                                    if module in ctx['manifest']['sources'] else fresh[module])
                    need(observed_guard==expected_guard,('project import differs from authenticated producer',name,module))
                else:
                    expected_guard={key:ctx['external_guard'][key] for key in observed_guard}
                    need(observed_guard==expected_guard,('external import differs from preflight guard',name,module))
                inputs.update(observed_guard)
            declared=set(row['imports']);actual=set(direct)
            need(declared<=actual and not actual-declared-{'Init'},('declared/compiler import mismatch',name,sorted(declared-actual),sorted(actual-declared-{'Init'})))
            need({n for n,x in direct.items() if x['kind']=='project'}==declared&all_project,('project import mismatch',name))
            check_guard(inputs);check_guard(ctx['external_guard']);reject_project_fallbacks((PKG,TOOL),ctx['tops'])
            obj=overlay/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
            need(not os.path.lexists(obj),('output preexists',name))
            log=logs/(f'{index:03d}-'+name.replace('.','_')+'.log')
            cmd=[str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(sources),str(src),'-o',str(obj)]
            code,seconds,compile_receipt=run_module(cmd,env,log,report);text=log.read_text()
            need(dep_out.read_text()==dep_stdout and dep_err.read_text()==dep_stderr,('deps logs changed',name))
            rec={'module':name,'exit':code,'seconds':seconds,'source_sha256':digest(src),'direct_inputs':direct,
                 'log':str(log),'log_sha256':digest(log),'object_sha256':digest(obj) if obj.is_file() else None,
                 'deps_stdout':str(dep_out),'deps_stdout_sha256':digest(dep_out),
                 'deps_stderr':str(dep_err),'deps_stderr_sha256':digest(dep_err),
                 'deps_receipt':dep_receipt,'compile_receipt':compile_receipt}
            state['records'].append(rec);save()
            need(code==0 and obj.is_file() and not obj.is_symlink() and
                 not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',text),('Lean failed',name))
            need(digest(src)==row['sha256'] and digest(ROOT/row['workspace_path'])==row['sha256'],('extension source changed after',name))
            check_guard(inputs);check_guard(ctx['external_guard']);check_guard(overlay_external_guard)
            reject_project_fallbacks((overlay,),external_tops);fresh[name]=capture_output(obj,rec['object_sha256'])
            print('PASS',index+1,len(ctx['order']),name,flush=True)
        state.update(phase='final authentication',module=None);save()
        pinned();base_gate();provider_gate();check_guard(ctx['external_guard']);check_guard(overlay_external_guard);check_guard(base_overlay_guard)
        reject_project_fallbacks((overlay,),external_tops)
        for g in fresh.values():check_guard(g)
        for rec in state['records']:
            need(digest(rec['log'])==rec['log_sha256'] and
                 digest(rec['deps_stdout'])==rec['deps_stdout_sha256'] and
                 digest(rec['deps_stderr'])==rec['deps_stderr_sha256'],('extension log changed',rec['module']))
        for name in ctx['order']:
            row=ctx['rows'][name]
            need(digest(staged[name])==row['sha256'] and digest(ROOT/row['workspace_path'])==row['sha256'],('final extension source drift',name))
        need(digest(__file__)==state['driver_sha256'] and digest(HERE/'guards.py')==state['guards_sha256'] and
             digest(HERE/'owned.py')==state['owned_sha256'],
             'driver changed during extension')
        state.update(status='PASS',phase='complete',outputs=fresh,external_guards=ctx['external_guard'],
                     overlay_external_guards=overlay_external_guard,base_overlay_guards=base_overlay_guard);save()
        print('PASS 61 extension modules; assembly and endpoint join not included',flush=True)
    except BaseException as exc:
        state.update(status='FAILED',failure=repr(exc));save();raise

def main():
    parser=argparse.ArgumentParser();group=parser.add_mutually_exclusive_group()
    group.add_argument('--check',action='store_true',help='preflight only (default)')
    group.add_argument('--run',action='store_true',help='perform the guarded 61-module build')
    args=parser.parse_args()
    need(not OUT.exists(),'extension output path exists')
    ctx=preflight()
    print(json.dumps({'status':'PREFLIGHT_PASS','base_modules':len(ctx['manifest']['order']),
                      'extension_modules':len(ctx['order']),'new_external_modules':ctx['new_external'],
                      'external_companion_guards':len(ctx['external_guard']),'free_bytes':ctx['free'],
                      'scope':'Preflight only; no extension or assembly theorem.'},sort_keys=True),flush=True)
    if args.run:execute(ctx)
if __name__=='__main__':
    try:main()
    except Exception as exc:print('REFUSED_OR_FAILED',repr(exc),file=sys.stderr);raise SystemExit(1)
