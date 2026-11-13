#!/usr/bin/env python3
"""DRAFT sequential 338-module endpoint successor and 69-binding pair.

This launcher must not be launched until the source snapshot and this exact
launcher have received independent prelaunch review. Sampled stops are not hard quotas.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
if not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
ROOT=BASE.parents[1]
PLAN=BASE/'research/thirteen-model-endpoint-closure'
SNAP=Path('/tmp/ipra-thirteen-endpoint-source-01')
HIST=Path('/tmp/ipra-aq29-fresh-project-pair')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOLCHAIN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
MONITOR=BASE/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py'
AUDIT=BASE/'reviews/thirteen-model-endpoint-closure-independent-audit'
NODES=BASE/'research/thirteen69-dag-binding/Thirteen69Nodes.lean'
CUTS=BASE/'research/thirteen69-dag-binding/Thirteen69Cuts.lean'
BINDING=PLAN/'Model69EndpointBindingDraft.lean'
CHECKS=HERE/'Model69EndpointChecks.lean'
PINS={PLAN/'frontier-plan.json':'73d0ff4eff130c0bf74ae7ba170e591f1b62b2d43dd0fcaf654964a4ba3e2b9e',
      PLAN/'source-manifest.json':'de858182dbaab901257fe1ab0f9ede3a0a8e15f39f2b9c8b1d794f28814fc3bb',
      AUDIT/'CHECK.json':'ab2255186de1e61028731a47a1c92e89792835efe7317e4560b86861bc002af7',AUDIT/'audit.py':'30ccbcaa1050d3c9e6b9e4b73e930928fd93cba2380bba3ecdb629de755e587c',
      AUDIT/'terminal-observation.json':'ed0c3e7b515f2f0e642f278ac67f44f2eae7cc035e4991b51c96756dc3762dda',
      SNAP/'manifest.json':'5be9ded1c401d511b8be4d34d3bcc7c71fc04929f9b43502bb92281827032778',
      HIST/'pair-state.json':'04832cc18c11ad9da49d2cfc0c865baed07a18ace44d1de9d8319b150890e7dd',
      HIST/'author/state.json':'b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153',
      HIST/'peer/state.json':'67ecbd3f7b0a7c632c732dc75f87275dc4e59aa32c4d0aa0f91ee1c2ef9727a1',
      NODES:'599ec909c6605024c41ad45287d8b944e488fbe82e1d1e0d559b4a5b4d38d02e',
      CUTS:'3e3258bda47ca0843eed32fdbfd69f9d1dc57b7def815d2d59a2fdbd07093d66',
      BINDING:'edc9b46ba7e82153bdf982ba9054ed6a4f421173ad8abf0e774c7c556d56919b',
      CHECKS:'fc35a01cad321515356d92e832c29b601208e8b69a6574ba7d20a35745461e8a',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
      MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'}
STATUS='PASS_INDEPENDENT_THIRTEEN_ENDPOINT_CLOSURE_AUDIT'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
EXTRA=[('DiophantineConsistency.Thirteen69Nodes',NODES,['DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ThirteenCarrier']),
       ('DiophantineConsistency.Thirteen69Cuts',CUTS,['DiophantineConsistency.Thirteen69Nodes']),
       ('Model69EndpointBindingDraft',BINDING,['DiophantineConsistency.ModelThirteenCarrier','DiophantineConsistency.Thirteen69Cuts']),
       ('Model69EndpointChecks',CHECKS,['Model69EndpointBindingDraft'])]
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def check_guards(guards):
    for key,expected in guards.items():
        p=Path(key)
        if expected is None:
            if os.path.lexists(p):raise ValueError(('unexpected companion',key))
        elif not p.is_file() or str(p.resolve())!=expected['realpath'] or H(p)!=expected['sha256']:
            raise ValueError(('guard drift',key))

def scan(stem):
    out={}
    for suffix in SUFFIXES:
        p=Path(str(stem)+suffix)
        if os.path.lexists(p):
            if not p.is_file():raise ValueError(('invalid companion',str(p)))
            out[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
        else:out[str(p)]=None
    return out

def check_inputs():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    obs=json.loads((AUDIT/'terminal-observation.json').read_text());check=json.loads((AUDIT/'CHECK.json').read_text())
    if check.get('status')!=STATUS or obs.get('observed_exit')!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json']:
        raise ValueError('independent plan audit not observed')
    plan=json.loads((PLAN/'frontier-plan.json').read_text());snapshot=json.loads((SNAP/'manifest.json').read_text())
    if plan.get('status')!='CANDIDATE_FRONTIER_PLAN_NOT_A_BUILD' or snapshot.get('status')!='FROZEN_338_SOURCE_FRONTIER_NOT_COMPILED':raise ValueError('bad plan or snapshot status')
    if snapshot['frontier_plan_sha256']!=PINS[PLAN/'frontier-plan.json'] or snapshot['order']!=plan['rebuild_order'] or len(snapshot['order'])!=338 or len(plan['reusable_seeds'])!=807:raise ValueError('frontier binding')
    for n,row in snapshot['sources'].items():
        src=SNAP/row['snapshot_path'];expected=SNAP/'src'/Path(*n.split('.')).with_suffix('.lean')
        if src!=expected or not src.is_file() or src.is_symlink() or H(src)!=row['sha256']:raise ValueError(('snapshot source drift',n))
    for side in ('author','peer'):check_guards(plan['direct_and_seed_output_guards'][side])
    for row in plan['rebuild_external_guards'].values():check_guards(row['companions'])
    return plan,snapshot

def audit():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],cwd=ROOT,text=True,capture_output=True,timeout=600)
    if p.returncode or p.stderr:raise ValueError(('plan audit failed',p.returncode,p.stdout,p.stderr))
    d=json.loads(p.stdout)
    if d.get('status')!=STATUS:raise ValueError(('audit status',d))
    return d

def seed_overlay(plan,side,lib):
    state=json.loads((HIST/side/'state.json').read_text())
    for n in plan['reusable_seeds']:
        obj=HIST/side/'lib'/Path(*n.split('.')).with_suffix('.olean')
        outputs=state['outputs'][n]
        expected={str(obj)[:-6]+suffix for suffix in SUFFIXES}
        if set(outputs)!=expected:raise ValueError(('seed output coverage',side,n))
        for key,val in outputs.items():
            if key not in plan['direct_and_seed_output_guards'][side] or plan['direct_and_seed_output_guards'][side][key]!=val:
                raise ValueError(('seed output plan mismatch',side,key))
            if val is None:continue
            original=Path(key);dest=lib/original.relative_to(HIST/side/'lib');dest.parent.mkdir(parents=True,exist_ok=True)
            if os.path.lexists(dest):raise ValueError(('seed collision',str(dest)))
            dest.symlink_to(original)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--preflight-only',action='store_true');a=ap.parse_args()
    out=a.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-endpoint-successor-pair-'):raise ValueError('invalid output')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    driver=H(Path(__file__));plan,snapshot=check_inputs();before=audit()
    for root in (PACKAGE,TOOLCHAIN):
        for top in {n.split('.')[0] for n in plan['reusable_seeds']+plan['rebuild_order']}:
            for suffix in ('',*SUFFIXES,'.so','.dll','.dylib'):
                if os.path.lexists(root/(top+suffix)):raise ValueError(('project fallback present',str(root/(top+suffix))))
    free=shutil.disk_usage('/tmp').free
    if free<4*1024**3:raise ValueError(('sampled free space below reserve',free))
    if a.preflight_only:print('PREFLIGHT_SUCCESSOR_338_PLUS_4',free,flush=True);return
    spec=importlib.util.spec_from_file_location('endpoint_monitor',MONITOR);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
    out.mkdir();runs=[];all_guards={};produced=[]
    for side in ('author','peer'):
        run=out/side;run.mkdir();lib=run/'lib';seed_overlay(plan,side,lib);available=set(plan['reusable_seeds']);env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        work=[(n,SNAP/row['snapshot_path'],row['imports'],row['sha256']) for n in snapshot['order'] for row in [snapshot['sources'][n]]]
        work.extend((n,path,deps,PINS[path]) for n,path,deps in EXTRA)
        for name,source,imports,source_hash in work:
            if H(source)!=source_hash:raise ValueError(('source before compiler',name))
            # Extra source files live outside the frozen root. Compile exact
            # copies at module-appropriate paths inside each sibling root.
            if name in {x[0] for x in EXTRA}:
                copy=run/'extra-src'/Path(*name.split('.')).with_suffix('.lean');copy.parent.mkdir(parents=True,exist_ok=True)
                with copy.open('xb') as f:f.write(source.read_bytes())
                source=copy;source_root=run/'extra-src'
            else:source_root=SNAP/'src'
            deps=subprocess.run([str(LEAN),'--deps',str(source)],env=env,text=True,capture_output=True,timeout=120)
            if deps.returncode or deps.stderr:raise ValueError(('dependency query failed',side,name,deps.returncode,deps.stderr))
            expected={str(PACKAGE/'Init.olean')}
            for dep in imports:
                if dep in available:expected.add(str(lib/Path(*dep.split('.')).with_suffix('.olean')))
                elif dep in plan['rebuild_external_guards']:expected.add(plan['rebuild_external_guards'][dep]['path'])
                else:raise ValueError(('unavailable declared import',side,name,dep))
            if set(deps.stdout.splitlines())!=expected:raise ValueError(('dependency mismatch',side,name,deps.stdout,sorted(expected)))
            guards={}
            for item in expected:
                path=Path(item)
                if not path.is_file():raise ValueError(('dependency missing',item))
                guards.update(scan(Path(str(path)[:-6])))
            check_guards(guards)
            obj=lib/Path(*name.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
            if os.path.lexists(obj):raise ValueError(('object collision',name))
            log=run/(name.replace('.','_')+'.log')
            cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={source_root}',str(source),'-o',str(obj)]
            code,peak,reason=monitor.monitored(cmd,env,log,timeout=600);output=log.read_text()
            reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",output,re.M)
            row={'side':side,'module':name,'command':cmd,'source_sha256':H(source),'exit':code,'stop_reason':reason,'peak_sampled_rss_bytes':peak,
                 'log':str(log),'log_sha256':H(log),'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'axiom_reports':reports}
            runs.append(row);(out/'progress.json').write_text(json.dumps(runs,indent=2)+'\n')
            if code or reason or not obj.is_file() or obj.is_symlink() or re.search(r'(?m)^.*error:|\bsorryAx\b|\bsorry\b',output):raise ValueError(('compiler failure',side,name,code,reason,output[-12000:]))
            if any({x.strip() for x in report.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for _,report in reports):raise ValueError(('unexpected axioms',side,name,reports))
            if name=='Model69EndpointChecks' and len(reports)!=8:raise ValueError(('incomplete endpoint axiom inventory',side,reports))
            if H(source)!=source_hash:raise ValueError(('source after compiler',name))
            check_guards(guards)
            for key,value in guards.items():
                if key in all_guards and all_guards[key]!=value:raise ValueError(('direct companion drift',key))
                all_guards[key]=value
            row['object_sha256']=H(obj);produced.append((str(obj),H(obj)));available.add(name)
            (out/'progress.json').write_text(json.dumps(runs,indent=2)+'\n');print(side,len(available)-len(plan['reusable_seeds']),342,name,'exit',code,'sampled_peak_rss',peak,flush=True)
    for i in range(342):
        x,y=runs[i],runs[i+342]
        if (x['source_sha256'],x['object_sha256'],x['log_sha256'])!=(y['source_sha256'],y['object_sha256'],y['log_sha256']):raise ValueError(('sibling mismatch',x['module']))
    for p,h in produced:
        if H(p)!=h:raise ValueError(('produced object drift',p))
    check_guards(all_guards);check_inputs();after=audit()
    if H(Path(__file__))!=driver or before!=after:raise ValueError('driver or audit drift')
    receipt={'status':'PASS_PAIRED_THIRTEEN_ENDPOINT_SUCCESSOR','runs':runs,'driver_sha256':driver,'audit':after,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'direct_guards':all_guards,
      'scope':'Paired 338-project-module successor plus two rebuilt DAG modules, binding draft and endpoint axiom inventory. Sampled RSS/disk checks are not quotas; package-transitive/dynamic and Foundation outer-wrapper limitations remain. No claim beyond checked endpoint statements and binding is made.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_ENDPOINT_SUCCESSOR',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
