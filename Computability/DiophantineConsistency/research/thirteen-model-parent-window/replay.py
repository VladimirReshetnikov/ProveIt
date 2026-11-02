#!/usr/bin/env python3
"""Sequential source-current window/rank rebuild over the audited 20-source prefix pair."""
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

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('prefix rebuild rejects optimized Python')
if not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke the prefix rebuild with python3 -I -S')

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
ROOT=BASE.parents[1]
SNAP=Path('/tmp/ipra-thirteen-current-source-02')
PARENT=Path('/tmp/ipra-thirteen-parent-prefix-pair-01')
PARENTMAN=Path('/tmp/ipra-ordinary12-coexistence-source-03/manifest.json')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOLCHAIN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
MONITOR=BASE/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py'
FREEZEAUDIT=BASE/'reviews/thirteen-model-parent-current-freezer-independent-audit'
PARENTAUDIT=BASE/'reviews/thirteen-model-parent-prefix-pair-independent-audit'
FROZEN_HASH='2b6dc7e05664e925728bfde59e9da4c3d30242a006b1310b1681be53f3b87ef3'
ROOT_MODULES=('DiophantineConsistency.ArithmeticWindowZero','DiophantineConsistency.ArithmeticRankForcing2011')
PINS={SNAP/'manifest.json':FROZEN_HASH,
      PARENTMAN:'9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded',
      MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
      FREEZEAUDIT/'CHECK.json':'680ea4d3d6a1189d966329eb5415a64494e6ad1d394805e6f0a8b9bc601ad342',
      FREEZEAUDIT/'audit.py':'8bcf48d968b5bd925b0751863cdef6671bb5f54fb4c3fc0c53eae6f27e614d9d',
      FREEZEAUDIT/'terminal-observation.json':'8bde82e3817efc036514e426e9fa3a446cea7179c162c41e626f168e99258106',
      PARENT/'receipt.json':'4f31021934bd9b9d85d8d734d636fd17b35c953018f2bd13c42dc0236b0e4c42',
      PARENTAUDIT/'CHECK.json':'dcca147c2f1aea76821ae7089da6dc1ceb1096dbdbbb33429d7c50ce40a1945d',
      PARENTAUDIT/'audit.py':'c05d6ce8e72e3ca95c0683c9dbca42c99522165b5f0ae50e7af091a4938734fd',
      PARENTAUDIT/'terminal-observation.json':'4002b74efe53c32e805f294342353780af65d6c397132e07da17f187661834d3'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')


def scan(stem):
    result={}
    for suffix in SUFFIXES:
        p=Path(str(stem)+suffix)
        if os.path.lexists(p):
            if not p.is_file():raise ValueError(('invalid companion',str(p)))
            result[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
        else:result[str(p)]=None
    return result


def check_guard(guard):
    for path,expected in guard.items():
        p=Path(path)
        if expected is None:
            if os.path.lexists(p):raise ValueError(('unexpected companion',path))
        elif not p.is_file() or str(p.resolve())!=expected['realpath'] or H(p)!=expected['sha256']:
            raise ValueError(('input drift',path))


def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    check=json.loads((FREEZEAUDIT/'CHECK.json').read_text())
    obs=json.loads((FREEZEAUDIT/'terminal-observation.json').read_text())
    if check.get('status')!='PASS_INDEPENDENT_CORRECTED_SOURCE_FREEZER_AUDIT' or obs.get('audit_observed_exit_code')!=0 or obs.get('receipt_sha256')!=PINS[FREEZEAUDIT/'CHECK.json']:
        raise ValueError('missing independently observed freezer audit')
    pcheck=json.loads((PARENTAUDIT/'CHECK.json').read_text())
    pobs=json.loads((PARENTAUDIT/'terminal-observation.json').read_text())
    if pcheck.get('status')!='PASS_INDEPENDENT_20_MODULE_PREFIX_PAIR_AUDIT' or pobs.get('audit_observed_exit_code')!=0 or pobs.get('receipt_sha256')!=PINS[PARENTAUDIT/'CHECK.json']:
        raise ValueError('missing independently observed parent audit')
    m=json.loads((SNAP/'manifest.json').read_text());parent=json.loads(PARENTMAN.read_text())
    if m.get('status')!='FROZEN_44_SOURCE_EXTENSION_NOT_COMPILED' or len(m.get('order',[]))!=44 or len(m.get('sources',{}))!=44:
        raise ValueError('unexpected source snapshot')
    if m.get('parent_manifest_sha256')!=PINS[PARENTMAN] or len(parent.get('order',[]))!=70:
        raise ValueError('unexpected project parent')
    for name,row in m['sources'].items():
        src=SNAP/row['snapshot_path'];expected=SNAP/'src'/Path(*name.split('.')).with_suffix('.lean')
        if src!=expected or not src.is_file() or src.is_symlink() or H(src)!=row['sha256']:
            raise ValueError(('snapshot drift',name))
        if (SNAP/'src').is_symlink() or any((SNAP/'src'/p).is_symlink() for p in src.relative_to(SNAP/'src').parents):
            raise ValueError(('snapshot has symlinked parent',name))
    for name,row in m['external_direct'].items():
        if not row['sha256'] or H(row['path'])!=row['sha256']:
            raise ValueError(('external direct drift',name))
    prefix=json.loads((PARENT/'receipt.json').read_text())
    if prefix.get('status')!='PASS_PAIRED_2011_PARENT_PREFIX' or len(prefix.get('order',[]))!=20:
        raise ValueError('unexpected audited prefix')
    if set(parent['order']) & set(prefix['order']):raise ValueError('parent and prefix overlap')
    parent['available_order']=parent['order']+prefix['order']
    return m,parent


def verify_audits():
    records=[]
    for audit,status in ((FREEZEAUDIT,'PASS_INDEPENDENT_CORRECTED_SOURCE_FREEZER_AUDIT'),
                         (PARENTAUDIT,'PASS_INDEPENDENT_20_MODULE_PREFIX_PAIR_AUDIT')):
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],cwd=ROOT,text=True,capture_output=True,timeout=240)
        if p.returncode or p.stderr:raise ValueError(('audit failed',str(audit),p.returncode,p.stdout,p.stderr))
        data=json.loads(p.stdout)
        if data.get('status')!=status:raise ValueError(('unexpected audit status',str(audit),data))
        records.append(data)
    return records


def prefix_order(m,parent):
    sources=m['sources'];bases=set(parent['available_order']);selected=set();active=set()
    def visit(name):
        if name in bases:return
        if name not in sources:
            if name not in m['external_direct']:raise ValueError(('unresolved declared import',name))
            return
        if name in selected:return
        if name in active:raise ValueError(('cyclic module',name))
        active.add(name)
        for child in sources[name]['imports']:visit(child)
        active.remove(name);selected.add(name)
    for module in ROOT_MODULES:visit(module)
    order=[n for n in m['order'] if n in selected]
    if len(order)!=24 or any(module not in order for module in ROOT_MODULES):raise ValueError(('unexpected window closure',order))
    return order


def overlay(base,dest):
    for root,dirs,files in os.walk(base,followlinks=False):
        root=Path(root);out=dest/root.relative_to(base);out.mkdir(parents=True,exist_ok=True)
        for name in list(dirs):
            if (root/name).is_symlink():
                (out/name).symlink_to(root/name);dirs.remove(name)
        for name in files:(out/name).symlink_to(root/name)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--preflight-only',action='store_true');a=ap.parse_args()
    out=a.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-parent-window-'):
        raise ValueError('output must be a fresh direct /tmp/ipra-thirteen-parent-window-* path')
    if out.exists() or out.is_symlink():raise ValueError('output already exists')
    driver_hash=H(Path(__file__))
    m,parent=check_pins();order=prefix_order(m,parent);before=verify_audits()
    for root in (PACKAGE,TOOLCHAIN):
        for top in ('DiophantineConsistency','BusyBeaver','FirstOrder','PAHF'):
            for suffix in ('',*SUFFIXES,'.so','.dll','.dylib'):
                if os.path.lexists(root/(top+suffix)):raise ValueError(('project fallback present',str(root/(top+suffix))))
    free=shutil.disk_usage('/tmp').free
    if free<4*1024**3:raise ValueError(('sampled free space below reserve',free))
    if a.preflight_only:
        print('PREFLIGHT_PASS',len(order),'sampled_free_bytes',free,flush=True);return
    spec=importlib.util.spec_from_file_location('prefix_monitor',MONITOR);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
    out.mkdir();rows=[];parent_set=set(parent['available_order']);produced=[];global_guard={}
    for label in ('author','peer'):
        run=out/label;lib=run/'lib';run.mkdir()
        overlay(PARENT/label/'lib',lib)
        available=set(parent_set);env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        for name in order:
            row=m['sources'][name];source=SNAP/row['snapshot_path']
            if H(source)!=row['sha256']:raise ValueError(('source before compiler',name))
            deps=subprocess.run([str(LEAN),'--deps',str(source)],env=env,text=True,capture_output=True,timeout=120)
            if deps.returncode or deps.stderr:raise ValueError(('dependency query failed',label,name,deps.returncode,deps.stderr))
            expected={str(PACKAGE/'Init.olean')}
            for dep in row['imports']:
                if dep in available:expected.add(str(lib/Path(*dep.split('.')).with_suffix('.olean')))
                elif dep in m['external_direct']:expected.add(m['external_direct'][dep]['path'])
                else:raise ValueError(('unavailable declared import',label,name,dep))
            if set(deps.stdout.splitlines())!=expected:
                raise ValueError(('dependency mismatch',label,name,deps.stdout,sorted(expected)))
            guards={}
            for p in expected:
                path=Path(p)
                if not path.is_file():raise ValueError(('dependency missing',p))
                for key,value in scan(Path(str(path)[:-6])).items():
                    if key in global_guard and global_guard[key]!=value:raise ValueError(('companion drift',key))
                    global_guard[key]=value;guards[key]=value
            check_guard(guards)
            obj=lib/Path(*name.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
            if obj.exists() or obj.is_symlink():raise ValueError(('object already present',name))
            log=run/(name.replace('.','_')+'.log')
            cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={SNAP / "src"}',str(source),'-o',str(obj)]
            code,peak,reason=monitor.monitored(cmd,env,log,timeout=300)
            output=log.read_text()
            reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
            record={'label':label,'module':name,'command':cmd,'source_sha256':H(source),'exit':code,'stop_reason':reason,
                    'peak_sampled_rss_bytes':peak,'log':str(log),'log_sha256':H(log),'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'axiom_reports':reports}
            rows.append(record);(out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
            if code or reason or not obj.is_file() or obj.is_symlink() or re.search(r'(?m)^.*error:|\bsorryAx\b|\bsorry\b',output):
                raise ValueError(('compiler failure',label,name,code,reason,output[-12000:]))
            if any({x.strip() for x in r.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for r in reports):
                raise ValueError(('unexpected axiom report',label,name,reports))
            if H(source)!=row['sha256']:raise ValueError(('source after compiler',name))
            check_guard(guards)
            record['object_sha256']=H(obj);produced.append((str(obj),H(obj)));available.add(name)
            (out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
            print(label,len(available)-len(parent_set),len(order),name,'exit',code,'sampled_peak_rss',peak,flush=True)
    for i in range(len(order)):
        x,y=rows[i],rows[i+len(order)]
        if (x['source_sha256'],x['object_sha256'],x['log_sha256'])!=(y['source_sha256'],y['object_sha256'],y['log_sha256']):
            raise ValueError(('sibling output mismatch',x['module']))
    for p,h in produced:
        if H(p)!=h:raise ValueError(('produced object drift',p))
    check_guard(global_guard);check_pins();after=verify_audits()
    if H(Path(__file__))!=driver_hash:raise ValueError('prefix driver changed during run')
    if before!=after:raise ValueError('independent audit output changed')
    receipt={'status':'PASS_PAIRED_2011_PARENT_WINDOW','order':order,'runs':rows,'independent_audits':after,
             'source_manifest_sha256':FROZEN_HASH,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
             'driver_sha256':driver_hash,
             'guarded_companions':global_guard,
             'scope':'Paired 24-module source-current project suffix over the independently audited 20-module prefix and 70-source parent. Sampled RSS and free-space stops are not hard quotas or continuous reservations. No rank-phase theorem, actual-zero client, fixed-port calibration beyond inherited parent, iPRA proof, Foundation outer-wrapper exit, or package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_2011_PARENT_WINDOW',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
