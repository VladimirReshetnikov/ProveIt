#!/usr/bin/env python3
"""Resumable bounded single-side build over the sampled QM40 provider.

This is an incremental experiment, not a fresh transitive-closure audit.
Initialize a fresh /tmp child with --init, then run at most --limit stages
per invocation. Never cleans or overwrites a failed attempt or target object.
"""
import argparse
import fcntl
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import traceback

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lakefile.toml').is_file())
REPORT=HERE/'REPORT.json'
SCAN=HERE/'scan.py'
SEED=Path('/tmp/ipra-standard-qm40-author-run-02/lib')
PARENT=SEED.parent/'RESULT.json'
PARENT_PRE=SEED.parent/'preflight.json'
NATIVE=Path('/tmp/ipra-qm40-incremental-author-20261102-d')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL=LEAN.parent.parent/'lib/lean'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash',
          '.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
PINS={REPORT:'1ac359467b25ec85419a752aa3629e65cd13dc024b9eedf45e8fd5bf971925dc',
      SCAN:'d72f3242ff991ad537217b8b25c3cde4ab091a06ce45f61d4f92f70886848816',
      PARENT:'0d77e6da49ebad57c6808fa1f38aefedef7d790ae620f6cc6c61749be705339a',
      PARENT_PRE:'ad79d027343d5e1b5fda641b8c9aaaba288c63f49284b65b10a34e357ca17c9f',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
      NATIVE/'RESULT.json':'3b2ad576262725baf0ad31e68266c9be8d8014f51d4dd905b00e24f5419e5bd0',
      NATIVE/'preflight.json':'c64c712c72a3940b92797c8d62f972de48642b1a775c96507fd4ad5888d34cc8'}
AUDIT={'module':'DiophantineConsistency.IPRANineChecks',
       'source':'Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRANineChecks.lean',
       'source_sha256':'860903cd7bd24457f4f2800f7e6f77c1e2a0e8906ac7e572ac99d7ddd9ffdcaf',
       'imports':['DiophantineConsistency.IPRANineCurrent']}

def need(ok,msg):
    if not ok: raise RuntimeError(msg)
def digest(p): return sha256(Path(p).read_bytes()).hexdigest()
def record(p):
    p=Path(p)
    if not os.path.lexists(p): return None
    need(p.is_file(),('nonfile or dangling path',str(p)))
    return {'sha256':digest(p),'resolved':str(p.resolve(strict=True)),
            'link':os.readlink(p) if p.is_symlink() else None}
def check(records):
    for path,value in records.items(): need(record(path)==value,('guard changed',path))
def save(path,value):
    with Path(path).open('x') as f:
        json.dump(value,f,sort_keys=True,indent=2);f.write('\n')
def slots(stem): return {str(stem)+s:record(str(stem)+s) for s in SUFFIXES}
def path_of(root,module): return root/('/'.join(module.split('.')))
def disk():
    for p in (ROOT,Path('/tmp')):
        need(shutil.disk_usage(p).free >= 4*1024**3,('less than 4 GiB free',str(p)))
def check_pins():
    for path,pin in PINS.items(): need(digest(path)==pin,('pinned input drift',str(path)))
def check_parents():
    check_pins()
    for result,pre in ((PARENT,PARENT_PRE),(NATIVE/'RESULT.json',NATIVE/'preflight.json')):
        r=json.loads(result.read_text());p=json.loads(pre.read_text())
        check(r['guards']);check(p['fixed']);check(p['sources'])
def plan():
    r=json.loads(REPORT.read_text());xs=list(r['topological_build_order'])
    need(r['status']=='SOURCE_DECLARED_PREFLIGHT_NOT_A_BUILD' and len(xs)==103,'preflight plan')
    i=next(i for i,x in enumerate(xs) if x['module']=='DiophantineConsistency.IPRANineCurrent')
    need(i==79,'unexpected NineCurrent position')
    xs.insert(i+1,AUDIT)
    need(len({x['module'] for x in xs})==len(xs),'duplicate module')
    return xs
def check_sources(out,xs):
    for x in xs:
        mod=x['module'];want=x['source_sha256'];frozen=path_of(out/'src',mod).with_suffix('.lean')
        need(digest(ROOT/x['source'])==want and digest(frozen)==want,('source drift',mod))
def warning_policies(out,xs):
    directory=out/'warning-policies';items=list(directory.iterdir());policies={}
    for p in items:
        need(p.is_file() and not p.is_symlink() and re.fullmatch(r'\d{3}\.(json|log)',p.name),
             ('unsafe warning-policy entry',str(p)))
    indices={int(p.stem) for p in items}
    for index in indices:
        need(1<=index<=len(xs),('warning-policy index',index))
        meta=directory/f'{index:03d}.json';baseline=directory/f'{index:03d}.log'
        need(meta.is_file() and baseline.is_file(),('orphan warning policy',index))
        r=json.loads(meta.read_text());x=xs[index-1];text=baseline.read_text()
        evidence=Path(r['evidence_attempt']);evidence_source=Path(r['evidence_source'])
        raw=evidence/'compile.log';failure=evidence/'failure.json';obj=evidence/'object.olean'
        need(r['module']==x['module'] and r['source_sha256']==x['source_sha256'] and
             r['baseline_sha256']==digest(baseline) and r['warning_count']==text.count('warning:') and
             r['warning_count']>0 and not any(y in text for y in ('error:','sorryAx')) and
             digest(evidence_source)==r['source_sha256'] and digest(raw)==r['evidence_log_sha256'] and
             digest(failure)==r['evidence_failure_sha256'] and digest(obj)==r['evidence_object_sha256'] and
             raw.read_text().replace(str(evidence_source),'<SOURCE>')==text,
             ('warning baseline drift',index))
        policies[index]={'metadata':r,'text':text,'guards':{str(p):record(p) for p in
                            (meta,baseline,evidence_source,raw,failure,obj)}}
    return policies
def warning_matches(text,source,policy):
    if policy is None: return 'warning:' not in text
    return text.replace(str(source),'<SOURCE>')==policy['text']
def register_warning(out,xs,evidence):
    evidence=evidence.resolve(strict=True)
    need(evidence.is_dir() and evidence.parent.name=='attempts' and evidence.parent.parent.parent==Path('/tmp'),
         'warning evidence must be an attempt under a direct /tmp child')
    match=re.fullmatch(r'(\d{3})-\d{3}',evidence.name)
    need(match is not None,'invalid evidence attempt name')
    index=int(match.group(1));need(1<=index<=len(xs),'invalid evidence stage')
    x=xs[index-1];eout=evidence.parent.parent
    previous=json.loads((eout/'manifest.json').read_text())
    need(previous['report_sha256']==PINS[REPORT] and previous['modules']==xs,'evidence plan mismatch')
    source=path_of(eout/'src',x['module']).with_suffix('.lean')
    need(digest(source)==x['source_sha256'],'evidence source hash mismatch')
    f=json.loads((evidence/'failure.json').read_text());log=evidence/'compile.log';obj=evidence/'object.olean'
    expected=[str(LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(eout/'src'),
              str(source),'-o',str(obj)]
    need(f['stage']=='compile' and f['exit']==0 and f['object_present'] and f['command']==expected and
         f['log_sha256']==digest(log) and obj.is_file(),'not a warning-only successful compiler attempt')
    raw=log.read_text();text=raw.replace(str(source),'<SOURCE>')
    need(raw.count('warning:')>0 and not any(y in raw for y in ('error:','sorryAx')),
         'evidence contains no warning or contains an error/sorryAx')
    directory=out/'warning-policies';meta=directory/f'{index:03d}.json';baseline=directory/f'{index:03d}.log'
    need(not os.path.lexists(meta) and not os.path.lexists(baseline),'warning baseline already exists')
    with baseline.open('x') as stream: stream.write(text)
    save(meta,{'module':x['module'],'source_sha256':x['source_sha256'],'baseline_sha256':digest(baseline),
         'warning_count':raw.count('warning:'),'evidence_attempt':str(evidence),
         'evidence_log_sha256':digest(log),'evidence_failure_sha256':digest(evidence/'failure.json'),
         'evidence_object_sha256':digest(obj),
         'evidence_source':str(source),'scope':'explicit operator registration; full log after exact source-path normalization'})
    warning_policies(out,xs)
    print('REGISTERED_WARNING_BASELINE',index,x['module'],'warnings',raw.count('warning:'),flush=True)
def safe_dirs(root,relative):
    cur=root
    for part in relative.parts:
        cur=cur/part
        if os.path.lexists(cur): need(cur.is_dir() and not cur.is_symlink(),('unsafe directory',str(cur)))
        else: cur.mkdir()
def initialize(out,xs):
    disk();check_parents()
    need(not os.path.lexists(out),'output already exists')
    for x in xs:
        need(digest(ROOT/x['source'])==x['source_sha256'],('preflight source drift',x['module']))
        for root in (SEED,PKG,TOOL):
            need(all(v is None for v in slots(path_of(root,x['module'])).values()),
                 ('planned output exists in input root',x['module'],str(root)))
    out.mkdir(mode=0o700);(out/'lib').mkdir();(out/'src').mkdir();(out/'attempts').mkdir();(out/'receipts').mkdir();(out/'warning-policies').mkdir()
    c=subprocess.run(['/usr/bin/cp','-as',str(SEED)+'/.',str(out/'lib')+'/'],capture_output=True,text=True,timeout=120)
    need(c.returncode==0 and not c.stdout and not c.stderr,('seed overlay failed',c.stderr))
    for base,dirs,_ in os.walk(out/'lib',followlinks=False):
        for d in dirs: need(not (Path(base)/d).is_symlink(),('linked overlay directory',base,d))
    for x in xs:
        mod=x['module'];relative=Path('/'.join(mod.split('.'))+'.lean')
        safe_dirs(out/'src',relative.parent)
        dest=out/'src'/relative
        with (ROOT/x['source']).open('rb') as src,dest.open('xb') as dst: shutil.copyfileobj(src,dst)
        need(digest(dest)==x['source_sha256'],('snapshot failure',mod))
    save(out/'manifest.json',{'status':'INITIALIZED_NO_LEAN','report_sha256':PINS[REPORT],
         'runner_sha256':digest(__file__),'modules':xs,'seed':str(SEED),
         'scope':'incremental single-side build; inherited package/project/dynamic ancestry'})
    check_sources(out,xs);check_parents()
    print('INITIALIZED_NO_LEAN',len(xs),'stages',flush=True)
def run_process(cmd,env,log,timeout):
    with log.open('xb') as stream:
        proc=subprocess.Popen(cmd,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
        try: return proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid,signal.SIGTERM)
            try: proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid,signal.SIGKILL);proc.wait()
            return None
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--init',action='store_true');ap.add_argument('--check',action='store_true')
    ap.add_argument('--register-warning',type=Path)
    ap.add_argument('--limit',type=int,default=1)
    args=ap.parse_args();out=args.output
    need(out.is_absolute() and out.parent==Path('/tmp'),'output must be a direct /tmp child')
    need(1<=args.limit<=104,'limit must be 1..104')
    need(sum((args.init,args.check,args.register_warning is not None))<=1,
         'choose at most one of --init, --check and --register-warning');xs=plan()
    if args.init:
        initialize(out,xs);return
    need(out.is_dir() and not out.is_symlink(),'missing or unsafe initialized output')
    with (out/'.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        manifest=json.loads((out/'manifest.json').read_text())
        need(manifest['runner_sha256']==digest(__file__) and manifest['modules']==xs and
             manifest['report_sha256']==PINS[REPORT],'manifest or runner drift')
        check_sources(out,xs);check_parents();disk();warning_policies(out,xs)
        if args.register_warning is not None:
            register_warning(out,xs,args.register_warning)
            return
        receipts=[]
        for index,x in enumerate(xs,1):
            f=out/'receipts'/f'{index:03d}.json'
            target=path_of(out/'lib',x['module']).with_suffix('.olean')
            if not f.exists():
                need(not os.path.lexists(target),('unreceipted output; inspect manually',str(target)))
                need(not any((out/'receipts'/f'{j:03d}.json').exists() for j in range(index+1,len(xs)+1)),
                     'non-contiguous receipt ledger')
                break
            r=json.loads(f.read_text())
            need(r['status']=='PASS' and r['module']==x['module'] and r['source_sha256']==x['source_sha256'],
                 ('receipt mismatch',str(f)))
            need(record(target)==r['output'] and digest(r['log'])==r['log_sha256'],('completed output drift',x['module']))
            check(r['direct_guards']);check(r['warning_policy_guards']);receipts.append(r)
        else:
            print('ALL_STAGES_RECORDED',len(xs),flush=True);return
        if args.check:
            print('READY_NO_LEAN',len(receipts),'completed; next',xs[len(receipts)]['module'],flush=True)
            return
        for _ in range(args.limit):
            index=len(receipts)+1
            if index>len(xs): print('ALL_STAGES_RECORDED',len(xs),flush=True);return
            x=xs[index-1];module=x['module'];source=path_of(out/'src',module).with_suffix('.lean')
            disk();check_sources(out,xs);check_parents();policies=warning_policies(out,xs)
            policy=policies.get(index)
            for r in receipts: check(r['direct_guards']);check(r['warning_policy_guards'])
            target=path_of(out/'lib',module).with_suffix('.olean')
            safe_dirs(out/'lib',target.parent.relative_to(out/'lib'))
            need(all(v is None for v in slots(target.with_suffix('')).values()),('output slot occupied',module))
            seq=1
            while (out/'attempts'/f'{index:03d}-{seq:03d}').exists(): seq+=1
            attempt=out/'attempts'/f'{index:03d}-{seq:03d}';attempt.mkdir()
            env={'PATH':'/usr/bin:/bin','HOME':'/home/codex','LEAN_PATH':str(out/'lib')+':'+str(SEED)+':'+str(PKG),
                 'LEAN_NUM_THREADS':'1'}
            try:
                dep=subprocess.run([str(LEAN),'--deps',str(source)],env=env,capture_output=True,text=True,timeout=120)
            except subprocess.TimeoutExpired as ex:
                save(attempt/'failure.json',{'stage':'deps','timeout_seconds':120,
                     'stdout':(ex.stdout or b'').decode(errors='replace') if isinstance(ex.stdout,bytes) else ex.stdout,
                     'stderr':(ex.stderr or b'').decode(errors='replace') if isinstance(ex.stderr,bytes) else ex.stderr})
                raise RuntimeError(('dependency query timed out',module,str(attempt))) from ex
            (attempt/'deps.stdout').write_text(dep.stdout);(attempt/'deps.stderr').write_text(dep.stderr)
            if dep.returncode!=0 or dep.stderr:
                save(attempt/'failure.json',{'stage':'deps','exit':dep.returncode});raise RuntimeError(('deps failed',module))
            roots=(out/'lib',SEED,PKG,TOOL);guards={};direct={}
            for line in dep.stdout.splitlines():
                path=Path(line);owner=next((r for r in roots if path.is_relative_to(r)),None)
                need(owner is not None and path.is_file() and line.endswith('.olean'),('bad direct input',line))
                rel=path.relative_to(owner);name='.'.join(rel.with_suffix('').parts);candidates=[]
                for root in roots:
                    entries=slots((root/rel).with_suffix(''))
                    for p,v in entries.items():
                        need(p not in guards or guards[p]==v,('inconsistent guard',p));guards[p]=v
                    v=entries[str(root/rel)]
                    if v is not None: candidates.append((root/rel,v))
                need(candidates and candidates[0][0]==path and
                     all(v['sha256']==candidates[0][1]['sha256'] for _,v in candidates),('ambiguous input',module,name))
                direct[name]={'path':str(path),'record':record(path)}
            need(set(direct)==({'Init'}|set(x['imports'])),('declared/direct import mismatch',module,list(direct),x['imports']))
            check(guards);check_sources(out,xs);check_parents()
            if policy is not None: check(policy['guards'])
            obj=attempt/'object.olean';log=attempt/'compile.log'
            cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(out/'src'),str(source),'-o',str(obj)]
            code=run_process(cmd,env,log,600);text=log.read_text(errors='replace')
            warning_ok=warning_matches(text,source,policy)
            if code!=0 or not obj.is_file() or any(s in text for s in ('error:','sorryAx')) or not warning_ok:
                save(attempt/'failure.json',{'stage':'compile','exit':code,'command':cmd,
                     'log_sha256':digest(log),'object_present':obj.is_file()})
                raise RuntimeError(('compile failed or warning',module,code,str(attempt)))
            produced=slots(obj.with_suffix(''))
            need(produced[str(obj)] is not None and
                 all(v is None for path,v in produced.items() if path != str(obj)),
                 ('unexpected compiler output companions',module))
            reports=re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
                               text,re.M|re.S)
            if module=='DiophantineConsistency.IPRANineChecks':
                expected=set(re.findall(r'^#print axioms\s+(\S+)',source.read_text(),re.M))
                need(len(expected)==15 and len(reports)==15 and {name for name,_ in reports}==expected,
                     ('unexpected NineChecks reports',module))
            if module=='DiophantineConsistency.IPRAExplicitZFCFinal':
                expected={'DiophantineConsistency.IPRAExplicitZFCFinal.'+name for name in
                          ('sourceModel','native_equivalence','standard_equivalence','reference_equivalence')}
                need(len(reports)==4 and {name for name,_ in reports}==expected,
                     ('unexpected explicit endpoint reports',module))
            for report in re.findall(r"^'[^']+' depends on axioms:\s*\[([^]]*)\]",text,re.M|re.S):
                need({a.strip() for a in report.split(',')} <= {'propext','Classical.choice','Quot.sound'},
                     ('unexpected axioms',module,report))
            check(guards);check_sources(out,xs);check_parents()
            if policy is not None: check(policy['guards'])
            os.link(obj,target)  # atomic no-overwrite publication on the same /tmp filesystem
            r={'status':'PASS','module':module,'source_sha256':x['source_sha256'],'command':cmd,
               'direct':direct,'direct_guards':guards,'output':record(target),'log':str(log),'log_sha256':digest(log),
               'warning_policy':None if policy is None else policy['metadata'],
               'warning_policy_guards':{} if policy is None else policy['guards'],
               'scope':'single-side incremental build; inherited transitive/package/dynamic ancestry'}
            save(out/'receipts'/f'{index:03d}.json',r);receipts.append(r)
            print('PASS',index,'/',len(xs),module,flush=True)

if __name__=='__main__':
    try: main()
    except BaseException:
        traceback.print_exc();raise
