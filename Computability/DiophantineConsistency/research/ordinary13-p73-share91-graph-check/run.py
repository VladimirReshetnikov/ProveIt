#!/usr/bin/env python3
"""Isolated P73 graph-only guard; no Lean without explicit --run."""
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
ROOT = P.parents[3]
D = ROOT/'Computability/DiophantineConsistency'
R = D/'research'
P72 = Path('/tmp/p72-current-base-extension-attempt02-20261105')
PKG = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent/'lib/lean'
OUT = Path('/tmp/ordinary13-p73-share91-graph-attempt01-20261111')
PLAN = P/'plan.json'
MON = R/'current14-auxiliary-order-generic-cast-check/monitor.py'
SURVEY = R/'ordinary13-p73-graph-route-survey/inspect.py'
PINS = {
    PLAN:'436298c31a3d851beaba2a1bbc2c0b7dd27a4a9c41af1871dbcfff696d8a3347',
    MON:'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0',
    SURVEY:'072edc61b17b6cd9344963db101004e2b2922bfbe34c13011d364c5b6b4983e2',
    R/'ordinary13-p73-graph-route-survey/observation.json':'5e3efc56c0659a60ba1c3a935c69050f1bb57fe02ad1a083fb92da2a54d3d333',
    D/'reviews/ordinary13-p73-graph-route-survey-independent/check.py':'c5798d854b2f0eeeee56875d83180afc0a3aa1d3f37a67669fe9c1d021bd25dc',
    D/'reviews/ordinary13-p73-graph-route-survey-independent/result.json':'ce16cb5b7e759fa4099874104ba00f70188084ac65a32f075c39ed5becef15af',
    D/'reviews/ordinary13-p73-share91-lean-draft-independent/check.py':'02ced5485086f6d236e4e1676cf40ea0a0a9e2706982587e6cd38c3aa5c46dc8',
    D/'reviews/ordinary13-p73-share91-lean-draft-independent/result.json':'401b7a09f0e1c5dbd33085267a80038e449c0fd82963c2453c09635909d034f6',
    LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
}
DISK_FLOOR = 5_100_000_000
MEM_FLOOR = 10*1024**3
RSS_LIMIT = 4*1024**3
CHILD_SECONDS = 180
TOTAL_SECONDS = 6*3600
INTERVAL = .2
SUFFIXES = ('.olean','.olean.private','.olean.server','.ir','.ilean',
            '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash',
            '.so','.dll','.dylib')
AXIOMS = {'propext','Classical.choice','Quot.sound'}
ACTIVE_WATCH = None

class Refusal(RuntimeError): pass
def need(value, message):
    if not value: raise Refusal(message)
def sha(path, watch_resources=True):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024), b''):
            if watch_resources and ACTIVE_WATCH is not None: ACTIVE_WATCH.check()
            h.update(block)
    return h.hexdigest()
def mem_available():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'): return int(line.split()[1])*1024
    raise Refusal('MemAvailable missing')
def decision(disk, mem, elapsed):
    if disk <= DISK_FLOOR: return 'disk_floor'
    if mem < MEM_FLOOR: return 'host_memory_floor'
    if elapsed >= TOTAL_SECONDS: return 'total_timeout'
    return None
def no_live_lean():
    for p in Path('/proc').iterdir():
        if not p.name.isdecimal(): continue
        try:
            if (p/'comm').read_text().strip() == 'lean' and (p/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X'):
                raise Refusal('another Lean process is active')
        except (FileNotFoundError,ProcessLookupError): continue
class Watch:
    def __init__(self,start):
        self.start=start; self.reason=None; self.done=threading.Event()
        self.thread=threading.Thread(target=self.loop,daemon=True)
    def loop(self):
        while not self.done.is_set():
            try: self.reason=decision(shutil.disk_usage('/tmp').free,mem_available(),time.monotonic()-self.start)
            except BaseException as e: self.reason='watchdog_error:'+repr(e)
            if self.reason: self.done.set(); return
            self.done.wait(INTERVAL)
    def begin(self): self.thread.start()
    def check(self):
        if self.reason: raise Refusal(self.reason)
        why=decision(shutil.disk_usage('/tmp').free,mem_available(),time.monotonic()-self.start)
        if why: raise Refusal(why)
    def stop(self): self.done.set(); self.thread.join(timeout=3)
def git_query(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT,timeout=30)
def source_imports(path):
    return [x for line in path.read_text().splitlines() if line.startswith('import ')
            for x in line.split('--',1)[0].split()[1:]]
def source_reports(path):
    return re.findall(r'^#print axioms\s+(\S+)',path.read_text(),re.M)
def validate_reports(text, reports):
    pairs=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
    free=re.findall(r"'([^']+)' does not depend on any axioms",text)
    names=[name for name,_ in pairs]+free
    need(len(names)==len(reports) and len(set(names))==len(names) and set(names)==set(reports),
         'unexpected/duplicate axiom report set')
    for name,body in pairs:
        found={x.strip() for x in body.split(',') if x.strip()}
        need(found <= AXIOMS,'unexpected axiom '+name+': '+str(found))
def inspect_guards(names):
    out={}
    for name in names:
        for root in (OUT/'lib',P72/'lib',PKG,TOOL):
            for suffix in SUFFIXES:
                if ACTIVE_WATCH is not None: ACTIVE_WATCH.check()
                p=root/(name.replace('.','/')+suffix)
                if os.path.lexists(p):
                    need(p.is_file(),'non-file dependency candidate '+str(p))
                    out[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
                else: out[str(p)]=None
    return out
def write_state(out,state):
    with (out/'state.tmp').open('w') as f:
        json.dump(state,f,sort_keys=True,indent=2);f.write('\n')
    os.replace(out/'state.tmp',out/'state.json')
def create_owned_state(out):
    state={'status':'STARTING','rows':[]};out.mkdir(mode=0o700)
    try: write_state(out,state)
    except BaseException as e:
        state.update(status='FAILED',failure=repr(e))
        try: write_state(out,state)
        except BaseException as receipt_error: print('FAILED_TO_RECORD_INITIAL_STATE',repr(receipt_error),file=sys.stderr,flush=True)
        raise
    return state
def mark_failed(state,error,elapsed):
    state.update(status='FAILED',failure=repr(error),elapsed_seconds=round(elapsed,3))
def record_child_result(row,kind,res,log,save):
    res['log']=str(log)
    try: res['log_sha256']=sha(log,watch_resources=False)
    except BaseException as e: res['log_hash_error']=repr(e)
    row[kind]=res;save(force=True)
    need('log_hash_error' not in res,'unable to hash '+kind+' log')

def preflight(require_fresh=True, enforce_resources=True):
    for path,expected in PINS.items(): need(path.is_file() and sha(path)==expected,'pin drift '+str(path))
    if require_fresh: need(not os.path.lexists(OUT),'output already exists')
    why=decision(shutil.disk_usage('/tmp').free,mem_available(),0)
    if enforce_resources: need(why is None,'resource refusal '+str(why))
    plan=json.loads(PLAN.read_text()); entries=plan['entries']; names=[e['module'] for e in entries]
    need(names==['DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.P73Graph','P73Shared91'], 'stage order drift')
    need([len(e['reports']) for e in entries]==[12,12,3], 'report count drift')
    need(set(plan['fixed_direct_routes'])=={'DiophantineConsistency.Compact44.FreeJSumSquares',
         'DiophantineConsistency.Compact44.FreeJSignedTransport','Mathlib.Tactic.LinearCombination','Init'},'fixed route inventory')
    for entry in entries:
        src=ROOT/entry['source']
        need(not Path(entry['source']).is_absolute() and src.resolve().is_relative_to(ROOT) and src.is_file() and
             sha(src)==entry['source_sha256'],'source pin '+entry['module'])
        need(source_imports(src)==entry['imports'] and source_reports(src)==entry['reports'],'source imports/reports '+entry['module'])
    tracked=set(git_query('ls-files','-z','--',*(e['source'] for e in entries)).decode().split('\0'))
    head=git_query('rev-parse','HEAD').decode().strip()
    dirty=set(git_query('diff','--name-only',head,'--',*(e['source'] for e in entries)).decode().splitlines())
    need(all(e['source'] in tracked and e['source'] not in dirty for e in entries),'source not tracked or differs from HEAD')
    q=subprocess.run([sys.executable,'-I','-S','-B',str(SURVEY)],cwd=ROOT,
                     stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
    need(q.returncode==0 and not q.stderr,'collision survey failed: '+q.stderr.decode(errors='replace')[-500:])
    if ACTIVE_WATCH is not None: ACTIVE_WATCH.check()
    obs=json.loads(q.stdout)
    need(obs['status']=='READ_ONLY_OBSERVATION_NOT_BUILD_READINESS' and not obs['head_changed_during_prior_survey'],'survey status/head')
    need(obs['head']==head and git_query('rev-parse','HEAD').decode().strip()==head,'HEAD changed during preflight')
    need(not obs['route_issues'] and not obs['different_hash_candidates'],'route/candidate conflict')
    inv=obs['overlay_inventory'];need(not inv['inventory_issues'] and not inv['cross_root_companion_intersections'],'P72 overlay collision')
    need(inv['observed_olean_names']==inv['expected_names']==1681,'P72 overlay inventory')
    need(not obs['excluded_target_artifacts'] and not obs['provider_snapshot_target_sources'],'source/output target collision')
    need(obs['counts']['p72_producers']==13 and obs['counts']['base_producers']==17 and
         obs['counts']['p72_direct_guard_slots']==1050 and obs['counts']['base_output_guard_slots']==170,'graph ancestry inventory')
    for name,expected in plan['fixed_direct_routes'].items():
        candidates=[root/(name.replace('.','/')+'.olean') for root in (P72/'lib',PKG,TOOL)]
        hits=[p for p in candidates if p.is_file()]
        need(hits and str(hits[0].resolve())==expected['realpath'] and sha(hits[0])==expected['sha256'],'fixed direct route '+name)
    if ACTIVE_WATCH is not None: ACTIVE_WATCH.check()
    why=decision(shutil.disk_usage('/tmp').free,mem_available(),0)
    if enforce_resources: need(why is None,'resource refusal '+str(why))
    return plan,obs,why

def self_test():
    need(decision(DISK_FLOOR,MEM_FLOOR,0)=='disk_floor','disk boundary')
    need(decision(DISK_FLOOR+1,MEM_FLOOR-1,0)=='host_memory_floor','memory boundary')
    need(decision(DISK_FLOOR+1,MEM_FLOOR,TOTAL_SECONDS)=='total_timeout','time boundary')
    need(decision(DISK_FLOOR+1,MEM_FLOOR,0) is None,'safe boundary')
    reports=['test.one','test.two']
    sample="'test.one' depends on axioms: [propext, Quot.sound]\n"+"'test.two' does not depend on any axioms"
    validate_reports(sample,reports)
    for bad in (sample.replace('propext','sorryAx'),sample.replace('test.one','wrong.name'),sample+'\n'+sample.splitlines()[0]):
        try: validate_reports(bad,reports)
        except Refusal: continue
        raise Refusal('bad axiom report accepted')
    print(json.dumps({'status':'PASS_SYNTHETIC_CONTROLS','scope':'Pure resource/report tests; no Lean or output tree.'},sort_keys=True))

def run():
    global ACTIVE_WATCH
    start=time.monotonic();watch=Watch(start);watch.begin();ACTIVE_WATCH=watch;state=None
    def save(force=False):
        if not force: watch.check()
        write_state(OUT,state)
    try:
        watch.check();runner_digest=sha(__file__);plan,_,_=preflight();watch.check();no_live_lean();watch.check()
        need(sha(__file__)==runner_digest,'runner changed during preflight')
        state=create_owned_state(OUT);watch.check()
        state.update(status='RUNNING',scope='Three-stage P73 graph-only client over retained P72 provider; no endpoint or file semantics; package/dynamic ancestry inherited.',
                     plan_sha256=sha(PLAN),runner_sha256=runner_digest,monitor_sha256=sha(MON),started_wall_seconds=time.time())
        save()
        for directory in ('src','lib','logs'):
            watch.check();(OUT/directory).mkdir()
        entries=plan['entries']
        for entry in entries:
            watch.check();src=ROOT/entry['source'];need(sha(src)==entry['source_sha256'],'source drift')
            dst=OUT/'src'/(entry['module'].replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True)
            with src.open('rb') as inp,dst.open('xb') as out:
                while True:
                    watch.check();block=inp.read(1024*1024)
                    if not block: break
                    out.write(block)
            need(sha(dst)==entry['source_sha256'],'source snapshot drift')
        spec=importlib.util.spec_from_file_location('p73_monitor',MON);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
        env=os.environ.copy()
        for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'): env.pop(key,None)
        env['LEAN_PATH']=str(OUT/'lib')+':'+str(P72/'lib')+':'+str(PKG);env['LEAN_NUM_THREADS']='1'
        roots=(OUT/'lib',P72/'lib',PKG,TOOL);completed={}
        for index,entry in enumerate(entries):
            watch.check();no_live_lean();name=entry['module']
            src=OUT/'src'/(name.replace('.','/')+'.lean');obj=OUT/'lib'/(name.replace('.','/')+'.olean')
            obj.parent.mkdir(parents=True,exist_ok=True)
            for suffix in SUFFIXES: need(not os.path.lexists(OUT/'lib'/(name.replace('.','/')+suffix)),'output collision '+name+suffix)
            row={'module':name,'source_sha256':entry['source_sha256']};state['rows'].append(row);save()
            print('STAGE',index+1,'/',len(entries),name,flush=True)
            prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M3600','-j1','-DElab.async=false']
            def child(args,kind):
                watch.check();remaining=TOTAL_SECONDS-(time.monotonic()-start);need(remaining>0,'total timeout')
                log=OUT/'logs'/(f'{index:03d}-'+name.replace('.','_')+'-'+kind+'.txt')
                res=monitor.run(prefix+args,OUT,env,log,rss_limit=RSS_LIMIT,mem_floor=MEM_FLOOR,
                                disk_floor=DISK_FLOOR,seconds=min(CHILD_SECONDS,remaining),interval=INTERVAL)
                record_child_result(row,kind,res,log,save);watch.check()
                need(res['exit']==0 and res['stop_reason'] is None and not res['monitor_errors'] and
                     not res['observed_descendant_pids'],kind+' failed '+name)
                return log
            depslog=child(['--deps',str(src)],'deps');records={};counts={}
            for line in depslog.read_text().splitlines():
                path=Path(line);hits=[root for root in roots if path.is_relative_to(root)]
                need(path.is_absolute() and path.is_file() and line.endswith('.olean') and len(hits)==1,'bad dependency path '+line)
                dep=str(path.relative_to(hits[0]))[:-6].replace('/','.');counts[dep]=counts.get(dep,0)+1
                need(dep not in records or (dep=='Init' and counts[dep]<=2 and records[dep]['path']==line),'duplicate dependency '+dep)
                records[dep]={'path':line,'realpath':str(path.resolve()),'sha256':sha(path)}
            need('Init' in records and set(records)-{'Init'}==set(entry['imports'])-{'Init'},'direct dependency set '+name)
            for dep,item in records.items():
                candidates=[root/(dep.replace('.','/')+'.olean') for root in roots if (root/(dep.replace('.','/')+'.olean')).is_file()]
                need(candidates and str(candidates[0])==item['path'],'first dependency route '+dep)
                if dep in completed:
                    expected={'realpath':str((OUT/'lib'/(dep.replace('.','/')+'.olean')).resolve()),'sha256':completed[dep]}
                else:
                    need(dep in plan['fixed_direct_routes'],'unplanned dependency '+dep);expected=plan['fixed_direct_routes'][dep]
                need(item['realpath']==expected['realpath'] and item['sha256']==expected['sha256'],'producer mismatch '+name+' -> '+dep)
            row['dependencies']=records;row['direct_guard']=inspect_guards(records);save()
            log=child(['--root='+str(OUT/'src'),str(src),'-o',str(obj)],'compile');text=log.read_text()
            need(not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",text) and obj.is_file(),'compile diagnostics '+name)
            need(inspect_guards(records)==row['direct_guard'],'direct guard drift '+name)
            validate_reports(text,entry['reports']);row['object_sha256']=sha(obj);row['output_guard']={}
            for suffix in SUFFIXES:
                p=OUT/'lib'/(name.replace('.','/')+suffix)
                if os.path.lexists(p):
                    need(p.is_file() and not p.is_symlink(),'bad output companion '+str(p))
                    row['output_guard'][str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
                else: row['output_guard'][str(p)]=None
            completed[name]=row['object_sha256'];save();print('PASS',name,flush=True)
        need(len(completed)==3,'compiled stage inventory')
        for entry,row in zip(entries,state['rows']):
            watch.check();name=entry['module'];src=OUT/'src'/(name.replace('.','/')+'.lean')
            need(sha(ROOT/entry['source'])==entry['source_sha256'] and sha(src)==entry['source_sha256'],'source postflight '+name)
            need(sha(OUT/'lib'/(name.replace('.','/')+'.olean'))==row['object_sha256'] and
                 inspect_guards(row['dependencies'])==row['direct_guard'],'output/direct postflight '+name)
            for raw,val in row['output_guard'].items():
                p=Path(raw)
                if val is None: need(not os.path.lexists(p),'unexpected output companion '+raw)
                else: need(p.is_file() and not p.is_symlink() and str(p.resolve())==val['realpath'] and sha(p)==val['sha256'],'output companion drift '+raw)
            for kind in ('deps','compile'): need(sha(row[kind]['log'])==row[kind]['log_sha256'],'log postflight '+name)
        watch.check();plan2,_,_=preflight(require_fresh=False);need(plan2==plan,'postflight plan drift')
        need(sha(__file__)==runner_digest,'runner changed during run');watch.check()
        state['status']='PASS';state['elapsed_seconds']=round(time.monotonic()-start,3);save()
        print('PASS P73 shared graph evaluation client',flush=True)
    except BaseException as e:
        if state is not None:
            mark_failed(state,e,time.monotonic()-start)
            try: save(force=True)
            except BaseException as receipt_error: print('FAILED_TO_RECORD_STATE',repr(receipt_error),file=sys.stderr,flush=True)
        raise
    finally:
        ACTIVE_WATCH=None;watch.stop()

def guarded_preflight():
    global ACTIVE_WATCH
    watch=Watch(time.monotonic());watch.begin();ACTIVE_WATCH=watch
    try:
        watch.check();plan,obs,_=preflight();watch.check()
        print(json.dumps({'status':'PASS_NO_LEAN_PREFLIGHT','stages':len(plan['entries']),
                          'disk_free':shutil.disk_usage('/tmp').free,'disk_stop_bytes':DISK_FLOOR,
                          'scope':'No Lean or output created; provider/package/dynamic limits remain.'},sort_keys=True))
    finally:
        ACTIVE_WATCH=None;watch.stop()

if __name__=='__main__':
    try:
        if sys.argv[1:]==['--self-test']: self_test()
        elif sys.argv[1:]==['--inspect']:
            plan,obs,why=preflight(enforce_resources=False)
            print(json.dumps({'status':'READ_ONLY_INSPECTION_NOT_LAUNCH_APPROVAL','stages':len(plan['entries']),
                              'resource_refusal':why,'disk_free':shutil.disk_usage('/tmp').free,
                              'disk_stop_bytes':DISK_FLOOR,'scope':'No Lean, no output tree.'},sort_keys=True))
        elif sys.argv[1:]==['--preflight']: guarded_preflight()
        elif sys.argv[1:]==['--run']: run()
        else: raise Refusal('use --self-test, --inspect, --preflight or --run')
    except BaseException as e:
        print('REFUSED_OR_FAILED',repr(e),file=sys.stderr);raise
