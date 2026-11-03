#!/usr/bin/env python3
"""DRAFT: capture-relative BFS 65-stage union replay. Do not launch before review."""
from pathlib import Path
from hashlib import sha256
import argparse, fcntl, importlib.util, json, os, re, shutil, subprocess, sys, tempfile, time

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
H=Path(__file__).resolve().parent; D=H.parents[1]
PLAN=D/'research/direct-bfs-80-coherent-rebuild-plan/observations/attempt01/result.json'
FIXED=D/'research/direct-bfs-80-ipra-serialized-audit/observations/attempt01/result.json'
REBUILT=D/'reviews/ten-positive-80-coherent-rebuilt-closure/observations/attempt01/result.json'
REPLAY=D/'research/ten-positive-80-coherent-rebuild/observations/attempt04/result.json'
V9=D/'research/ordinary12-direct90-ipra-join/run-v9.py'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SYS=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
PINS={PLAN:'14c9a694d6574037e70044fcec7ef12aae0d399ce1341add86cdafd1d0388893',
 FIXED:'beca7bfd182f49fb0640ed2b49bff33aa2aa8e1ec09bb1fa1d632b2f06ab9883',
 REBUILT:'75d4cf43ed4d716b15a13536be5a4cbba96ad03e2249aba7acdc7ace30892276',
 REPLAY:'e1ccee0f9c5fdc14cde89368925cb56f41d6acbe5c89a41c9e2bab798184582b',
 V9:'117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
SUFFIXES=('.olean','.olean.hash','.olean.private','.olean.private.hash','.olean.server',
          '.olean.server.hash','.ilean','.ilean.hash','.ir','.ir.hash')
ENDPOINT='DirectBFS80FixedIPRA'
THEOREMS=('standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency')
def need(b,m):
    if not b: raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rel(n):return n.replace('.','/')
def present(p):return os.path.lexists(p)
def files(stem):
    out={}
    for suffix in SUFFIXES:
        p=Path(str(stem)+suffix)
        if not present(p):out[suffix]=None;continue
        need(p.is_file(),'present non-regular or dangling path '+str(p))
        out[suffix]={'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p)}
    return out
def hashes(records):return {s:(None if x is None else x['sha256']) for s,x in records.items()}
def ensure_vacant(stem):
    for suffix in SUFFIXES:
        need(not present(Path(str(stem)+suffix)),'refusing to replace existing path '+str(stem)+suffix)
def check_records(stem,expected,mode):
    need(mode in ('link','regular','external'),'unknown provider mode')
    current=files(stem)
    need(set(current)==set(expected),'provider companion keys drift '+str(stem))
    for suffix,old in expected.items():
        new=current[suffix];path=Path(str(stem)+suffix)
        need((old is None)==(new is None),'provider presence drift '+str(path))
        if old is None:continue
        need(new['sha256']==old['sha256'] and new['resolved']==old['resolved'],'provider content or target drift '+str(path))
        if mode=='link':need(path.is_symlink(),'initial union entry is not symlink '+str(path))
        if mode=='regular':need(not path.is_symlink() and str(path.absolute())==new['resolved'],'built entry is not regular fresh-union path '+str(path))
    return current
def diagnostics_ok(text):
    return not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',text)
def endpoint_axioms_ok(text):
    for name in THEOREMS:
        pattern=r"'DirectBFS80FixedIPRA\."+re.escape(name)+r"' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
        matches=re.findall(pattern,text,re.S)
        if len(matches)!=1:return False
        if not set(x.strip() for x in matches[0].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}:return False
    return True
def resources():
    ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
    live=[x.strip() for x in ps if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean']
    mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])
    return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':live}
def imports(p):return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',p.read_text(),re.M)
def monitored(cmd,env,so,se,timeout=600):
    pre=resources();need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'resource preflight')
    samples=[];reason=None;start=time.monotonic()
    with so.open('x') as out,se.open('x') as err:
        proc=subprocess.Popen(cmd,env=env,stdout=out,stderr=err)
        try:
            while proc.poll() is None:
                sample=resources();samples.append(sample)
                if sample['mem_available_kib']<8*1024**2 or len(sample['lean'])>2:reason='resource guard';proc.terminate();break
                if time.monotonic()-start>timeout:reason='timeout';proc.terminate();break
                time.sleep(2)
            try:proc.wait(timeout=10)
            except subprocess.TimeoutExpired:proc.kill();proc.wait()
        finally:
            if proc.poll() is None:proc.kill();proc.wait()
    return {'exit':proc.returncode,'reason':reason,'elapsed':time.monotonic()-start,'preflight':pre,
            'postflight':resources(),'samples':samples,'stdout_sha256':sha(so),'stderr_sha256':sha(se)}
parser=argparse.ArgumentParser();parser.add_argument('--attempt');parser.add_argument('--preflight-only',action='store_true');args=parser.parse_args()
need(args.preflight_only != bool(args.attempt),'specify exactly one of --preflight-only or --attempt')
if args.attempt:need(re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is not None,'bad attempt')
if args.attempt:
    lock_fd=os.open('/tmp/direct-bfs-80-coherent-rebuild.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600)
    fcntl.flock(lock_fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
for p,h in PINS.items():need(sha(p)==h,'input pin drift '+str(p))
plan=json.loads(PLAN.read_text());fixed=json.loads(FIXED.read_text());rebuilt=json.loads(REBUILT.read_text());replay=json.loads(REPLAY.read_text())
need(fixed['status']=='PASS_CAPTURE' and rebuilt['status']=='PASS' and replay['status']=='PASS','input status')
P=fixed['closure']['project'];O=fixed['closure']['outside'];B=rebuilt['selected_project'];BO=rebuilt['selected_outside']
order=plan['rebuild_order'];todo=[x['module'] for x in order];supp=plan['unaffected_missing_supplements']
need(len(todo)==65 and len(set(todo))==65 and todo[-1]==ENDPOINT and [x['index'] for x in order]==list(range(1,66)),'bad stage order')
need(len(supp)==101 and len(set(supp))==101 and not (set(todo)&set(supp)),'bad supplement set')
need(set(P)-set(B)==set(todo)|set(supp),'missing project classification')
need(set(O)==set(BO) and len(O)==80,'outside set mismatch')
need(len(B)==1765 and len(P)==1795,'project count drift')
for name in O:
    need(hashes(O[name]['companions'])==hashes(BO[name]),'outside capture mismatch '+name)
stagepos={n:i for i,n in enumerate(todo)}
for row in order:
    n=row['module'];src=Path(row['producer']['source_snapshot']);receipt=Path(row['producer']['receipt'])
    need(sha(src)==row['producer']['source_sha256'] and sha(receipt)==row['producer']['receipt_sha256'],'source/receipt drift '+n)
    need(imports(src)==[x for x in P[n]['imports'] if x!='Init'],'source imports changed '+n)
    for dep in P[n]['imports']:
        if dep in stagepos:need(stagepos[dep]<stagepos[n],'non-topological '+n+' '+dep)
# The prior union objects are used as captured; companion paths and bytes must still exist.
initial={}
for n,record in B.items():
    stem=Path(str(record['.olean']['path'])[:-6]);cur=files(stem)
    need(hashes(cur)==hashes(record),'rebuilt union drift '+n)
    for suffix,x in record.items():
        if x is not None:need(cur[suffix]['resolved']==x['real_path'],'rebuilt target drift '+n+suffix)
    initial[n]=cur
for n in supp:
    row=P[n];stem=Path(str(row['path'])[:-6]);cur=files(stem)
    need(hashes(cur)==hashes(row['companions']),'supplement drift '+n)
    for suffix,x in row['companions'].items():
        if x is not None:need(cur[suffix]['resolved']==x['resolved'],'supplement target drift '+n+suffix)
    initial[n]=cur
outside={}
for n,row in O.items():
    stem=Path(str(row['path'])[:-6]);cur=files(stem)
    need(hashes(cur)==hashes(row['companions']),'outside drift '+n)
    for suffix,x in row['companions'].items():
        if x is not None:need(cur[suffix]['resolved']==x['resolved'],'outside target drift '+n+suffix)
    outside[n]=cur
known=set(B)|set(P)
project_roots={n.split('.')[0] for n in known if '.' in n}
outside_roots={n.split('.')[0] for n in O if '.' in n}
need(not project_roots & outside_roots,'project/outside namespace shadow')
need(len(known)==1931 and len(initial)==1866,'union count drift')
need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
pre=resources();need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'resource preflight')
if args.preflight_only:
    print(json.dumps({'status':'PREFLIGHT_PASS','base':len(B),'supplements':len(supp),'to_build':len(todo),'known_project':len(known),'outside':len(O),'resources':pre}))
    raise SystemExit(0)
obs=H/'observations'/args.attempt;need(not present(obs),'observation exists');obs.mkdir(parents=True)
out=Path(tempfile.mkdtemp(prefix='direct-bfs-80-coherent-'));union=out/'lib';srcroot=out/'src';union.mkdir();srcroot.mkdir()
runner_hash=sha(Path(__file__))
result={'status':'RUNNING','attempt':args.attempt,'output_root':str(out),'preflight':pre,'inputs':{str(k):v for k,v in PINS.items()},
 'runner_sha256':runner_hash,'stages':[],'scope':'fresh selected union plus 65 source-pinned stages; prior 127 replay and unrebuilt source/package/dynamic ancestry remain inherited'}
def save():
    tmp=obs/'result.json.tmp';tmp.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');os.replace(tmp,obs/'result.json')
try:
    (obs/'initial-project.json').write_text(json.dumps(initial,indent=2,sort_keys=True)+'\n')
    (obs/'outside-baseline.json').write_text(json.dumps(outside,indent=2,sort_keys=True)+'\n')
    result['initial_project_sha256']=sha(obs/'initial-project.json');result['outside_baseline_sha256']=sha(obs/'outside-baseline.json')
    for n,records in initial.items():
        stem=union/rel(n);stem.parent.mkdir(parents=True,exist_ok=True)
        for suffix,rec in records.items():
            if rec is not None:Path(str(stem)+suffix).symlink_to(rec['resolved'])
    # Refuse namespace shadowing: any outside root selected by Lean cannot also
    # be an initial project namespace directory or an exact known project name.
    for n in O:
        need(n not in known,'outside module also known project '+n)
        need(not present(union/(rel(n)+'.olean')),'outside object shadowed '+n)
    snapshots={}
    for row in order:
        n=row['module'];source=Path(row['producer']['source_snapshot']);dst=srcroot/(rel(n)+'.lean');dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source,dst);need(sha(dst)==row['producer']['source_sha256'],'source copy mismatch '+n);snapshots[n]=dst
    env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(union)+':'+str(PACK),'LEAN_NUM_THREADS':'1'}
    built={}
    def resolve(n):
        path=rel(n)+'.olean'
        choices=[]
        for root in (union,PACK,SYS):
            candidate=root/path
            if present(candidate):
                need(candidate.is_file(),'invalid selected object '+str(candidate))
                choices.append(candidate)
        need(choices,'unresolved '+n);chosen=choices[0]
        if n in known:
            need(chosen==union/path,'project fallback '+n)
            need(n in initial or n in built,'unbuilt project import '+n)
            return check_records(union/rel(n),built[n] if n in built else initial[n],
                                 'regular' if n in built else 'link')
        need(n in outside,'untracked outside '+n)
        need(str(chosen)==O[n]['path'],'outside selection path drift '+n)
        return check_records(Path(str(chosen)[:-6]),outside[n],'external')
    def check_built():
        for name,rec in built.items():check_records(union/rel(name),rec,'regular')
    for row in order:
        n=row['module'];idx=row['index'];target=snapshots[n];stem=union/rel(n);stem.parent.mkdir(parents=True,exist_ok=True)
        stage=obs/f'stage-{idx:03}';stage.mkdir();shutil.copyfile(target,stage/'source.lean')
        record={'index':idx,'module':n,'source_sha256':sha(target),'status':'PREPARING'};result['stages'].append(record);save()
        need(sha(target)==sha(stage/'source.lean')==row['producer']['source_sha256'],'stage source drift '+n)
        check_built();deps=set(P[n]['imports']);before={dep:resolve(dep) for dep in sorted(deps)}
        for dep in deps:
            if dep in stagepos:need(dep in built,'unbuilt affected import '+n+' '+dep)
        ensure_vacant(stem)
        command=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={srcroot}',str(target),'-o',str(stem)+'.olean']
        record.update({'command':command,'direct_before':before,'status':'STARTING'});save()
        record.update(monitored(command,env,stage/'stdout',stage/'stderr'));record['status']='RETURNED'
        record['direct_after']={dep:resolve(dep) for dep in sorted(deps)};save()
        need(record['exit']==0 and record['reason'] is None,'Lean failure '+n)
        need(record['direct_before']==record['direct_after'],'direct dependency drift '+n)
        check_built();need(sha(target)==sha(stage/'source.lean')==sha(row['producer']['source_snapshot'])==row['producer']['source_sha256'],'source drift '+n)
        text=(stage/'stdout').read_text()+(stage/'stderr').read_text()
        need(diagnostics_ok(text),'diagnostic '+n)
        product=files(stem);need(product['.olean'] is not None,'missing output '+n)
        check_records(stem,product,'regular');built[n]=product;record['output']=product;save()
    def final_guards():
        for n,rec in initial.items():check_records(union/rel(n),rec,'link')
        check_built()
        for n,row in O.items():need(hashes(resolve(n))==hashes(outside[n]),'outside final drift '+n)
        for row in order:
            n=row['module'];stage=obs/f"stage-{row['index']:03}"
            need(sha(snapshots[n])==sha(stage/'source.lean')==sha(row['producer']['source_snapshot'])==row['producer']['source_sha256'],'final source drift '+n)
            need(sha(row['producer']['receipt'])==row['producer']['receipt_sha256'],'producer receipt drift '+n)
        for p,h in PINS.items():need(sha(p)==h,'final input drift '+str(p))
        need(sha(Path(__file__))==runner_hash,'runner drift')
        need(sha(obs/'initial-project.json')==result['initial_project_sha256'] and sha(obs/'outside-baseline.json')==result['outside_baseline_sha256'],'baseline drift')
    final_guards()
    # Re-read the whole selected transitive closure from the newly built root.
    spec=importlib.util.spec_from_file_location('audited_v9',V9);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    need(sha(m.LEAN)==m.PINS[m.LEAN] and sha(m.HELPER)==m.PINS[m.HELPER] and sha(m.INVENTORY)==m.PINS[m.INVENTORY],'reader tool drift')
    closure=m.scan_closure([ENDPOINT],[union],env,obs,'post',known)
    need(set(closure['project'])==set(P) and set(closure['outside'])==set(O),'post-closure membership differs; expand plan')
    for n,row in closure['project'].items():
        need(row['imports']==P[n]['imports'],'post header changed '+n)
        expected=built[n] if n in built else initial[n]
        need(hashes(row['companions'])==hashes(expected),'post selected project mismatch '+n)
    for n,row in closure['outside'].items():need(hashes(row['companions'])==hashes(outside[n]),'post selected outside mismatch '+n)
    m.recheck_outside(closure)
    endpoint=(obs/f"stage-{stagepos[ENDPOINT]+1:03}"/'stdout').read_text()
    need(endpoint_axioms_ok(endpoint),'endpoint axiom reports invalid')
    final_guards();need(sha(m.LEAN)==m.PINS[m.LEAN] and sha(m.HELPER)==m.PINS[m.HELPER] and sha(m.INVENTORY)==m.PINS[m.INVENTORY],'reader drift')
    result.update(status='PASS',closure=closure,built=built,postflight=resources());save()
    print(json.dumps({'status':'PASS','output_root':str(out),'stages':len(built),'result_sha256':sha(obs/'result.json')}),flush=True)
except BaseException as ex:
    result.update(status='FAILED',failure=repr(ex),postflight=resources());save();raise
