#!/usr/bin/env python3
"""DRAFT: guarded fresh-union replay of the observed 127-module cone.

Do not run until this exact script, inputs, scope, guards and warning policy
have been independently reviewed. No source or object outside a fresh /tmp
root is modified.
"""
from hashlib import sha256
from pathlib import Path
import argparse, json, os, re, shutil, subprocess, sys, tempfile, time

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
H=Path(__file__).resolve().parent; D=H.parents[1]
PLAN=D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json'
SCAN=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
CLIENT=D/'research/ten-positive-80-symbolic-ipra-client-prototype/observations/fixed-attempt01/terminal.json'
HELPER=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
WARNING_RECEIPT=D/'reviews/nine-variable-ipra-stages-6-9-author-observation/author/receipts/008.json'
WARNING_BASE=H/'warning-baseline-pigeonhole/baseline.txt'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SYS=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
EXPECTED_PLAN='cd224b6f17f9cd3cd08cf3a9e84923c1de9edbb635f6969cd4e1991e009b7e3a'
EXPECTED_SCAN='d65d7c776eb23425f9e2a290d8c3fdeebc011920619241290fdee85bc4ae68a9'
EXPECTED_HELPER='886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f'
EXPECTED_CLIENT='ba10b48d9c2843caf24c56938c88068ddb82372a43461c7ce7fb4ad2c62004da'
EXPECTED_LEAN='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
EXPECTED_WARNING_RECEIPT='86cea8817e9e52731cc61a6b3b983a0635d96cc8dba13ea1743ae6bb82133d94'
EXPECTED_WARNING_BASE='1848875f336080bc59033d40b66a69d97cc9d1e90904d4f0d559b998fff7de92'
WARNING_MODULE='DiophantineConsistency.ArithmeticPellPigeonhole'
WARNING_SOURCE='ebdbc22e239754f8f686be6971742d1b02560c9ffa35d464d2aecc323370765c'
SUFFIXES=('.olean','.olean.hash','.olean.private','.olean.private.hash','.olean.server',
          '.olean.server.hash','.ilean','.ilean.hash','.ir','.ir.hash')
ENDPOINT='Direct80SymbolicFixedIPRA'
THEOREMS=('standard_consistency','standard_translated_consistency',
          'reference_consistency','reference_translated_consistency')

def need(b,m):
    if not b: raise RuntimeError(m)
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def rel(name): return name.replace('.','/')
def files(stem):
    return {s:({'path':str(Path(str(stem)+s)),
                'resolved':str(Path(str(stem)+s).resolve(strict=True)),
                'sha256':sha(Path(str(stem)+s))} if Path(str(stem)+s).is_file() else None)
            for s in SUFFIXES}
def resource():
    rows=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
    ps=[x.strip() for x in rows if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean']
    mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])
    return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':ps}
def source_imports(p):
    imports=[]
    for line in p.read_text().splitlines():
        if line.startswith('import '): imports.extend(line[7:].split())
    return imports
def diagnostics_allowed(module,source_hash,text,source_path,baseline):
    diagnostic=re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)',text)
    return diagnostic is None or (module==WARNING_MODULE and source_hash==WARNING_SOURCE and
                                  text.replace(source_path,'<SOURCE>')==baseline)
def run_monitored(cmd,env,stdout,stderr,timeout=600):
    before=resource(); need(before['mem_available_kib']>=8*1024**2 and len(before['lean'])<2,'resource preflight')
    samples=[]; reason=None; start=time.monotonic()
    with stdout.open('x') as so, stderr.open('x') as se:
        proc=subprocess.Popen(cmd,env=env,stdout=so,stderr=se)
        try:
            while proc.poll() is None:
                s=resource();samples.append(s)
                if s['mem_available_kib']<8*1024**2 or len(s['lean'])>2:
                    reason='resource guard';proc.terminate();break
                if time.monotonic()-start>timeout:
                    reason='timeout';proc.terminate();break
                time.sleep(2)
            try: proc.wait(timeout=10)
            except subprocess.TimeoutExpired: proc.kill();proc.wait()
        finally:
            if proc.poll() is None:proc.kill();proc.wait()
    return {'exit':proc.returncode,'reason':reason,'elapsed':time.monotonic()-start,
            'preflight':before,'samples':samples,'postflight':resource(),
            'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr)}

parser=argparse.ArgumentParser()
parser.add_argument('--attempt',required=True)
arg=parser.parse_args()
need(re.fullmatch(r'attempt[0-9]{2,}',arg.attempt) is not None,'bad attempt')
obs=H/'observations'/arg.attempt
need(not obs.exists(),'observation exists')
need(sha(PLAN)==EXPECTED_PLAN and sha(SCAN)==EXPECTED_SCAN and sha(HELPER)==EXPECTED_HELPER and
     sha(CLIENT)==EXPECTED_CLIENT and sha(LEAN)==EXPECTED_LEAN and
     sha(WARNING_RECEIPT)==EXPECTED_WARNING_RECEIPT and sha(WARNING_BASE)==EXPECTED_WARNING_BASE,'input pin mismatch')
warning_receipt=json.loads(WARNING_RECEIPT.read_text())
need(warning_receipt['status']=='PASS' and warning_receipt['module']==WARNING_MODULE and
     warning_receipt['source_sha256']==WARNING_SOURCE and
     warning_receipt['warning_policy']['baseline_sha256']==EXPECTED_WARNING_BASE,'warning policy mismatch')
plan=json.loads(PLAN.read_text()); scan=json.loads(SCAN.read_text()); client=json.loads(CLIENT.read_text())
need(plan['status']=='PASS_PLAN_ONLY' and scan['status']=='PASS','input failed')
need(client['exit']==0 and client['reason'] is None and client['pins']==client['after'],'client receipt failed')
need(sha(LEAN)==client['pins']['lean'],'Lean binary drift')
need(len(plan['ordered'])==127 and len(set(plan['ordered']))==127 and plan['ordered'][-1]==ENDPOINT,'unexpected order')
need(set(plan['ordered'])==set(plan['sources']),'plan mismatch')
need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
project=scan['project']; outside=scan['outside']; need(len(project)==1765,'project count')
need(not scan['different_shadowed'],'selected overlap conflicts')
position={n:i for i,n in enumerate(plan['ordered'])}
for n in plan['ordered']:
    entry=plan['sources'][n]; source=Path(entry['source'])
    need(sha(source)==entry['sha256'],'source drift '+n)
    need(set(source_imports(source))==set(entry['imports'])==set(scan['fresh_headers'][n])-{ 'Init' },'imports drift '+n)
    for dep in entry['imports']:
        need(dep not in position or position[dep]<position[n],'non-topological order '+n+' '+dep)
for n,z in project.items():
    p=Path(z['selected']['path']);need(p.is_file() and sha(p)==z['selected']['sha256'],'project drift '+n)
outside_baseline={}
for n,z in outside.items():
    p=Path(z['path']);need(p.is_file() and sha(p)==z['sha256'],'outside drift '+n)
    outside_baseline[n]=files(Path(str(p)[:-6]))
pre=resource();need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'resource preflight')
obs.mkdir(parents=True)
out=Path(tempfile.mkdtemp(prefix='direct80-coherent-rebuild-')); union=out/'lib'; src=out/'src'; union.mkdir();src.mkdir()
result={'status':'RUNNING','attempt':arg.attempt,'output_root':str(out),'preflight':pre,
        'inputs':{str(p):sha(p) for p in (PLAN,SCAN,CLIENT,HELPER,LEAN,WARNING_RECEIPT,WARNING_BASE,H/'run-v4.py')},'stages':[],
        'scope':'fresh selected-project union and source-pinned 127-module replay; inherited unrebuilt ancestry, package-transitive and dynamic boundaries'}
def save():
    temporary=obs/'result.json.tmp'
    temporary.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    os.replace(temporary,obs/'result.json')
try:
    (obs/'outside-baseline.json').write_text(json.dumps(outside_baseline,indent=2,sort_keys=True)+'\n')
    result['outside_baseline_sha256']=sha(obs/'outside-baseline.json')
    # Materialize a single project namespace. Every link targets the exact
    # selected object's companion, not an unspecified earlier search root.
    initial={}
    for name,z in project.items():
        source=Path(z['selected']['path']); stem=Path(str(source)[:-6]); dest=union/rel(name);dest.parent.mkdir(parents=True,exist_ok=True)
        companions=files(stem);need(companions['.olean'] and companions['.olean']['sha256']==z['selected']['sha256'],'bad companion '+name)
        for suffix,rec in companions.items():
            if rec is not None: Path(str(dest)+suffix).symlink_to(rec['resolved'])
        initial[name]=companions
    (obs/'initial-project.json').write_text(json.dumps(initial,indent=2,sort_keys=True)+'\n')
    result['initial_project_sha256']=sha(obs/'initial-project.json')
    snapshots={}
    for n in plan['ordered']:
        target=src/(rel(n)+'.lean');target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(plan['sources'][n]['source'],target)
        need(sha(target)==plan['sources'][n]['sha256'],'copy mismatch '+n);snapshots[n]=target
    env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(union)+':'+str(PACK),'LEAN_NUM_THREADS':'1'}
    built={}; all_project=set(project)
    def resolve(name):
        path=rel(name)+'.olean'; choices=[r/path for r in (union,PACK,SYS) if (r/path).is_file()]
        need(choices,'unresolved '+name); chosen=choices[0]
        if name in all_project:need(chosen==union/path,'project fallback '+name)
        else:
            need(name in outside and str(chosen)==outside[name]['path'] and
                 sha(chosen)==outside[name]['sha256'],'outside selection drift '+name)
        snapshot=files(Path(str(chosen)[:-6]))
        if name not in all_project:need(snapshot==outside_baseline[name],'outside companion drift '+name)
        return snapshot
    def verify_unchanged(before):
        for name,snapshot in before.items():need(resolve(name)==snapshot,'direct dependency changed '+name)
    for index,n in enumerate(plan['ordered'],1):
        target=snapshots[n];stem=union/rel(n)
        so=obs/f'stage-{index:03}.stdout';se=obs/f'stage-{index:03}.stderr'
        command=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={src}',str(target),'-o',str(stem)+'.olean']
        record={'index':index,'module':n,'command':command,'status':'PREPARING'}
        result['stages'].append(record);save()
        need(sha(target)==sha(plan['sources'][n]['source'])==plan['sources'][n]['sha256'],'stage source drift '+n)
        deps=set(scan['fresh_headers'][n]); before={dep:resolve(dep) for dep in sorted(deps)}
        for dep in deps:
            if dep in position:need(dep in built,'unbuilt affected import '+n+' '+dep)
        for suffix in SUFFIXES:
            p=Path(str(stem)+suffix)
            if p.is_symlink():p.unlink()
            else:need(not p.exists(),'refusing to replace regular file '+str(p))
        record.update({'source_sha256':sha(target),'direct_before':before,'status':'STARTING'});save()
        record.update(run_monitored(command,env,so,se));record['status']='RETURNED'
        record['direct_after']={dep:resolve(dep) for dep in sorted(deps)};save()
        need(record['exit']==0 and record['reason'] is None,'Lean failure '+n)
        need(record['direct_before']==record['direct_after'],'direct guard failed '+n)
        need(sha(target)==plan['sources'][n]['sha256'] and sha(plan['sources'][n]['source'])==plan['sources'][n]['sha256'],'source changed '+n)
        text=so.read_text()+se.read_text()
        need(diagnostics_allowed(n,record['source_sha256'],text,str(target),WARNING_BASE.read_text()),
             'diagnostic or sorryAx '+n)
        if text:
            # A nonempty clean log remains permitted; the exact warning
            # exception is recorded only when the entire normalized log is
            # the pinned baseline.
            has_diagnostic=re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)',text)
        else:has_diagnostic=None
        if has_diagnostic:
            record['warning_exception']={'baseline_sha256':EXPECTED_WARNING_BASE,
                                         'receipt_sha256':EXPECTED_WARNING_RECEIPT,
                                         'normalization':'exact copied source path → <SOURCE>'}
        product=files(stem);need(product['.olean'] is not None,'missing object '+n)
        built[n]=product;record['output']=product;save()
    # The single union cannot contain stale affected artifacts. Recheck every
    # unrebuilt project companion and every produced companion after the run.
    for n in project:
        actual=files(union/rel(n)); expected=built[n] if n in built else initial[n]
        for suffix in SUFFIXES:
            a=actual[suffix];e=expected[suffix]
            need((a is None)==(e is None),'companion presence changed '+n+suffix)
            if a is not None:need(a['sha256']==e['sha256'],'companion hash changed '+n+suffix)
    for n in outside:
        need(resolve(n)==outside_baseline[n],'outside final drift '+n)
    for n,target in snapshots.items():
        need(sha(target)==sha(plan['sources'][n]['source'])==plan['sources'][n]['sha256'],'final source drift '+n)
    # Read the rebuilt objects' actual serialized headers, not merely source
    # imports, and reject missing/duplicate records or changed dependencies.
    outputs=[str(union/(rel(n)+'.olean')) for n in plan['ordered']]
    headers={}
    for k in range(0,len(outputs),32):
        chunk=outputs[k:k+32];so=obs/f'headers-{k//32:03}.stdout';se=obs/f'headers-{k//32:03}.stderr'
        command=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER),*chunk]
        hrun=run_monitored(command,env,so,se,timeout=120);need(hrun['exit']==0 and hrun['reason'] is None and not se.read_text(),'header reader failure')
        current=None;batch={}
        for line in so.read_text().splitlines():
            if line.startswith('BEGIN '):
                need(current is None and line[6:] in chunk and line[6:] not in batch,'bad header begin');current=line[6:];batch[current]=[]
            elif line.startswith('IMPORT ') and current is not None:batch[current].append(line[7:])
            elif line=='END' and current is not None:current=None
            else:raise RuntimeError('bad header line')
        need(current is None and set(batch)==set(chunk),'missing header')
        for path,imports in batch.items():
            name=plan['ordered'][outputs.index(path)]
            need(imports==scan['fresh_headers'][name],'serialized header changed '+name);headers[name]=imports
        result.setdefault('header_batches',[]).append(hrun);save()
    need(set(headers)==set(plan['ordered']),'incomplete headers')
    endpoint_log=(obs/f'stage-{position[ENDPOINT]+1:03}.stdout').read_text()
    for name in THEOREMS:
        need(re.search(r"'Direct80SymbolicFixedIPRA\."+re.escape(name)+r"' depends on axioms: \[propext, Classical\.choice, Quot\.sound\]",endpoint_log) is not None,'missing endpoint axiom report '+name)
    for n in project:
        actual=files(union/rel(n)); expected=built[n] if n in built else initial[n]
        for suffix in SUFFIXES:
            a=actual[suffix];e=expected[suffix]
            need((a is None)==(e is None),'post-header companion presence changed '+n+suffix)
            if a is not None:need(a['sha256']==e['sha256'],'post-header companion hash changed '+n+suffix)
    for n in outside:need(resolve(n)==outside_baseline[n],'post-header outside drift '+n)
    for n,target in snapshots.items():
        need(sha(target)==sha(plan['sources'][n]['source'])==plan['sources'][n]['sha256'],'post-header source drift '+n)
    need(sha(obs/'outside-baseline.json')==result['outside_baseline_sha256'],'outside baseline drift')
    for p,h in result['inputs'].items():need(sha(p)==h,'input drift '+p)
    result['status']='PASS';result['headers']=headers;result['built']=built;result['postflight']=resource();save()
    print(json.dumps({'status':'PASS','output_root':str(out),'stages':len(built),'result_sha256':sha(obs/'result.json')}))
except BaseException as ex:
    result['status']='FAILED';result['failure']=repr(ex);result['postflight']=resource();save()
    raise
