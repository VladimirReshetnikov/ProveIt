from pathlib import Path
import os,re,subprocess,json,time,sys,hashlib,shutil

base=Path(__file__).resolve().parent
src=base/'src'
cache=base/'cache'
cache.mkdir(exist_ok=True)
lean=os.environ.get('ZFC_LEAN') or shutil.which('lean') or '/tmp/lean-4.32.0-linux/bin/lean'
manifest=json.loads((base/'source_manifest.json').read_text())
for item in manifest['sources']:
    p=src/Path(item['module'].replace('.','/')+'.lean')
    data=p.read_bytes()
    digest=hashlib.sha1(b'blob '+str(len(data)).encode()+bytes([0])+data).hexdigest()
    if digest != item['git_blob_sha']:
        raise SystemExit('Pinned source mismatch: '+str(p))
version=subprocess.run([lean,'--version'],capture_output=True,text=True,check=True).stdout.strip()
seen=set()
ordered=[]
def visit(p):
    if p in seen:
        return
    seen.add(p)
    for name in re.findall(r'^import ([A-Za-z0-9_.]+)',p.read_text(),re.M):
        q=src/Path(name.replace('.','/')+'.lean')
        if q.exists():
            visit(q)
    ordered.append(p)
roots=sys.argv[1:] or ['BusyBeaver/ZFC/EnumModelBridge254.lean','BusyBeaver/ZFC/ModelBridge254Checks.lean']
for name in roots:
    visit(src/name)
log=[]
env={**os.environ,'LEAN_PATH':str(cache)}
for p in ordered:
    out=cache/p.relative_to(src).with_suffix('.olean')
    out.parent.mkdir(parents=True,exist_ok=True)
    t=time.monotonic()
    r=subprocess.run([lean,'-o',str(out),str(p)],capture_output=True,text=True,env=env)
    item={'path':str(p.relative_to(src)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'seconds':time.monotonic()-t,'returncode':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
    log.append(item)
    print(item['path'],r.returncode,round(item['seconds'],3),flush=True)
    if r.returncode:
        print(r.stdout,r.stderr,flush=True)
        break
(base/'dependency-build.json').write_text(json.dumps(log,indent=2))
(base/'verification.json').write_text(json.dumps({
    'status':'PASS' if len(log)==len(ordered) and all(x['returncode']==0 for x in log) else 'FAIL',
    'scope':'Same-structure original decoded/encodable/native-CP-GIC model equivalence and abstract enumerator characterization; no binary machine or internal-ZFC theorem.',
    'compiler':version,'command':[lean,'-o','<cache module>','<source module>'],
    'pinned_repository':manifest['repository'],'pinned_commit':manifest['commit'],
    'upstream_git_blobs_verified':len(manifest['sources']),
    'all_source_modules_recompiled':len(log),'module_count_expected':len(ordered),
    'total_compile_seconds':sum(x['seconds'] for x in log),
    'new_source_sha256':{p:hashlib.sha256((src/p).read_bytes()).hexdigest() for p in manifest['new_sources']},
    'allowed_axioms':['propext','Classical.choice','Quot.sound'],
    'proof_audit_output':'\n'.join(x['stdout'] for x in log if x['path'] in manifest['new_sources']),
    'logs':'dependency-build.json'},indent=2))
sys.exit(log[-1]['returncode'])
