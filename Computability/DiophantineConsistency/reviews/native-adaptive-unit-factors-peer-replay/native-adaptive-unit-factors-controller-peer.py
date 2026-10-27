from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
V=R/'Computability/DiophantineConsistency/reviews'
P=V/'native-adaptive-unit-factors-replay.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return {'path':str(p),'sha256':sha(p)}
def check(e):
    if sha(e['path'])!=e['sha256']:raise RuntimeError('Pin mismatch: '+e['path'])
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def guard():
    free=shutil.disk_usage('/tmp').free
    if free<512*1024**2:raise RuntimeError('Disk reserve: '+str(free))
    return free
assert sha(P)=='be118b13e49d8c55ddeab16b010a973c99280264297ed2f11d6736ba07edd2de'
a=json.loads(P.read_text());check(a['inputs']);check(a['driver']);check(a['bundle_manifest'])
i=json.loads(Path(a['inputs']['path']).read_text());assert i['counts']==dict(custom=25,Foundation=0,artifacts=25,boundaries=22,external_companions=66)
mf=json.loads(Path(a['bundle_manifest']['path']).read_text())
for e in mf['files']:
    check(dict(path=str(Path(a['bundle_manifest']['path']).parent/e['path']),sha256=e['sha256']))
    check(dict(path=e['original'],sha256=e['sha256']))
for x in a['records']:
    for key in ['source','snapshot','log','timing','object']:check(x[key])
pins=[*i['pins'],rec(P),a['inputs'],a['driver'],a['bundle_manifest'],rec(__file__),rec(V/'native-adaptive-unit-factors-author.md')]
for x in a['records']:pins.extend([x['source'],x['object']])
for e in pins:check(e)
audit=json.loads(Path(i['pins'][0]['path']).read_text());scope=audit['scopes'][0]
known={x['module'] for x in i['modules']}|{x['module'] for x in scope['external_boundary']}
for m in i['modules']:
    check(dict(path=m['source'],sha256=m['source_sha256']))
    imports=['Init']+re.findall(r'^(?:(?:public|meta)\s+)*import\s+(\S+)',Path(m['source']).read_text(),re.M)
    assert imports==m['imports'],m['module']
    assert set(imports)<=known,(m['module'],set(imports)-known)
    for o in m['objects']:check(o)
assert len(i['pins'])==1523
guard();p=Path(tempfile.mkdtemp(prefix='native-adaptive-unit-factors-controller-peer-'));lib=p/'lib';lib.mkdir()
Path('/tmp/native-adaptive-unit-factors-controller-peer-location.txt').write_text(str(p))
for m in i['modules']:
    for o in m['objects']:
        d=lib/Path(*m['module'].split('.')[:-1])/Path(o['path']).name
        d.parent.mkdir(parents=True,exist_ok=True);d.symlink_to(o['path'])
external=i['lean_path'].split(':')[1:]
stdlib=str(Path(i['compiler']['path']).parent.parent/'lib/lean')
assert all('.lake/packages/' in x or x==stdlib for x in external)
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*external]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
inputs=dict(author=rec(P),author_inputs=a['inputs'],pins=pins,modules=i['modules'],counts=i['counts'],lean_path=env['LEAN_PATH'],compiler=i['compiler'],snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip())
save(p/'inputs.json',inputs)
result=dict(status='RUNNING',private=str(p),inputs=rec(p/'inputs.json'),driver=rec(__file__),records=[])
save(p/'RESULT.json',result)
for old in a['records']:
    free=guard()
    for e in pins:check(e)
    source=Path(old['source']['path']);name=source.stem;snapshot=p/source.name;shutil.copyfile(source,snapshot)
    out=lib/'DiophantineConsistency'/(name+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
    assert not out.exists() and not out.is_symlink()
    log=p/(name+'.log');timing=p/(name+'.time')
    cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(source)]
    start=time.monotonic()
    with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
    x=dict(module=old['module'],source=rec(source),snapshot=rec(snapshot),command=cmd,exit_code=code,seconds=time.monotonic()-start,free_before=free,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None)
    result['records'].append(x);save(p/'RESULT.json',result)
    assert sha(source)==sha(snapshot)
    if code:
        result['status']='FAILED';save(p/'RESULT.json',result);raise RuntimeError(log.read_text())
    x['author_object_equal']=sha(out)==old['object']['sha256']
    x['axiom_reports']=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())
    for _,ax in x['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
    save(p/'RESULT.json',result);print(json.dumps(x),flush=True)
for e in pins:check(e)
assert len(result['records'][0]['axiom_reports'])==0 and len(result['records'][1]['axiom_reports'])==5
result.update(status='PASS',final_pin_count=len(pins),free_after=shutil.disk_usage('/tmp').free)
save(p/'RESULT.json',result);print(json.dumps(dict(status='PASS',private=str(p),result=rec(p/'RESULT.json'))),flush=True)
