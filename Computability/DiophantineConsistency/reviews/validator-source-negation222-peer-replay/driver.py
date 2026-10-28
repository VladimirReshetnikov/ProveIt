import hashlib, json, os, re, shutil, subprocess, tempfile, time
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=ROOT/'Computability/DiophantineConsistency'
CACHE=DC/'reviews/validator-source-negation222-cache.json'
CACHE_HASH='fb33ff9c1bf83ca829d82958beadb725e3db1a347878caac2ab1a98e55fc4fae'
AUTHOR=DC/'reviews/validator-source-negation222-author-replay'
FIXED={
 str(CACHE):CACHE_HASH,
 str(DC/'reviews/validator-source-negation222-replay.json'):'cfb206112f8eb04f4a104a7313b8ef51cb566bb82509518f731d78accd81351e',
 str(DC/'reviews/validator-source-negation222-author.md'):'9dcf2b99736157f99d9015580dd275a5b2229d79ad672859c91b1ec9286ca025',
 str(AUTHOR/'FILES.json'):'70c7319c28aab8df8b6ebb065a7d3ad017a599266bd4d5dc658e64b3fba57920'}
LEAVES=[
 ('ZFCinPA.ValidatorSourceNegation222','766f589378be9c2bfe583f248b8e2a448945d74114400f46c7d8ed210bbd16b4','6155f06b7f9809a19ca7aec04c4f813fd69f58a41dc88e1a9a547f35eac6f119'),
 ('ZFCinPA.ValidatorSourceNegation222Checks','7fd75fe179da81627761d1ad4845bd0bf8c81768e3fd6db1691ae450e1f2afcc','aa98d0b79ce994484b5e4250522a269e17fa753016cc65040148d8ca89257c29')]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok, msg):
    if not ok: raise RuntimeError(msg)
def stripped(s):
    # Keep line structure and strings; erase nested comments and line comments.
    out=[]; i=0; depth=0; quoted=False
    while i<len(s):
        pair=s[i:i+2]
        if depth:
            if pair=='/-': depth+=1; out.extend('  '); i+=2
            elif pair=='-/': depth-=1; out.extend('  '); i+=2
            else: out.append('\n' if s[i]=='\n' else ' '); i+=1
        elif quoted:
            out.append(s[i])
            if s[i]=='\\' and i+1<len(s): out.append(s[i+1]); i+=2; continue
            if s[i]=='"': quoted=False
            i+=1
        elif pair=='/-': depth=1; out.extend('  '); i+=2
        elif pair=='--':
            while i<len(s) and s[i]!='\n': out.append(' '); i+=1
        else:
            if s[i]=='"': quoted=True
            out.append(s[i]); i+=1
    require(depth==0,'unterminated block comment')
    return ''.join(out)
def imports(path):
    s=stripped(Path(path).read_text())
    result=[] if re.search(r'^\s*prelude\s*$',s,re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M):
        result.extend(re.findall(r'[\w.]+',line))
    return result
require(sha(CACHE)==CACHE_HASH,'author inventory pin')
data=json.loads(CACHE.read_text())
require(data['counts']=={'cached':152,'foundation':117,'artifacts':503,'boundaries':40},'exact inventory size')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve before setup')
out=Path(tempfile.mkdtemp(prefix='validator-source-negation222-peer-'))
lib=out/'lib';lib.mkdir();OBS=[]
shutil.copy2(__file__,out/'driver.py')
shutil.copy2(CACHE,out/'inputs.json')
state={'status':'AUTHENTICATING','scope':'Independent two-leaf replay; all 152 prerequisites reused, no Foundation/dependency build.',
       'overlay':str(out),'inventory_sha256':CACHE_HASH,'driver_sha256':sha(__file__),'completed':[]}
def save():
    (out/'state.json').write_text(json.dumps(state,indent=2)+'\n')
    (out/'observations.json').write_text(json.dumps(OBS,indent=2)+'\n')
def observe(p,h,role):
    actual=sha(p);require(actual==h,role+' mismatch '+str(p))
    OBS.append({'path':str(p),'sha256':actual,'role':role})
def check_all():
    for p,h in FIXED.items(): observe(p,h,'author packet')
    for k in ['compiler','manifest','toolchain']: observe(data[k],data[k+'_sha256'],k)
    for p in data['parent_receipts']: observe(p['path'],p['sha256'],'parent receipt')
    for r in data['modules']:
        observe(r['source'],r['source_sha256'],'cached source')
        for a in r['objects']: observe(a['path'],a['sha256'],'cached artifact')
    for r in data['external']: observe(r['path'],r['sha256'],'explicit external boundary')
    for r in json.loads((AUTHOR/'FILES.json').read_text()): observe(AUTHOR/r['path'],r['sha256'],'author evidence file')
    for name,h,_ in LEAVES:
        observe(ROOT/'Logic/Interpretability/ZFCinPA/Lean'/(name.replace('.','/')+'.lean'),h,'fresh source')
try:
    check_all()
    selected={r['module'] for r in data['modules']}; external={r['module'] for r in data['external']}
    require(len(selected)==152 and len(external)==40,'unique inventory')
    for r in data['modules']:
        actual=imports(r['source'])
        require(set(actual)==set(r['imports']),'import header '+r['module'])
        require(set(actual)<=(selected|external),'unaccounted dependency '+r['module'])
        stem=lib/r['module'].replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
        base=r['module'].rsplit('.',1)[-1]
        for a in r['objects']:
            p=Path(a['path']);require(p.name.startswith(base+'.'),'artifact suffix')
            dest=Path(str(stem)+p.name[len(base):]);require(not dest.exists(),'duplicate object')
            dest.symlink_to(p)
    require('Init' in external and 'Aesop' in external,'implicit/meta boundaries')
    env=dict(os.environ,LEAN_PATH=str(lib)+':'+data['lean_path'].split(':',1)[1],LEAN_NUM_THREADS='1')
    env.pop('LEAN_SRC_PATH',None)
    state['lean_path']=env['LEAN_PATH'];state['counts']=data['counts'];state['status']='RUNNING';save()
    for name,h,expected_object in LEAVES:
        require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve before leaf')
        source=ROOT/'Logic/Interpretability/ZFCinPA/Lean'/(name.replace('.','/')+'.lean')
        require(set(imports(source)) <= (selected|external|{n for n,_,_ in LEAVES}),'leaf imports')
        code=stripped(source.read_text())
        require(not re.search(r'\b(sorry|admit|native_decide|axiom)\b',code),'proof shortcut')
        snapshot=out/source.name;shutil.copy2(source,snapshot)
        target=lib/(name.replace('.','/')+'.olean')
        require(not target.exists() and not target.is_symlink(),'fresh target')
        target.parent.mkdir(parents=True,exist_ok=True)
        log=out/(name+'.log');timing=out/(name+'.time')
        command=[data['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(target),str(source)]
        row={'module':name,'source':str(source),'source_sha256':h,'snapshot':str(snapshot),'command':command,'expected_object':expected_object}
        state['active']=row;save();print('START '+name,flush=True);start=time.monotonic()
        with log.open('w') as f:
            result=subprocess.run(['/usr/bin/time','-v','-o',str(timing)]+command,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
        row.update(exit_code=result.returncode,seconds=time.monotonic()-start,log=str(log),log_sha256=sha(log),timing=str(timing),timing_sha256=sha(timing))
        state['completed'].append(row);state.pop('active',None);save()
        require(result.returncode==0,'Lean failed '+name)
        require(target.is_file() and not target.is_symlink(),'regular new output')
        row['object']={'path':str(target),'sha256':sha(target),'bytes':target.stat().st_size}
        require(sha(target)==expected_object,'author/peer object differs '+name)
        reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log.read_text(),flags=re.S)
        row['axiom_reports']=reports
        for theorem,axioms in reports:
            require(set(re.findall(r'[\w.]+',axioms))<={'propext','Classical.choice','Quot.sound'},'unexpected axiom '+theorem)
        require('warning:' not in log.read_text() and 'error:' not in log.read_text(),'diagnostic')
        check_all();save();print('PASS '+name+' '+str(row['seconds']),flush=True)
    require(sum(len(r['axiom_reports']) for r in state['completed'])==16,'exact report count')
    state['status']='PASS';state['observation_count']=len(OBS);save()
    print('PASS '+str(out),flush=True)
except BaseException as e:
    state['status']='FAIL';state['failure']=repr(e);save();print('FAIL '+str(out),flush=True);raise
