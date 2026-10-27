"""Authenticate the approved GIC closure and prepare only a private cache overlay."""
import hashlib,json,re,shutil,tempfile
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');D=ROOT/'Computability/DiophantineConsistency'
PLAN=D/'research/validator-seed-gic-image-accepted-provider.json'
MF=D/'research/validator-seed-gic-image-accepted-provider-FILES.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
    if not c:raise RuntimeError(m)
def pin(p,h):
    require(sha(p)==h,'drift '+str(p));return {'path':str(p),'sha256':h}
def imports(p):
    s=Path(p).read_text();out=[];i=0;depth=0
    while i<len(s):
        if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
        elif depth and s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
        elif not depth and s.startswith('--',i):
            j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
        else:out.append(s[i] if not depth or s[i]=='\n' else ' ');i+=1
    require(depth==0,'comment');s=''.join(out)
    names=[] if re.search(r'^\s*prelude\s*$',s,re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M):
        names.extend(re.findall(r'[\w.]+',line))
    return list(dict.fromkeys(names))
require(shutil.disk_usage('/tmp').free>=512*1024**2,'disk reserve')
pin(PLAN,'0a338dd4dc3e2eb15cf1bce3259d2851003684e1af6beac0ebd474ca96506046')
pin(MF,'80c139817199bfca3e31de4aa1ab25dd724308c88190bcaef166efc46b688ccf')
p=json.loads(PLAN.read_text());obs=[]
for r in json.loads(MF.read_text())['files']:obs.append(pin(MF.parent/r['path'],r['sha256']))
for r in p['observations']:obs.append(pin(r['path'],r['sha256']))
require(p['counts']=={'cached_modules':215,'foundation':136,'artifacts':623,'external_boundaries':45,'artifact_providers':668},'scope')
modules={r['module']:r for r in p['modules_dependency_order']};external={r['module']:r for r in p['external']}
seen=set();active=set();boundary=set()
def visit(n):
    if n in seen:return
    if n not in modules:require(n in external,'unknown '+n);boundary.add(n);return
    require(n not in active,'cycle');active.add(n);r=modules[n]
    obs.append(pin(r['source'],r['source_sha256']))
    actual=imports(r['source']);require(set(actual)==set(r['actual_imports']),'header '+n)
    for dep in actual:visit(dep)
    for o in r['objects']:obs.append(pin(o['path'],o['sha256']))
    seen.add(n);active.remove(n)
for n in p['imports']:visit(n)
require(seen==set(modules) and boundary==set(external),'reachable closure')
for r in p['actual_first_artifact_providers']:
    first=next((Path(d)/r['relative'] for d in p['existing_search_path'] if (Path(d)/r['relative']).is_file()),None)
    require(first is not None and str(first)==r['path'],'first provider '+r['relative'])
    obs.append(pin(first,r['sha256']))
run=Path(tempfile.mkdtemp(prefix='validator-seed-gic-images222-author-'));lib=run/'lib';lib.mkdir()
for r in modules.values():
    for o in r['objects']:
        rel=r['module'].replace('.','/')+Path(o['path']).name[len(r['module'].split('.')[-1]):]
        q=lib/rel;q.parent.mkdir(parents=True,exist_ok=True)
        require(not q.exists() and not q.is_symlink(),'existing output');q.symlink_to(o['path'])
i={'status':'AUTHENTICATED_PREPARE_ONLY','plan':pin(PLAN,sha(PLAN)),'plan_manifest':pin(MF,sha(MF)),
 'counts':p['counts'],'modules':p['modules_dependency_order'],'external':p['external'],
 'package_paths':p['existing_search_path'],'compiler':p['compiler'],'toolchain':p['toolchain'],'manifest':p['manifest'],
 'inherited_observations':p['observations'],'observations':obs,'lib':str(lib),'private':str(run),
 'driver':{'path':__file__,'sha256':sha(__file__)},'scope':'215 cached /136 Foundation, zero refresh; two new GIC leaves only.'}
(run/'inputs.json').write_text(json.dumps(i,indent=2)+'\n');shutil.copy2(__file__,run/'prepare.py')
Path('/tmp/seed-gic-images222-current.txt').write_text(str(run)+'\n')
print(json.dumps({'private':str(run),'inputs_sha256':sha(run/'inputs.json'),'observations':len(obs)},indent=2))
