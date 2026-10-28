import hashlib,json,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
    if not c:raise RuntimeError(m)
def imports(p):
    s=re.sub(r'/\-.*?\-/','',Path(p).read_text(),flags=re.S)
    out=[] if re.search(r'^\s*prelude\s*$',s,re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M):
        out.extend(re.findall(r'[\w.]+',line.split('--',1)[0]))
    return list(dict.fromkeys(out))
plan=D/'research/validator-source-quantifier-context222-plan.json'
proposal=D/'research/validator-source-quantifier-context222-plan.md'
require(sha(plan)=='9dad1db62489fb5622829b826e26fccef1ace2315974200fe32878d7606b63f9','frozen plan')
require(sha(proposal)=='0336d92a63d6c3e017df476d0ca6abf6a73a2bcda4f9556cb269a82265117173','proposal')
p=json.loads(plan.read_text())
for r in p['observations']:require(sha(r['path'])==r['sha256'],'planning observation '+r['path'])
for r in p['modules']:require(imports(r['source'])==r['imports'],'source header '+r['module'])
base=json.loads((D/'reviews/validator-source-negation222-replay.json').read_text())['inputs']
for k in ['compiler','manifest','toolchain']:require(sha(base[k])==base[k+'_sha256'],k)
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
out=Path(tempfile.mkdtemp(prefix='validator-source-quantifier-context222-author-'))
(out/'lib').mkdir();(out/'attempts').mkdir()
for r in p['modules']:
    n=r['module'];stem=out/'lib'/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
    for o in r['objects']:
        src=Path(o['path']);suffix=src.name[len(n.rsplit('.',1)[-1]):]
        Path(str(stem)+suffix).symlink_to(src)
data={k:base[k] for k in ['compiler','compiler_sha256','manifest','manifest_sha256','toolchain','toolchain_sha256']}
data.update(status='AUTHENTICATED_BEFORE_EXECUTION',
 snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 modules=p['modules'],external=p['external'],counts=p['counts'],
 parent_receipts=[{'path':str(plan),'sha256':sha(plan)},{'path':str(proposal),'sha256':sha(proposal)}]+p['parents'],
 inherited_observations=p['observations'],overlay=str(out),
 lean_path=str(out/'lib')+':'+base['lean_path'].split(':',1)[1],
 scope='162 cached current-source modules,117 Foundation,513 object artifacts,40 explicit boundaries. No dependency/Foundation build. Only two new leaves.',
 driver={'path':__file__,'sha256':sha(__file__)})
(out/'inputs.json').write_text(json.dumps(data,indent=2)+'\n')
cache=D/'reviews/validator-source-quantifier-context222-cache.json';require(not cache.exists(),'new cache inventory path')
cache.write_bytes((out/'inputs.json').read_bytes())
Path('/tmp/validator-source-quantifier-context222-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'cache':str(cache),'sha256':sha(cache)},indent=2))
