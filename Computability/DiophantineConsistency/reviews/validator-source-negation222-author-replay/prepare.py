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
    return out
plan=D/'research/validator-source-negation222-plan.json'
require(sha(plan)=='418971e7da7efeec1e02402bf692b14e975bfa1826ccce3675bc722692ded5f9','frozen plan pins')
p=json.loads(plan.read_text())
require(sha(p['plan']['path'])==p['plan']['sha256'],'proposal')
require(sha(p['parent_inventory']['path'])==p['parent_inventory']['sha256'],'parent inventory')
require(sha(p['aesop_boundary_provider']['path'])==p['aesop_boundary_provider']['sha256'],'accepted Aesop provider')
for o in p['observations']:require(sha(o['path'])==o['sha256'],'read-only source/object pin')
base=json.loads(Path(p['parent_inventory']['path']).read_text())
for r in p['modules']:require(set(imports(r['source']))==set(r['imports']),'current full import header '+r['module'])
for k in ['compiler','manifest','toolchain']:require(sha(base[k])==base[k+'_sha256'],k)
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
out=Path(tempfile.mkdtemp(prefix='validator-source-negation222-author-'));(out/'lib').mkdir();(out/'attempts').mkdir()
for r in p['modules']:
    n=r['module'];stem=out/'lib'/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
    for o in r['objects']:
        src=Path(o['path']);suffix=src.name[len(n.rsplit('.',1)[-1]):]
        Path(str(stem)+suffix).symlink_to(src)
data={k:base[k] for k in ['compiler','compiler_sha256','manifest','manifest_sha256','toolchain','toolchain_sha256']}
data.update(status='AUTHENTICATED_BEFORE_EXECUTION',
 snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 modules=p['modules'],external=p['external'],counts={k:v for k,v in p['counts'].items() if k!='fresh_if_approved'},
 parent_receipts=[{'path':str(plan),'sha256':sha(plan)},p['plan'],p['parent_inventory'],p['aesop_boundary_provider']],
 header_metadata_corrections=p['header_metadata_corrections'],inherited_observations=p['observations'],
 overlay=str(out),lean_path=str(out/'lib')+':'+base['lean_path'].split(':',1)[1],
 scope='152 current-source cached modules,117 Foundation,503 artifacts,40 explicit boundaries including meta-import Aesop. No dependency or Foundation build.',
 driver={'path':__file__,'sha256':sha(__file__)})
(out/'inputs.json').write_text(json.dumps(data,indent=2)+'\n')
cache=D/'reviews/validator-source-negation222-cache.json';require(not cache.exists(),'freeze path exists')
cache.write_bytes((out/'inputs.json').read_bytes())
Path('/tmp/validator-source-negation222-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'cache':str(cache),'sha256':sha(cache),'counts':data['counts']},indent=2))
