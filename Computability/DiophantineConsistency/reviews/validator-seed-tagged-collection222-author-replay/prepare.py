import hashlib,json,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
    if not c:raise RuntimeError(m)
def strip_comments(text):
    # Preserve newlines; nested Lean block comments and line comments are both
    # ignored before reading the import header. These sources have no imports
    # inside multiline strings before the first declaration.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            out.extend('  ')
            i += 2
        elif not depth and text.startswith('--', i):
            j = text.find('\n', i)
            j = len(text) if j == -1 else j
            out.extend(' ' * (j - i))
            i = j
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    if depth:
        raise RuntimeError('unclosed Lean block comment')
    return ''.join(out)


def imports(path):
    text = strip_comments(Path(path).read_text())
    result = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        result.extend(re.findall(r'[\w.]+', line))
    return list(dict.fromkeys(result))

plan=D/'research/validator-seed-tagged-collection-cache-plan.json'
proposal=D/'research/validator-seed-tagged-collection-plan.md'
require(sha(plan)=='94c923959cc8870c08f452e26d330c68b8bea7f43961595498e5eb355cdde911','frozen plan')
require(sha(proposal)=='f16a12c1af42b0c68a6e8cee005557e74d9194119a0519f5ae6306ff9046b280','proposal')
p=json.loads(plan.read_text())
for r in p['observations']:require(sha(r['path'])==r['sha256'],'inherited observation '+r['path'])
for r in p['modules_dependency_order']:require(set(imports(r['source']))==set(r.get('actual_imports',r['imports'])),'source header '+r['module'])
for k in ['compiler','manifest','toolchain']:require(sha(p[k]['path'])==p[k]['sha256'],k)
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
out=Path(tempfile.mkdtemp(prefix='validator-seed-tagged-collection222-author-'))
(out/'lib').mkdir();(out/'attempts').mkdir()
for r in p['modules_dependency_order']:
    n=r['module'];stem=out/'lib'/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
    for o in r['objects']:
        src=Path(o['path']);suffix=src.name[len(n.rsplit('.',1)[-1]):]
        Path(str(stem)+suffix).symlink_to(src)
data={}
for k in ['compiler','manifest','toolchain']:
    data[k]=p[k]['path'];data[k+'_sha256']=p[k]['sha256']
data.update(status='AUTHENTICATED_BEFORE_EXECUTION',
 snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 modules=p['modules_dependency_order'],external=p['external'],counts=p['counts'],
 parent_receipts=[{'path':str(plan),'sha256':sha(plan)},{'path':str(proposal),'sha256':sha(proposal)}]+p['parents'],
 inherited_observations=p['observations'],overlay=str(out),
 lean_path=':'.join([str(out/'lib')]+p['existing_search_path'][2:]),
 scope='207 cached current-source modules,136 Foundation,615 object artifacts,45 explicit boundaries. No dependency/Foundation build. Only two new leaves.',
 driver={'path':__file__,'sha256':sha(__file__)})
for r in data['modules']:
    actual=out/'lib'/(r['module'].replace('.','/')+'.olean')
    expected=next(o for o in r['objects'] if o['path'].endswith('.olean'))
    require(sha(actual)==expected['sha256'],'overlay primary '+r['module'])
# Check every selected compiler artifact's actual first provider, not just primary objects.
for r in p['actual_first_artifact_providers']:
    candidates=[Path(q)/r['relative'] for q in data['lean_path'].split(':')]
    got=next((q for q in candidates if q.is_file()),None)
    require(got is not None and sha(got)==r['sha256'],'first artifact '+str(r))
(out/'inputs.json').write_text(json.dumps(data,indent=2)+'\n')
cache=D/'reviews/validator-seed-tagged-collection222-cache.json';require(not cache.exists(),'new cache inventory path')
cache.write_bytes((out/'inputs.json').read_bytes())
Path('/tmp/validator-seed-tagged-collection222-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'cache':str(cache),'sha256':sha(cache)},indent=2))
