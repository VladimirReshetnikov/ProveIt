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

plan=D/'research/validator-source-derivation222-plan.json'
proposal=D/'research/validator-source-derivation222-plan.md'
require(sha(plan)=='9dc83e9ab42279fd86c004c171609a54c228703f922fafe458bba33f177f66ba','frozen plan')
require(sha(proposal)=='899e787fce0ab61e906daa4bc71cde4ab360a19f8f586f2c9e144d180838f8b3','proposal')
p=json.loads(plan.read_text())
for r in p['observations']:require(sha(r['path'])==r['sha256'],'planning observation '+r['path'])
for r in p['modules']:require(imports(r['source'])==r['imports'],'source header '+r['module'])
base=json.loads((D/'reviews/validator-source-negation222-replay.json').read_text())['inputs']
for k in ['compiler','manifest','toolchain']:require(sha(base[k])==base[k+'_sha256'],k)
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
out=Path(tempfile.mkdtemp(prefix='validator-source-derivation222-author-'))
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
 scope='164 cached current-source modules,117 Foundation,515 object artifacts,40 explicit boundaries. No dependency/Foundation build. Only two new leaves.',
 driver={'path':__file__,'sha256':sha(__file__)})
(out/'inputs.json').write_text(json.dumps(data,indent=2)+'\n')
cache=D/'reviews/validator-source-derivation222-cache.json';require(not cache.exists(),'new cache inventory path')
cache.write_bytes((out/'inputs.json').read_bytes())
Path('/tmp/validator-source-derivation222-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'cache':str(cache),'sha256':sha(cache)},indent=2))
