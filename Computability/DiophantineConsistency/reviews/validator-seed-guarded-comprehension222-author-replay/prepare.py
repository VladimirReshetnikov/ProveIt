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

plan=D/'reviews/validator-seed-guarded-comprehension222-provider-supplement.json'
proposal=D/'research/validator-seed-guarded-comprehension-plan.md'
require(sha(plan)=='0211217ba2314cab3afb873cd8b458802520f1c0e6baa43d3af7d74ab7b2c920','frozen accepted-provider supplement')
require(sha(proposal)=='4d62d6356b0e4297642da4be82f71f606988ae9e6c7a5caf8207d0f5b1a037ea','proposal')
p=json.loads(plan.read_text())
for r in p['observations']:require(sha(r['path'])==r['sha256'],'supplement observation '+r['path'])
for r in p['modules_dependency_order']:require(set(imports(r['source']))==set(r.get('actual_imports',r['imports'])),'source header '+r['module'])
basepath=D/'reviews/validator-seed-raw-comprehension222-cache.json'
require(sha(basepath)=='4f8bc557fe69b298526859717182a1d6e557fe8d934420fb0ac98e0c66343c24','parent compiler inventory')
base=json.loads(basepath.read_text())
for k in ['compiler','manifest','toolchain']:require(sha(base[k])==base[k+'_sha256'],k)
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
out=Path(tempfile.mkdtemp(prefix='validator-seed-guarded-comprehension222-author-'))
(out/'lib').mkdir();(out/'attempts').mkdir()
for r in p['modules_dependency_order']:
    n=r['module'];stem=out/'lib'/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
    for o in r['objects']:
        src=Path(o['path']);suffix=src.name[len(n.rsplit('.',1)[-1]):]
        Path(str(stem)+suffix).symlink_to(src)
data={k:base[k] for k in ['compiler','compiler_sha256','manifest','manifest_sha256','toolchain','toolchain_sha256']}
data.update(status='AUTHENTICATED_BEFORE_EXECUTION',
 snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 modules=p['modules_dependency_order'],external=p['external'],counts=p['counts'],
 parent_receipts=[{'path':str(plan),'sha256':sha(plan)},{'path':str(proposal),'sha256':sha(proposal)},
 {'path':str(basepath),'sha256':sha(basepath)},p['root_receipt'],p['root_packet'],p['root_manifest']],
 inherited_observations=p['observations'],overlay=str(out),
 lean_path=':'.join([str(out/'lib')]+p['existing_search_path'][2:]),
 scope='202 cached current-source modules,136 Foundation,610 object artifacts,45 explicit boundaries. No dependency/Foundation build. Only two new leaves.',
 driver={'path':__file__,'sha256':sha(__file__)})
# Confirm the overlay, rather than an inherited cache directory, supplies every custom module.
for r in data['modules']:
    actual=out/'lib'/(r['module'].replace('.','/')+'.olean')
    expected=next(o for o in r['objects'] if o['path'].endswith('.olean'))
    require(sha(actual)==expected['sha256'],'overlay primary '+r['module'])
(out/'inputs.json').write_text(json.dumps(data,indent=2)+'\n')
cache=D/'reviews/validator-seed-guarded-comprehension222-cache.json';require(not cache.exists(),'new cache inventory path')
cache.write_bytes((out/'inputs.json').read_bytes())
Path('/tmp/validator-seed-guarded-comprehension222-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'cache':str(cache),'sha256':sha(cache)},indent=2))
