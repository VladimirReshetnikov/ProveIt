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

plan=D/'research/validator-seed-tagged-interpretation-plan.json'
proposal=D/'research/validator-seed-tagged-interpretation-plan.md'
require(sha(plan)=='f139d86765d1827c6dfb938065ae4e705e96387840dc5fabae7221d065326f46','frozen plan')
require(sha(proposal)=='6bd9bc2a292d1892b5bd07db6f5acb9822872629175bca40240424420a11b35b','proposal')
p=json.loads(plan.read_text())
for r in p['observations']:require(sha(r['path'])==r['sha256'],'planning observation '+r['path'])
for r in p['branches']['recommended_seed_open_basis']['modules_dependency_order']:require(set(imports(r['source']))==set(r.get('actual_imports',r['imports'])),'source header '+r['module'])
base=json.loads((D/'reviews/validator-full-seed-theory222-cache.json').read_text())
for k in ['compiler','manifest','toolchain']:require(sha(base[k])==base[k+'_sha256'],k)
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
out=Path(tempfile.mkdtemp(prefix='validator-seed-source-basis222-author-'))
(out/'lib').mkdir();(out/'attempts').mkdir()
for r in p['branches']['recommended_seed_open_basis']['modules_dependency_order']:
    n=r['module'];stem=out/'lib'/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
    for o in r['objects']:
        src=Path(o['path']);suffix=src.name[len(n.rsplit('.',1)[-1]):]
        Path(str(stem)+suffix).symlink_to(src)
data={k:base[k] for k in ['compiler','compiler_sha256','manifest','manifest_sha256','toolchain','toolchain_sha256']}
data.update(status='AUTHENTICATED_BEFORE_EXECUTION',
 snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 modules=p['branches']['recommended_seed_open_basis']['modules_dependency_order'],external=p['branches']['recommended_seed_open_basis']['external'],counts=p['branches']['recommended_seed_open_basis']['counts'],
 parent_receipts=[{'path':str(plan),'sha256':sha(plan)},{'path':str(proposal),'sha256':sha(proposal)},
 {'path':str(D/'reviews/validator-full-seed-theory222-root.md'),'sha256':sha(D/'reviews/validator-full-seed-theory222-root.md')}],
 inherited_observations=p['observations'],overlay=str(out),
 lean_path=str(out/'lib')+':'+base['lean_path'].split(':',1)[1],
 scope='200 cached current-source modules,136 Foundation,608 object artifacts,45 explicit boundaries. No dependency/Foundation build. Only two new leaves.',
 driver={'path':__file__,'sha256':sha(__file__)})
(out/'inputs.json').write_text(json.dumps(data,indent=2)+'\n')
cache=D/'reviews/validator-seed-source-basis222-cache.json';require(not cache.exists(),'new cache inventory path')
cache.write_bytes((out/'inputs.json').read_bytes())
Path('/tmp/validator-seed-source-basis222-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'cache':str(cache),'sha256':sha(cache)},indent=2))
