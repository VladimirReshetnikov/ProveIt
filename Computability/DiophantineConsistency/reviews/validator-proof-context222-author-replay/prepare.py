import hashlib, json, re, shutil, subprocess, tempfile
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
REV = ROOT/'Computability/DiophantineConsistency/reviews'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c, msg):
    if not c: raise RuntimeError(msg)
def imports(p):
    s=Path(p).read_text();s=re.sub(r'/\-.*?\-/', '', s, flags=re.S)
    return ['Init']+re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)', s, re.M)

parent=REV/'validator-formula-encoder222-replay.json'
rootrec=REV/'validator-formula-encoder222-root-replay/ROOT.json'
base=json.loads(parent.read_text())['inputs'];root=json.loads(rootrec.read_text())
for n,h in root['files'].items():
    require(sha(rootrec.parent/n)==h, 'root bundle '+n)
records={r['module']:dict(r) for r in base['modules']}
for r in root['state']['completed']:
    require(r['exit_code']==0, 'accepted root execution')
    n=r['module']
    records[n]={'module':n,'source':r['source'],'source_sha256':r['source_sha256'],
      'objects':[{'path':r['object'],'sha256':r['object_sha256']}],
      'provenance':'accepted independent root fresh encoder replay',
      'root_record':{'path':str(rootrec),'sha256':sha(rootrec)},
      'imports':imports(r['source'])}
external={r['module']:r for r in base['external']}
needed=[];boundary=set();seen=set()
def visit(n):
    if n in seen:return
    seen.add(n)
    if n not in records:
        require(n in external, 'unrecorded import '+n);boundary.add(n);return
    r=records[n];require(sha(r['source'])==r['source_sha256'], 'source '+n)
    actual=imports(r['source'])
    require(set(actual)==set(r['imports']), 'import drift '+n)
    for m in actual:visit(m)
    for o in r['objects']:require(sha(o['path'])==o['sha256'],'artifact '+o['path'])
    needed.append(r)
visit('ZFCinPA.ValidatorFormulaEncoder222')
for n in boundary:require(sha(external[n]['path'])==external[n]['sha256'],'boundary '+n)
require(sha(base['compiler'])==base['compiler_sha256'],'compiler')
require(sha(ROOT/'lake-manifest.json')==base['manifest_sha256'],'manifest')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
out=Path(tempfile.mkdtemp(prefix='validator-proof-context222-author-'));(out/'lib').mkdir();(out/'attempts').mkdir()
for r in needed:
    n=r['module'];stem=out/'lib'/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
    for o in r['objects']:
        p=Path(o['path']);suffix=p.name[len(n.rsplit('.',1)[-1]):]
        Path(str(stem)+suffix).symlink_to(p)
inventory={'status':'AUTHENTICATED_BEFORE_EXECUTION','scope':'Minimal current encoder-only closure, accepted source/object records reused; no dependency or Foundation build.',
 'snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'compiler':base['compiler'],'compiler_sha256':base['compiler_sha256'],
 'manifest':str(ROOT/'lake-manifest.json'),'manifest_sha256':base['manifest_sha256'],
 'toolchain':str(ROOT/'lean-toolchain'),'toolchain_sha256':sha(ROOT/'lean-toolchain'),
 'parent_receipts':[{'path':str(p),'sha256':sha(p)} for p in [parent,rootrec,rootrec.parent/'packet.json']],
 'modules':needed,'external':[external[n] for n in sorted(boundary)],
 'lean_path':str(out/'lib')+':'+base['lean_path'].split(':',1)[1],'overlay':str(out),
 'counts':{'cached':len(needed),'foundation':sum(r['module'].startswith('Foundation.') for r in needed),
 'artifacts':sum(len(r['objects']) for r in needed),'boundaries':len(boundary)},
 'excluded_parent_modules':sorted(set(records)-{r['module'] for r in needed}),
 'driver':{'path':__file__,'sha256':sha(__file__)}}
(out/'inputs.json').write_text(json.dumps(inventory,indent=2)+'\n')
p=REV/'validator-proof-context222-cache.json';require(not p.exists(),'freeze path exists')
p.write_bytes((out/'inputs.json').read_bytes())
Path('/tmp/validator-proof-context222-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'cache':str(p),'sha256':sha(p),'counts':inventory['counts'],'excluded':inventory['excluded_parent_modules']},indent=2))
