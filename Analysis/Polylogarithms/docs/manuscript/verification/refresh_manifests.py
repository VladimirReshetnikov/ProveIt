"""Pin a reviewed release; refuse to refresh changed immutable evidence.

Run only after mathematical replay, final source audit and PDF review. This
records digests; verify_receipts.py checks outcomes and artifact agreement.
"""
from pathlib import Path
import hashlib, json, subprocess

B=Path(__file__).resolve().parents[1]
V=B/'verification'
def digest(p,mode):
    data=p.read_bytes()
    if mode=='lf-normalized':data=data.replace(b'\r\n',b'\n')
    return hashlib.sha256(data).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8'))
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')

previous=read(V/'dependency-sha256.json')
for name,entry in previous.items():
    if name.startswith('../'):
        assert digest(B/name,entry['mode'])==entry['sha256'],name+' changed immutable input'
archives=sum((read(V/name) for name in ['incoming-archives.json',
    'research-incoming-archives.json','third-incoming-archives.json',
    'fourth-incoming-archives.json','fifth-incoming-archives.json',
    'sixth-incoming-archives.json','seventh-incoming-archives.json',
    'eighth-incoming-archives.json','ninth-incoming-archives.json','tenth-incoming-archives.json','eleventh-incoming-archives.json','twelfth-incoming-archives.json']), [])
for a in archives:
    archive=B.parents[3]/a['archive']
    blob=archive.read_bytes() if archive.is_file() else subprocess.check_output(['git','show',a['archive_git_revision']+':'+a['archive']],cwd=B.parents[3])
    assert hashlib.sha256(blob).hexdigest()==a['archive_sha256'],a['archive']
    for f in a['files']:
        assert digest(B.parent/f['path'],'raw')==f['sha256'],f['path']

sources=[*sorted(B.glob('*.tex')),*sorted((B/'volumes').rglob('*.tex')),*sorted((B/'chapters').glob('*.tex')),
         *sorted(V.glob('*.py')),*sorted(V.glob('*.wls'))]
save(V/'source-sha256.json',{p.relative_to(B).as_posix():digest(p,'lf-normalized') for p in sources})
dependencies={}
for name,entry in previous.items():
    dependencies[name]={'sha256':digest(B/name,entry['mode']),'mode':entry['mode']}
# Pin upstream's flattened placement copies as well as their full packages.
for folder in ['gaussian-parity-reductions','rational-grid-distribution-ranks']:
    for p in sorted((B.parent/'reports'/folder).rglob('*')):
        if not p.is_file() or not p.name.startswith(('20-','21-','22-','23-','24-')):continue
        name='../'+p.relative_to(B.parent).as_posix()
        mode='lf-normalized' if p.suffix in {'.py','.tex','.md','.txt','.json','.wls','.patch'} else 'raw'
        dependencies[name]={'sha256':digest(p,mode),'mode':mode}
# Every newly delivered member is pinned raw, including its original PDFs,
# code, exact certificates and correction registers. It is never regenerated.
for a in archives:
    for f in a['files']:
        dependencies['../'+f['path']]={'sha256':f['sha256'],'mode':'raw'}
for p in sorted((B/'figures').rglob('*')):
    if p.is_file():dependencies[p.relative_to(B).as_posix()]={'sha256':digest(p,'raw'),'mode':'raw'}
excluded={'source-sha256.json','dependency-sha256.json','receipt-integrity.json'}
for p in sorted(V.rglob('*')):
    if not p.is_file() or any(s.startswith('.scratch') or s=='__pycache__' for s in p.parts):continue
    if p.name in excluded or p.suffix not in {'.json','.tex'}:continue
    dependencies[p.relative_to(B).as_posix()]={'sha256':digest(p,'lf-normalized'),'mode':'lf-normalized'}
save(V/'dependency-sha256.json',dict(sorted(dependencies.items())))
print('Pinned',len(sources),'canonical sources and',len(dependencies),'dependencies.')
