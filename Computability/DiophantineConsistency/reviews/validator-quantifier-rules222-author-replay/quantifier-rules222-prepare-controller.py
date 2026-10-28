import hashlib,json,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
RES=ROOT/'Computability/DiophantineConsistency/research'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,msg):
    if not c:raise RuntimeError(msg)
parents=[(RES/'c222-quantifier-rules222-cache-plan-20261026.json','214674a0f44f8aec74f22ac6fc110862b9767572eaad994c36b487221aed3d1b'),(RES/'c222-quantifier-rules222-proposal-20261026.md','c88a1b0f7995caa16775d60f9a675972beedfba2e646fdde240f79caa8520528')]
for p,h in parents:require(sha(p)==h,'plan/outline pin '+str(p))
audit=json.loads(parents[0][0].read_text())
records={r['module']:r for r in audit['records']};externalmap={r['module']:r for r in audit['external']}
needed=set();external=set()
def visit(n):
    if n in needed or n in external:return
    if n not in records:
        require(n in externalmap,'unknown import '+n);external.add(n);return
    r=records[n]
    require(sha(r['source'])==r['source_sha256'],'source '+n)
    for o in r['objects']:require(sha(o['path'])==o['sha256'],'object '+n)
    raw=re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',Path(r['source']).read_text(),re.M)
    actual=['Init']+[x for line in raw for x in line.split('--',1)[0].split()]
    require(actual==r['imports'],'imports '+n)
    needed.add(n)
    for d in actual:visit(d)
for n in audit['imports']:visit(n)
require(needed==set(records) and len(needed)==159,'selected159')
require(sum(n.startswith('Foundation.') for n in needed)==117,'Foundation117')
require(external==set(externalmap) and len(external)==40,'external40')
require(sum(len(records[n]['objects']) for n in needed)==510,'artifacts510')
for r in audit['parent_records']+audit['source_only_guides']:
    require(sha(r['path'])==r['sha256'],'prior record/guide '+r['path'])
require(sha(audit['compiler']['path'])==audit['compiler']['sha256'],'compiler')
require(sha(ROOT/'lake-manifest.json')==audit['manifest_sha256'],'manifest')
for r in externalmap.values():require(sha(r['path'])==r['sha256'],'external '+r['module'])
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
out=Path(tempfile.mkdtemp(prefix='quantifier-rules222-controller-'));(out/'lib').mkdir();(out/'logs').mkdir()
for n in sorted(needed):
    stem=out/'lib'/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
    for o in records[n]['objects']:
        p=Path(o['path']);suffix=p.name[len(n.rsplit('.',1)[-1]):]
        Path(str(stem)+suffix).symlink_to(p)
inputs={'status':'AUTHENTICATED_BEFORE_EXECUTION','overlay':str(out),
 'snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'compiler':audit['compiler']['path'],'compiler_sha256':audit['compiler']['sha256'],'manifest_sha256':audit['manifest_sha256'],
 'lean_path':str(out/'lib')+':'+audit['package_lean_path'],
 'parent_receipts':[{'path':str(p),'sha256':h} for p,h in parents]+audit['parent_records'],
 'source_only_guides':audit['source_only_guides'],
 'modules':[records[n] for n in sorted(needed)],'external':[externalmap[n] for n in sorted(external)],'fresh_prerequisites':[],
 'scope':'159 current-source cached prerequisites,117 Foundation,510 artifacts,40 explicit external primary boundaries. Accepted root Streams222 and Substitution222 providers. Only two new actual C222 finite quantifier-rule leaves fresh; no dependency build or old CProv254 semantics.'}
(out/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
Path('/tmp/quantifier-rules222-controller-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'custom':159,'foundation':117,'external':40,'artifacts':510,'inputs_sha256':sha(out/'inputs.json'),'free_bytes':shutil.disk_usage('/tmp').free},indent=2))
