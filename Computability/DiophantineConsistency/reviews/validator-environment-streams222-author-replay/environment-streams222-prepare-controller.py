import hashlib,json,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
REV=ROOT/'Computability/DiophantineConsistency/reviews'
RES=ROOT/'Computability/DiophantineConsistency/research'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,msg):
    if not c:raise RuntimeError(msg)
parents=[(RES/'c222-substitution-opening-cache-plan-20261026.json','16d3cbc7ac69f4386b9dd02cba242c98de51e79a6d0fc6cff4d029e7b9bb0c19'),
 (RES/'c222-streams222-proposal-20261026.md','74c9667f235a98bb9bd8d20f23e47cd53b7b30b00e9b012e24f35db19a2600ec'),
 (REV/'validator-environment-alpha222-replay.json','333cd5571624fd3a269d2e4d82f6cf60f827dc4b2669e3a570e33041fd8c0c41')]
for p,h in parents:require(sha(p)==h,'parent pin '+str(p))
audit=json.loads(parents[0][0].read_text());base=json.loads(parents[2][0].read_text())['inputs']
plan=audit['plans']['streams'];records={r['module']:r for r in audit['records']}
externalmap={r['module']:r for r in audit['external']};needed=set();external=set()
def visit(n):
    if n in needed or n in external:return
    if n not in records:
        require(n in externalmap,'unknown import '+n);external.add(n);return
    r=records[n]
    require(sha(r['source'])==r['source_sha256'],'source '+n)
    for o in r['objects']:require(sha(o['path'])==o['sha256'],'object '+n)
    raw=re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',Path(r['source']).read_text(),re.M)
    actual=['Init']+[n for line in raw for n in line.split('--',1)[0].split()]
    require(actual==r['imports'],'imports '+n)
    needed.add(n)
    for d in actual:visit(d)
for n in plan['proposed_imports']:visit(n)
require(needed==set(plan['modules']) and len(needed)==156,'selected156')
require(sum(n.startswith('Foundation.') for n in needed)==117,'Foundation117')
require(external==set(plan['external_names']) and len(external)==40,'external40')
require(sum(len(records[n]['objects']) for n in needed)==507,'artifact507')
for p in audit['parents']:require(sha(p['path'])==p['sha256'],'prior parent')
require(sha(base['compiler'])==base['compiler_sha256'],'compiler')
require(sha(ROOT/'lake-manifest.json')==base['manifest_sha256'],'manifest')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
out=Path(tempfile.mkdtemp(prefix='environment-streams222-controller-'))
(out/'lib').mkdir();(out/'logs').mkdir()
for n in sorted(needed):
    stem=out/'lib'/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
    for o in records[n]['objects']:
        p=Path(o['path']);suffix=p.name[len(n.rsplit('.',1)[-1]):]
        Path(str(stem)+suffix).symlink_to(p)
ext=[externalmap[n] for n in sorted(external)]
for r in ext:require(sha(r['path'])==r['sha256'],'external '+r['module'])
inputs={'status':'AUTHENTICATED_BEFORE_EXECUTION','overlay':str(out),
 'snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'compiler':base['compiler'],'compiler_sha256':base['compiler_sha256'],'manifest_sha256':base['manifest_sha256'],
 'lean_path':str(out/'lib')+':'+base['lean_path'].split(':',1)[1],
 'parent_receipts':[{'path':str(p),'sha256':h} for p,h in parents],
 'modules':[records[n] for n in sorted(needed)],'external':ext,'fresh_prerequisites':[],
 'scope':'156 current-source cached prerequisites,117 Foundation,507 artifacts,40 explicit external primary boundaries. Reuse accepted root Alpha222 provider. Only two new actual C222 Streams222 leaves fresh; no dependency rebuild or old CProv254 semantics.'}
(out/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
Path('/tmp/environment-streams222-controller-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'custom':len(needed),'foundation':117,'external':len(ext),'artifacts':507,'inputs_sha256':sha(out/'inputs.json'),'free_bytes':shutil.disk_usage('/tmp').free},indent=2))
