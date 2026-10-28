import hashlib,json,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');REV=ROOT/'Computability/DiophantineConsistency/reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,msg):
    if not c:raise RuntimeError(msg)
parents=[(REV/'validator-eind-context222-replay.json','a26fc0465cbeda971ffa8fcdda19fbb1b61168ee3681e406815b15416f78fa19'),
 (REV/'validator-eind-context222-root-replay/ROOT.json','b3edf1c7915e66d33e4cc9eb973afe4c284d7f6b60d42d3d976d1188a0b84061'),
 (ROOT/'Computability/DiophantineConsistency/research/c222-uniform-alpha-proposal-20261026.md','24ad6ab111843daa5d34a3f6c4cff52956cfc18552ec8b3ebacc8e02e32f13c6')]
for p,h in parents:require(sha(p)==h,'parent pin '+str(p))
old=json.loads(parents[0][0].read_text());base=old['inputs'];peer=json.loads(parents[1][0].read_text())['state']
require(peer['status']=='PASS','accepted peer status')
records={r['module']:r.copy() for r in base['modules']};authors={r['module']:r for r in old['final_leaves']}
for r in peer['completed']:
    if r['module'].endswith('Checks'):continue
    require(r['exit_code']==0 and r['matches_author'],'peer leaf success')
    a=authors[r['module']]
    require(r['source_sha256']==a['source_sha256'] and r['object_sha256']==a['object']['sha256'],'source/primary identity')
    require(sha(r['source'])==r['source_sha256'] and sha(r['object'])==r['object_sha256'],'current peer pair')
    require(sha(r['log'])==r['log_sha256'],'peer log')
    records[r['module']]={'module':r['module'],'source':r['source'],'source_sha256':r['source_sha256'],
      'objects':[{'path':r['object'],'sha256':r['object_sha256']}],
      'provenance':'accepted fresh root replay, byte-identical to accepted author fresh object','root_execution':r,'action':'authenticated reuse'}
needed=set();external=set();externalmap={r['module']:r for r in base['external']}
def visit(n):
    if n in needed or n in external:return
    if n not in records:
        require(n in externalmap,'unknown import '+n);external.add(n);return
    r=records[n]
    require(sha(r['source'])==r['source_sha256'],'source '+n)
    for o in r['objects']:require(sha(o['path'])==o['sha256'],'object '+n)
    raw=re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',Path(r['source']).read_text(),re.M)
    r['imports']=['Init']+[n for line in raw for n in line.split('--',1)[0].split()]
    needed.add(n)
    for dep in r['imports']:visit(dep)
visit('ZFCinPA.ValidatorEindContext222')
require(len(needed)==154,'expected selected154')
require(sum(n.startswith('Foundation.') for n in needed)==117,'expected117 Foundation')
require(len(external)==40,'expected40 external boundaries')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
require(sha(base['compiler'])==base['compiler_sha256'],'compiler')
require(sha(ROOT/'lake-manifest.json')==base['manifest_sha256'],'manifest')
out=Path(tempfile.mkdtemp(prefix='atomic-transport222-controller-'));(out/'lib').mkdir();(out/'logs').mkdir()
for n in sorted(needed):
    stem=out/'lib'/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
    for o in records[n]['objects']:
        p=Path(o['path']);suffix=p.name[len(n.rsplit('.',1)[-1]):];Path(str(stem)+suffix).symlink_to(p)
ext=[externalmap[n] for n in sorted(external)]
for r in ext:require(sha(r['path'])==r['sha256'],'external '+r['module'])
inputs={'status':'AUTHENTICATED_BEFORE_EXECUTION','overlay':str(out),
 'snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'compiler':base['compiler'],'compiler_sha256':base['compiler_sha256'],'manifest_sha256':base['manifest_sha256'],
 'lean_path':str(out/'lib')+':'+base['lean_path'].split(':',1)[1],
 'parent_receipts':[{'path':str(p),'sha256':h} for p,h in parents],
 'modules':[records[n] for n in sorted(needed)],'external':ext,'fresh_prerequisites':[],
 'scope':'154 authenticated current-source prerequisites reused, including accepted fresh root EindContext222. Existing117 Foundation providers retain the prior20-trace/2-historical added-subset distinction. Only new actual C222 finite atomic-transport leaves fresh; no Foundation rebuild or uniform-alpha theorem.'}
(out/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n');Path('/tmp/atomic-transport222-controller-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'custom':len(needed),'foundation':117,'external_including_Init':len(ext),'artifact_records':sum(len(records[n]['objects']) for n in needed),'inputs_sha256':sha(out/'inputs.json')},indent=2))
