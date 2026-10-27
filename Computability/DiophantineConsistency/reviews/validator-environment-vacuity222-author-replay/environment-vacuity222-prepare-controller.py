import hashlib,json,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');REV=ROOT/'Computability/DiophantineConsistency/reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,msg):
    if not c:raise RuntimeError(msg)
parents=[(REV/'validator-formula-encoder222-replay.json','70bffc0bf179043259301bb8f006109ddce2e160af393fb427649622a624679d'),
 (Path('/tmp/validator-formula-encoder222-root-peer-c0wplw6c/state.json'),'57ba6480ddc064449491341429625fff5a803957f907f566f9e666b8e5244640'),
 (Path('/tmp/validator-formula-encoder222-root-peer-c0wplw6c/pins.json'),'8a6b76fcc253ee87c608e838d352aa632e7afb9360477cb1e717a10cfb4ef906'),
 (REV/'validator-seed-image222-replay.json','d79bf3855cd650c5d4df1a80ce4460ad3c513f774038c92efad3ca1a32bec0a7')]
for p,h in parents:require(sha(p)==h,'parent pin '+str(p))
old=json.loads(parents[0][0].read_text());base=old['inputs'];peer=json.loads(parents[1][0].read_text())
require(peer['status']=='PASS','accepted peer status')
records={r['module']:r.copy() for r in base['modules']};authors={r['module']:r for r in old['final_leaves']}
for r in peer['completed']:
    require(r['exit_code']==0 and r['matches_author'],'peer leaf success')
    a=authors[r['module']]
    require(r['source_sha256']==a['source_sha256'] and r['object_sha256']==a['object']['sha256'],'source/primary identity')
    require(sha(r['source'])==r['source_sha256'] and sha(r['object'])==r['object_sha256'],'current peer pair')
    require(sha(r['log'])==r['log_sha256'],'peer log')
    records[r['module']]={'module':r['module'],'source':r['source'],'source_sha256':r['source_sha256'],
      'objects':[{'path':r['object'],'sha256':r['object_sha256']}],
      'provenance':'accepted fresh root replay, byte-identical to accepted author fresh object','root_execution':r,'action':'authenticated reuse'}
needed=set();external=set();externalmap={r['module']:r for r in base['external']}
# The earlier source-plan parser omitted public meta import Aesop. Its
# exact provider is already pinned in the accepted SeedImage cache.
seed=json.loads(parents[3][0].read_text())
externalmap['Aesop']=next(r for r in seed['inputs']['external'] if r['module']=='Aesop')
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
visit('ZFCinPA.ValidatorFormulaEncoder222')
require(len(needed)==152,'expected selected152')
require(sum(n.startswith('Foundation.') for n in needed)==117,'expected117 Foundation')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
require(sha(base['compiler'])==base['compiler_sha256'],'compiler')
require(sha(ROOT/'lake-manifest.json')==base['manifest_sha256'],'manifest')
out=Path(tempfile.mkdtemp(prefix='environment-vacuity222-controller-'));(out/'lib').mkdir();(out/'logs').mkdir()
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
 'scope':'152 authenticated current-source prerequisites reused; the three syntax clients and Encoder222 use accepted fresh root objects. Existing117 Foundation providers retain the prior20-trace/2-historical added-subset distinction. Only new actual C222 IΣ2 uniform-vacuity leaves fresh, no Foundation rebuild.'}
(out/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n');Path('/tmp/environment-vacuity222-controller-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'custom':len(needed),'foundation':117,'external_including_Init':len(ext),'inputs_sha256':sha(out/'inputs.json')},indent=2))
