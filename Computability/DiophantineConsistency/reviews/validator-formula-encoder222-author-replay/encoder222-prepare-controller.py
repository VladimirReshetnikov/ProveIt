import hashlib, json, re, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
REV = ROOT/'Computability/DiophantineConsistency/reviews'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,msg):
    if not c: raise RuntimeError(msg)
parents = [
 (REV/'validator-seed-image222-replay.json','d79bf3855cd650c5d4df1a80ce4460ad3c513f774038c92efad3ca1a32bec0a7'),
 (REV/'fixed-consistency-nat-cache-audit/encoder222-foundation22-auth.json','6279f7df8780b39d1b25701df2ddee960cdca8cc1e8950fa51d7fb0d7405094d'),
 (Path('/tmp/c222-encoder-plan-20261026.json'),'d7a62b321a90031a9b730dbcd9f12b7a9938d1d6f82a448011dff6e67a1ff94e')]
for p,h in parents: require(sha(p)==h,'parent receipt '+str(p))
old=json.loads(parents[0][0].read_text());base=old['inputs']
new=json.loads(parents[1][0].read_text());plan=json.loads(parents[2][0].read_text())
records={r['module']:r.copy() for r in base['modules']}
for r in new['trace_modules']:
    require(sha(r['trace'])==r['trace_sha256'],'trace '+r['module'])
    files=r['files'];src=next(f for f in files if f['path'].endswith('.lean'))
    for f in files: require(sha(f['path'])==f['sha256'],'trace artifact '+f['path'])
    records[r['module']]={'module':r['module'],'source':src['path'],'source_sha256':src['sha256'],
      'objects':[{'path':f['path'],'sha256':f['sha256']} for f in files if not f['path'].endswith('.lean')],
      'provenance':'current source and four artifacts authenticated by exact Lean4.32 Lake trace','trace':r}
for r in new['private_modules']:
    for tag in ['record','snapshot','later_companion_record']:
        require(sha(r[tag]['path'])==r[tag]['sha256'],'historical record '+tag)
    require(sha(r['compiler']['path'])==r['compiler']['sha256'],'historical compiler')
    require(r['source_command']['exit_code']==0,'historical source execution')
    records[r['module']]={'module':r['module'],'source':r['source'],'source_sha256':r['source_sha256'],
      'objects':r['objects'],'provenance':r['artifact_provenance_scope'],'historical':r}
providers=json.loads(Path('/tmp/zfc-r2-provider-inventory/inventory.json').read_text())['selected_candidate_pairs']
refresh=['ZFCinPA.Instances','ZFCinPA.ValidatorFormulaEncoder254','ZFCinPA.ValidatorEnvironmentLabels254']
for n in refresh:
    r=providers[n]
    require(sha(r['record']['path'])==r['record']['sha256'],'historical syntax record '+n)
    require(sha(r['source'])==r['source_sha256'],'historical syntax snapshot '+n)
    require(sha(r['object'])==r['object_sha256'],'historical syntax object '+n)
    require(sha(r['record_compiler']['path'])==r['record_compiler']['sha256'],'historical syntax compiler')
    records[n]={'module':n,'source':str(ROOT/'Logic/Interpretability/ZFCinPA/Lean'/(n.replace('.','/')+'.lean')),
      'source_sha256':r['source_sha256'],'objects':[{'path':r['object'],'sha256':r['object_sha256']}],
      'provenance':'historical pair authenticated for comparison; omitted from overlay and freshly rebuilt before use',
      'historical':r,'action':'fresh prerequisite'}
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
require(sha(base['compiler'])==base['compiler_sha256'],'compiler')
require(sha(ROOT/'lake-manifest.json')==base['manifest_sha256'],'manifest')
needed=[]
for p in plan['modules']:
    n=p['module'];r=records[n]
    require(sha(p['source'])==p['source_sha256']==r['source_sha256'],'source '+n)
    r['source']=p['source'];r['imports']=p['imports']
    for o in r['objects']: require(sha(o['path'])==o['sha256'],'object '+n)
    needed.append(r)
require(len(needed)==151 and sum(r['module'].startswith('Foundation.') for r in needed)==117,'closure counts')
extmap={r['module']:r for r in base['external']}
for n in ['Mathlib.Combinatorics.Colex','Mathlib.SetTheory.Cardinal.Basic']:
    p=Path('/home/codex/src/Proofs/.lake/packages/mathlib/.lake/build/lib/lean')/(n.replace('.','/')+'.olean')
    extmap[n]={'module':n,'path':str(p),'sha256':sha(p),'scope':'explicit precompiled mathlib package boundary; not freshly replayed'}
ext=[extmap[n] for n in plan['external_imports']]
for r in ext: require(sha(r['path'])==r['sha256'],'external '+r['module'])
out=Path(tempfile.mkdtemp(prefix='formula-encoder222-controller-'));(out/'lib').mkdir();(out/'logs').mkdir()
for r in needed:
    n=r['module']
    if n in refresh:continue
    stem=out/'lib'/n.replace('.','/');stem.parent.mkdir(parents=True,exist_ok=True)
    for o in r['objects']:
        p=Path(o['path']);suffix=p.name[len(n.rsplit('.',1)[-1]):]
        Path(str(stem)+suffix).symlink_to(p)
inputs={'status':'AUTHENTICATED_BEFORE_EXECUTION','overlay':str(out),
 'snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'compiler':base['compiler'],'compiler_sha256':base['compiler_sha256'],'manifest_sha256':base['manifest_sha256'],
 'lean_path':str(out/'lib')+':'+base['lean_path'].split(':',1)[1],
 'parent_receipts':[{'path':str(p),'sha256':h} for p,h in parents],
 'modules':needed,'external':ext,'fresh_prerequisites':refresh,
 'scope':'151 current-source prerequisite records: 148 reused and three fresh syntax clients. The22 added Foundation records retain20 trace bundles versus2 historically executed primary pairs with later companion observations. No Foundation rebuild and no old CProv254 semantic client.'}
(out/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
Path('/tmp/formula-encoder222-controller-latest').write_text(str(out)+'\n')
print(json.dumps({'overlay':str(out),'custom':len(needed),'foundation':117,'reused':148,'refresh':refresh,'external_including_Init':len(ext),'inputs_sha256':sha(out/'inputs.json')},indent=2))
