"""Read-only next source-bridge inventory. No Lean, overlay, or dependency changes."""
import hashlib,json,re
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency';R=D/'reviews';P=D/'research'
OBS={}
def require(c,m):
    if not c:raise RuntimeError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def pin(p,h=None):
    p=str(p);a=sha(p);require(h is None or a==h,'drift '+p)
    require(p not in OBS or OBS[p]==a,'mid-audit drift '+p)
    OBS[p]=a;return {'path':p,'sha256':a}
def manifest(p,h):
    pin(p,h);d=read(p)
    for r in d['files'] if isinstance(d,dict) else d:
        q=Path(r['path']);base=ROOT if q.parts[0] in ['Logic','Computability'] else Path(p).parent
        pin(base/q,r['sha256'])
def imports(p):
    s=Path(p).read_text();out=[];i=0;depth=0
    while i<len(s):
        if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
        elif depth and s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
        elif not depth and s.startswith('--',i):
            j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
        else:out.append(s[i] if not depth or s[i]=='\n' else ' ');i+=1
    require(depth==0,'unclosed comment');s=''.join(out)
    names=[] if re.search(r'^\s*prelude\s*$',s,re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M):
        names.extend(re.findall(r'[\w.]+',line))
    return list(dict.fromkeys(names))
parent=R/'validator-seed-logical-images222-replay.json'
parentpin=pin(parent,'5f0797aba7355b5fafbfa25adc56b22ee3a37700c63ce0a5dd1b8af95651a57c')
parentmf=R/'validator-seed-logical-images222-author-replay/FILES.json'
manifest(parentmf,'02d815a565075f547c2932f368d38c91daf7880cf286c61cd0ff7663410b3cfa')
receipt=pin(R/'validator-seed-logical-images222-author.md','7fdadd153145201a3920e4e6d0b8d84a456444e031a3ab9ecb52c329362db9e7')
j=read(parent);require(j['status']=='PASS','author terminal status');base=j['inputs']
for o in base['observations']:pin(o['path'],o['sha256'])
records={x['module']:dict(x) for x in base['modules']}
rootpacket=R/'validator-seed-logical-images222-root-replay.json'
rootpin=pin(rootpacket,'97e86d457fa22c4adc6ad0db0b427084a3e8d52430bc6cafa1a9f375d167d9db')
rootmf=R/'validator-seed-logical-images222-root-replay/FILES.json'
manifest(rootmf,'7eded66b85380e049713de51c4b70566a8cea4a7a4651976c186457344cf2491')
rootreceipt=pin(R/'validator-seed-logical-images222-root.md')
r=read(rootpacket);require(r['status']=='PASS','ROOT terminal status')
for k in ['author','state','durable_state','driver','inputs','final_authentication']:
    z=r[k];pin(z['path'],z['sha256'])
rootinputs=read(r['inputs']['path'])
for z in rootinputs['pins']:pin(z['path'],z['sha256'])
for rec in r['records']:
    require(rec['exit_code']==0 and rec['author_object_and_full_log_equal'],'ROOT pair result')
    for k in ['source','snapshot','log','timing','object']:
        z=rec[k];pin(z['path'],z['sha256'])
require(len(r['records'][1]['axiom_reports'])==15,'ROOT audit count')
new=r['records'][0]
require(new['source']['sha256']==j['completed'][0]['source']['sha256'] and
 new['object']['sha256']==j['completed'][0]['object']['sha256'],'ROOT source/object equality')
require(new['exit_code']==0 and Path(new['log']['path']).read_text()=='','LogicalImages main ROOT pass')
require(not Path(new['object']['path']).is_symlink(),'LogicalImages fresh output regular')
for k in ['log','timing','object']:pin(new[k]['path'],new[k]['sha256'])
pin(new['source']['path'],new['source']['sha256']);pin(new['snapshot']['path'],new['snapshot']['sha256'])
records[new['module']]={'module':new['module'],'source':new['source']['path'],
 'source_sha256':new['source']['sha256'],'objects':[new['object']],
 'imports':imports(new['source']['path']),'provenance_parent':str(rootpacket),
 'qualification':'Accepted independent ROOT LogicalImages source/object selected directly; original author evidence separately authenticated.'}
externals={x['module']:x for x in base['external']}
search=rootinputs['LEAN_PATH']
require(search[0]==r['provider'],'explicit ROOT overlay first')
seen=set();active=set();order=[];boundary=set()
def visit(n):
    if n in seen:return
    if n not in records:require(n in externals,'unknown boundary '+n);boundary.add(n);return
    require(n not in active,'import cycle');active.add(n);x=records[n]
    pin(x['source'],x['source_sha256']);actual=imports(x['source'])
    require(set(actual)==set(x.get('actual_imports',x['imports'])),'header '+n)
    for dep in actual:visit(dep)
    for obj in x['objects']:pin(obj['path'],obj['sha256'])
    for k in ['provenance','trace','lake_trace']:
        v=x.get(k)
        if isinstance(v,dict) and 'path' in v and 'sha256' in v:pin(v['path'],v['sha256'])
    for a in x.get('absent_companions',[]):require(not Path(a).exists(),'historically absent '+a)
    active.remove(n);seen.add(n);order.append({**x,'actual_imports':actual})
visit(new['module'])
require(seen==set(records) and boundary==set(externals),'exact reachable DAG')
ext=[externals[n] for n in sorted(boundary)];providers=[]
for x in order+ext:
    n=x['module']
    for obj in x['objects'] if 'objects' in x else [x]:
        suffix=Path(obj['path']).name[len(n.rsplit('.',1)[-1]):];relative=n.replace('.','/')+suffix
        first=next((Path(d)/relative for d in search if (Path(d)/relative).is_file()),None)
        require(first is not None,'missing first '+relative)
        providers.append({'module':n,'relative':relative,**pin(first,obj['sha256']),
                          'resolved':str(first.resolve())})
require(Path(next(x for x in providers if x['module']==new['module'])['path']).resolve()==
 Path(new['object']['path']).resolve(),'direct accepted ROOT LogicalImages provider')
counts={'cached_modules':len(order),'foundation':sum(x['module'].startswith('Foundation.') for x in order),
 'artifacts':sum(len(x['objects']) for x in order),'external_boundaries':len(ext),'artifact_providers':len(providers)}
require(counts=={'cached_modules':217,'foundation':136,'artifacts':625,'external_boundaries':45,'artifact_providers':670},'scope')
custom=['ValidatorSourceFullSeed222','ValidatorSeedRawComprehension222','ValidatorSeedGuardedComprehension222','ValidatorSeedLogicalImages222','ValidatorEqualityImages222','ValidatorFullSeedTheory222','ValidatorSeedSourceBasis222',
 'ValidatorSeedTaggedCollection222','ValidatorSeedMarkerDischarge222','ValidatorSeedMarkerRelativization222',
 'ValidatorSeedGicImages222','ModelCodedSpecialization','ModelCodedOpenSchemaAxioms','SetCongruence',
 'NativeGicDelta1','NativePeel','NativeTheory','NativeInterp','NativeSchema','InternalInterpretation',
 'OpenTemplateClosure','SetPlaceholderQuotient','LSchema']
guides=[pin(ROOT/('Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/'+n+'.lean')) for n in custom]
guides += [pin(ROOT/('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'+n+'.lean')) for n in
 ['KLowerRaw','KLowerTag','KLowerEqv','KLowerQHyp','KQHyp','KQ1Model','KQ1ZF',
  'ProfileCollection','ProfileComposition','ProfileSyntax','ProfileModel']]
eqsrc=next(x['source'] for x in order if x['module']=='Foundation.FirstOrder.Basic.Eq')
guides.append(pin(eqsrc))
result={'status':'READ_ONLY_PLAN_NO_LEAN_NO_OVERLAY_NO_REFRESH',
 'parent_author_packet':parentpin,'parent_author_manifest':pin(parentmf),'parent_author_receipt':receipt,
 'accepted_root_packet':rootpin,'accepted_root_manifest':pin(rootmf),'accepted_root_receipt':rootreceipt,
 'selected_logical_provider':records[new['module']],
 'imports':[new['module']],'counts':counts,'modules_dependency_order':order,'external':ext,
 'existing_search_path':search,'actual_first_artifact_providers':providers,
 'compiler':pin(base['compiler']['path'],base['compiler']['sha256']),
 'toolchain':pin(base['toolchain']['path'],base['toolchain']['sha256']),
 'manifest':pin(base['manifest']['path'],base['manifest']['sha256']),
 'source_anchors':guides,'driver':pin(__file__),'new_prerequisite_refresh':[],
 'observations':[{'path':p,'sha256':h} for p,h in sorted(OBS.items())],
 'qualification':'Full selected header/DAG/object/first-provider reauthentication only. Existing historical source-run and missing-companion qualifications remain inherited. Guide sources outside the selected DAG are source-only, not authenticated compiled dependencies. Accepted ROOT LogicalImages is selected directly using its explicit overlay plus package boundaries only; no new proof source or compiler was executed.'}
p=P/'validator-seed-transitive-plan.json';require(not p.exists(),'frozen plan exists')
p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'path':str(p),'sha256':sha(p),'counts':counts,'observations':len(OBS)},indent=2))
