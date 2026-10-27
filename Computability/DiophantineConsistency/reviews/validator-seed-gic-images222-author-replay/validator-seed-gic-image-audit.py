"""Read-only exact GIC image cache proposal: no Lean, overlay or refresh."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency';R=D/'reviews';O=D/'research'
observations={}
def require(c,m):
    if not c:raise RuntimeError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def observe(p,h=None):
    p=str(p);a=sha(p);require(h is None or a==h,'drift '+p)
    require(p not in observations or observations[p]==a,'mid-audit drift '+p)
    observations[p]=a;return {'path':p,'sha256':a}
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
def mf(p,h):
    observe(p,h);d=read(p)
    for r in d['files'] if isinstance(d,dict) else d:
        q=Path(r['path']);base=ROOT if q.parts[0] in ['Logic','Computability'] else Path(p).parent
        observe(base/q,r['sha256'])
mp=R/'validator-seed-marker-relativization222-replay.json'
cp=R/'validator-seed-tagged-collection222-root-replay.json'
fp=R/'fixed-consistency73-root-replay/plan.json'
observe(mp,'6a9f41af0b6c3683f1ae0f2c6f1767f480e31a98845e8e6e6b9784072a65e5d1')
observe(cp,'9f825accf2e3b4c57b6c4eb5bfa9001d6af7f6c5ac71d8b5e55bd2473e0f8597')
observe(fp)
m,c,f=read(mp),read(cp),read(fp)
require(m['status']=='PASS' and c['status']=='PASS','parent status')
mf(Path(m['bundle'])/'FILES.json',m['manifest_sha256'])
mf(R/'validator-seed-tagged-collection222-root-replay/FILES.json','9c0fb3de41ff6a3e7ad5cb71fae094772bb8c832e685a9a2fb08df7a00aec2a9')
observe(R/'validator-seed-marker-relativization222-author.md','2b028c6cb3d2748be44eb9df528efa59b584ef53b3295c710f2d53a889d94570')
observe(R/'validator-seed-tagged-collection222-root.md')
mi=m['inputs'];ci=read(R/'validator-seed-tagged-collection222-cache.json')
observe(R/'validator-seed-marker-relativization222-cache.json',m['input_inventory_sha256'])
observe(R/'validator-seed-tagged-collection222-cache.json','377db7c77dec3e9d1570419a08aa4cd23e8b7504d14d3f6153a9d582f27a22b0')
for r in mi['inherited_observations']+ci['inherited_observations']:observe(r['path'],r['sha256'])
records={}
for r in f['modules']:
    rr=dict(r);rr['source_sha256']=r['source']['sha256'];rr['source']=r['source']['path']
    rr['provenance_parent']=str(fp);records[r['module']]=rr
for r in mi['modules']+ci['modules']:records[r['module']]=r
for summary,rec,qualification in [(mp,m['completed'][0],'Candidate author PASS; independent ROOT acceptance pending. A separately pinned accepted-provider supplement is required before execution.'),(cp,c['records'][0],'Accepted ROOT Collection provider selected directly.')]:
    src=rec['source'];records[rec['module']]={'module':rec['module'],'source':src['path'],
      'source_sha256':src['sha256'],'objects':[rec['object']],'imports':imports(src['path']),
      'provenance_parent':str(summary),'qualification':qualification}
externals={r['module']:r for r in mi['external']}
for r in ci['external']:
    require(r['module'] not in externals or r['sha256']==externals[r['module']]['sha256'],'external disagreement')
    externals[r['module']]=r
collection_provider=c['private_provider']
if isinstance(collection_provider,dict):collection_provider=collection_provider['path']
marker_provider=str(Path(m['completed'][0]['object']['path']).parents[1])
# Existing paths only. No directory or namespace overlay is created.
search=[collection_provider,marker_provider]
for name in ['ZFCinPA.NativeGicDelta1','ZFCinPA.NativePeel','ZFCinPA.InternalInterpretation','ZFCinPA.SetRelativization']:
    obj=records[name]['objects'][0]['path'];rel=name.replace('.','/')+'.olean'
    require(obj.endswith(rel),'provider suffix');search.append(obj[:-len(rel)].rstrip('/'))
search=list(dict.fromkeys(search+mi['package_paths']))
def branch(targets,expected):
    seen=set();active=set();order=[];boundary=set()
    def visit(n):
        if n in seen:return
        if n not in records:require(n in externals,'unknown boundary '+n);boundary.add(n);return
        require(n not in active,'cycle '+n);active.add(n);r=records[n]
        observe(r['source'],r['source_sha256']);actual=imports(r['source'])
        require(set(actual)==set(r.get('actual_imports',r['imports'])),'header '+n)
        for x in actual:visit(x)
        for obj in r['objects']:observe(obj['path'],obj['sha256'])
        for k in ['provenance','trace','lake_trace']:
            z=r.get(k)
            if isinstance(z,dict) and 'path' in z and 'sha256' in z:observe(z['path'],z['sha256'])
        for p in r.get('absent_companions',[]):require(not Path(p).exists(),'absent companion appeared '+p)
        active.remove(n);seen.add(n);order.append({**r,'actual_imports':actual})
    for n in targets:visit(n)
    ext=[externals[n] for n in sorted(boundary)];providers=[]
    for r in order+ext:
        n=r['module']
        for obj in r['objects'] if 'objects' in r else [r]:
            tail=Path(obj['path']).name[len(n.rsplit('.',1)[-1]):];rel=n.replace('.','/')+tail
            p=next((Path(d)/rel for d in search if (Path(d)/rel).is_file()),None)
            require(p is not None,'missing first provider '+rel)
            providers.append({'module':n,'relative':rel,**observe(p,obj['sha256']),'resolved':str(p.resolve())})
    counts={'cached_modules':len(order),'foundation':sum(n.startswith('Foundation.') for n in seen),
      'artifacts':sum(len(r['objects']) for r in order),'external_boundaries':len(ext),'artifact_providers':len(providers)}
    require(counts==expected,'counts '+str(counts))
    base={r['module'] for r in mi['modules']+ci['modules']}
    return {'imports':targets,'counts':counts,'modules_dependency_order':order,'external':ext,
      'existing_search_path':search,'actual_first_artifact_providers':providers,
      'delta_vs_marker_and_collection_prerequisites':sorted(seen-base),'new_prerequisite_refresh':[]}
base=['ZFCinPA.ValidatorSeedMarkerRelativization222','ZFCinPA.ValidatorSeedTaggedCollection222','ZFCinPA.NativeGicDelta1']
minimal=branch(base,{'cached_modules':212,'foundation':136,'artifacts':620,'external_boundaries':45,'artifact_providers':665})
recommended=branch(base+['ZFCinPA.NativePeel'],{'cached_modules':215,'foundation':136,'artifacts':623,'external_boundaries':45,'artifact_providers':668})
Z=ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA';B=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
anchors=[Z/(n+'.lean') for n in ['NativeGicDelta1','SchemaClosure','NativePeel','R2Ax','InternalInterpretation',
 'ModelCodedBindFree','ModelCodedOpenSchemaAxioms','NativeTheory','ValidatorSeedTaggedCollection222',
 'ValidatorSeedMarkerRelativization222','ValidatorSeedMarkerDischarge222','ValidatorFullSeedTheory222',
 'ValidatorEqualityImages222','ValidatorSeedSourceBasis222']]
anchors += [B/(n+'.lean') for n in ['KLowerTag','KLowerQHyp','KQHyp','KQ1ZF']]
result={'status':'READ_ONLY_PROPOSAL_NO_LEAN_NO_OVERLAY_NO_REFRESH',
 'snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'branches':{'recommended_existing_syntax_helpers':recommended,'minimal_local_helper_alternative':minimal},
 'selected_collection_provider':records['ZFCinPA.ValidatorSeedTaggedCollection222'],
 'candidate_marker_provider':records['ZFCinPA.ValidatorSeedMarkerRelativization222'],
 'compiler':observe(mi['compiler']['path'],mi['compiler']['sha256']),
 'toolchain':observe(mi['toolchain']['path'],mi['toolchain']['sha256']),
 'manifest':observe(mi['manifest']['path'],mi['manifest']['sha256']),
 'parents':[observe(p) for p in [mp,cp,fp]],'anchor_sources':[observe(p) for p in anchors],
 'driver':observe(__file__),'observations':[{'path':p,'sha256':h} for p,h in sorted(observations.items())],
 'qualification':'Planning only. Collection selects accepted ROOT directly. MarkerRelativization is author-only pending acceptance and requires a separately pinned ROOT-provider supplement before execution. The four old syntax/interpretation modules retain previously accepted source/run and absent-companion qualifications; no fresh whole-closure claim. NativePeel only supplies two syntax identities; its Good-dependent peel is not applicable.'}
p=O/'validator-seed-gic-image-plan.json';require(not p.exists(),'frozen plan exists')
p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'path':str(p),'sha256':sha(p),'observations':len(observations),
 'branches':{k:v['counts'] for k,v in result['branches'].items()}},indent=2))
