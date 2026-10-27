"""Read-only GIC cache supplement selecting accepted ROOT Marker; no overlay or Lean."""
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
planpath=P/'validator-seed-gic-image-plan.json'
planpin=pin(planpath,'f9c5279931ec426798b8fe1b1143bfb188c90f5ec0d7f27368808cef258ad20f')
planmf=P/'validator-seed-gic-image-FILES.json'
manifest(planmf,'c3fc61d1a8331ce2efa57b5d560c8b2b6a82b9622cd3b6f84c1ea350e1f60610')
plan=read(planpath)
for o in plan['observations']:pin(o['path'],o['sha256'])
rp=R/'validator-seed-marker-relativization222-root-replay.json'
rpin=pin(rp,'6378b980a50f5d0d924e450efefabb231e97a0eaeac6cfd28291bcd39d65450a')
rmf=R/'validator-seed-marker-relativization222-root-replay/FILES.json'
manifest(rmf,'fc464fafa04bf254bf11cf1b6ebe961f93009405fe9618eb350e746b0eb29086')
receipt=pin(R/'validator-seed-marker-relativization222-root.md')
r=read(rp);require(r['status']=='PASS' and len(r['records'])==2,'accepted pair')
for k in ['author','state','durable_state','driver','inputs','final_authentication']:
    z=r[k];pin(z['path'],z['sha256'])
for rec in r['records']:
    require(rec['exit_code']==0 and rec['author_object_and_full_log_equal'],'independent result')
    for k in ['source','snapshot','object','log','timing']:
        z=rec[k];pin(z['path'],z['sha256'])
    require(not Path(rec['object']['path']).is_symlink(),'accepted output regular')
require(Path(r['records'][0]['log']['path']).read_text()=='','main diagnostics')
require(len(r['records'][1]['axiom_reports'])==15,'fifteen root audits')
old=plan['candidate_marker_provider'];new=r['records'][0]
require(old['module']==new['module'] and old['source_sha256']==new['source']['sha256'],'marker source')
require(old['objects'][0]['sha256']==new['object']['sha256'],'marker object changed')
base=plan['branches']['recommended_existing_syntax_helpers']
records={x['module']:dict(x) for x in base['modules_dependency_order']}
records[new['module']]={**old,'objects':[new['object']],
 'provenance_parent':str(rp),'qualification':'Accepted independent ROOT provider selected directly; frozen author history retained unchanged.'}
externals={x['module']:x for x in base['external']}
oldroot=str(Path(old['objects'][0]['path']).parents[1]);newroot=r['provider']
search=[newroot if x==oldroot else x for x in base['existing_search_path']]
require(newroot in search and oldroot not in search,'exact provider replacement')
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
for n in base['imports']:visit(n)
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
for n,expected in [(new['module'],new['object']),
                    ('ZFCinPA.ValidatorSeedTaggedCollection222',plan['selected_collection_provider']['objects'][0])]:
    actual=next(x for x in providers if x['module']==n and x['relative'].endswith('.olean'))
    require(Path(actual['path']).resolve()==Path(expected['path']).resolve(),'direct accepted provider '+n)
counts={'cached_modules':len(order),'foundation':sum(x['module'].startswith('Foundation.') for x in order),
 'artifacts':sum(len(x['objects']) for x in order),'external_boundaries':len(ext),'artifact_providers':len(providers)}
require(counts=={'cached_modules':215,'foundation':136,'artifacts':623,'external_boundaries':45,'artifact_providers':668},'scope')
result={'status':'READ_ONLY_ACCEPTED_PROVIDER_SUPPLEMENT_NO_LEAN_NO_OVERLAY_NO_REFRESH',
 'original_plan':planpin,'original_plan_manifest':pin(planmf),
 'accepted_marker_packet':rpin,'accepted_marker_manifest':pin(rmf),'accepted_marker_receipt':receipt,
 'selected_marker_provider':records[new['module']],
 'selected_collection_provider':plan['selected_collection_provider'],
 'imports':base['imports'],'counts':counts,'modules_dependency_order':order,'external':ext,
 'existing_search_path':search,'actual_first_artifact_providers':providers,
 'compiler':pin(plan['compiler']['path'],plan['compiler']['sha256']),
 'toolchain':pin(plan['toolchain']['path'],plan['toolchain']['sha256']),
 'manifest':pin(plan['manifest']['path'],plan['manifest']['sha256']),
 'driver':pin(__file__),'new_prerequisite_refresh':[],
 'observations':[{'path':p,'sha256':h} for p,h in sorted(OBS.items())],
 'qualification':'Replaces only the provisional Marker primary with the accepted byte-identical ROOT primary. Collection ROOT remains selected directly. Original frozen proposal and author history unchanged. Historical source/run and absent-companion qualifications retained. Complete DAG/first providers rechecked; this is neither implementation authorization nor a fresh compilation claim.'}
p=P/'validator-seed-gic-image-accepted-provider.json';require(not p.exists(),'frozen supplement exists')
p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'path':str(p),'sha256':sha(p),'counts':counts,'observations':len(OBS)},indent=2))
