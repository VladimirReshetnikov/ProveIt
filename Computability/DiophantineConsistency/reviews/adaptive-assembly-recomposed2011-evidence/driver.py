from pathlib import Path
import hashlib,json,os,shutil,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');N=Path(os.environ['ADAPTIVE_HALF_BASE']);P=Path(os.environ['ADAPTIVE_PELL_BASE']);I=Path('/tmp/adaptive13-assembly-independent-4tmj26_8');Q=Path('/tmp/adaptive13-assembly-prefix-d_s896gq');M=Path('/tmp/adaptive13-machine-independent-2fb2oum7');D=Path('/tmp/adaptive13-cell-root-parent-wnvsel13');roots={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver','FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
checks={};records=[];grafts={}
def guard(path,h):
 path=str(path);assert path not in checks or checks[path]==h,(path,'inconsistent guard');checks[path]=h;assert sha(path)==h,(path,'changed')
def source(ns,n):return roots[ns]/(n.replace('.','/')+'.lean')
def relmod(m):return Path(m.replace('.','/')+'.olean')
def guarded_record(label,base,r):
 ns=r.get('namespace','DiophantineConsistency');n=r['name'];src=roots[ns]/(n+'.lean');obj=base/'lib'/ns/(n+'.olean');guard(src,r['source_sha256']);guard(obj,r['object_sha256']);records.append({'branch':label,'namespace':ns,'name':n,'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'source':str(src),'object':str(obj)});return Path(ns)/(n+'.olean'),obj,r['object_sha256']
def add_graft(rel,obj,h,label):
 key=str(rel);assert key not in grafts or grafts[key][1]==h,(key,'graft mismatch');grafts[key]=(Path(obj),h,label);guard(obj,h)
ns=read(N/'state.json');assert ns['status']=='PASS';guard(N/'state.json',sha(N/'state.json'))
for r in ns['records']:guarded_record('half-index',N,r)
# Authenticate the unchanged earlier window/population source and object anchors.
for path,exclude in [(Path('/tmp/adaptive13-window-refresh-s_sg2q3z'),{'ArithmeticCarrierRadix2011'}),(Path('/tmp/adaptive13-population-refresh-8rcbg45y'),{'ArithmeticHalfBinomial','ArithmeticHalfBinomialSandwich','ArithmeticBinomLegendre'}),(Path('/tmp/adaptive13-window-postmerge-vx7i_2i7'),{'ArithmeticAdaptiveWindow2011','ArithmeticAdaptiveWindow2011Checks'})]:
 s=read(path/'state.json');assert s['status']=='PASS';guard(path/'state.json',sha(path/'state.json'))
 for r in s['records']:
  n=r['name'];ns_=r.get('namespace','DiophantineConsistency')
  if n in exclude:continue
  guard(roots[ns_]/(n+'.lean'),r['source_sha256']);guard(N/'lib'/ns_/(n+'.olean'),r['object_sha256'])
for path,name in [(Path('/tmp/adaptive13-legendre-postmerge-p2ybhokz'),'ArithmeticBinomLegendre'),(Path('/tmp/adaptive13-sandwich-postmerge-8tly07ke'),'ArithmeticHalfBinomialSandwich')]:
 s=read(path/'state.json');assert s['status']=='PASS';guard(path/'state.json',sha(path/'state.json'));r=next(x for x in s['records'] if x['name']==name);guard(source('DiophantineConsistency',name),r['source_sha256']);guard(N/'lib/DiophantineConsistency'/(name+'.olean'),r['object_sha256'])
# Add the independently accepted Wang-independent base outputs.
is_=read(I/'state.json');assert is_['status']=='PASS';guard(I/'state.json',sha(I/'state.json'));ia=read(I/'audit.json');guard(I/'audit.json',sha(I/'audit.json'))
for r in is_['records']:
 rel,obj,h=guarded_record('independent-seven',I,r);add_graft(rel,obj,h,'independent-seven')
for r in ia['rows']:
 guard(source('DiophantineConsistency',r['module']),r['source_sha256']);guard(r['resolved_object'],r['object_sha256']);guard(N/'lib/DiophantineConsistency'/(r['module']+'.olean'),r['object_sha256'])
for r in ia.get('cross_cache_records',[]):
 guard(r['current_source'],r['source_sha256']);guard(r['other_source'],r['source_sha256']);guard(r['object'],r['object_sha256']);guard(N/'lib'/relmod(r['module']),r['object_sha256'])
# Add only audited prefix objects and the new target outputs from each accepted branch.
branch_audits=[]
for label,b in [('prefix',Q),('machine',M)]:
 s=read(b/'state.json');assert s['status']=='PASS';guard(b/'state.json',sha(b/'state.json'));a=read(b/'audit.json');guard(b/'audit.json',sha(b/'audit.json'));assert not a['missing'] and not a['bad'];guard(D/'state.json',a['prefix_state_sha256']);branch_audits.append((label,a))
 for r in a['rows']:
  ns_,n=r['module'].split('.',1);guard(source(ns_,n),r['source_sha256']);guard(r['object'],r['object_sha256'])
  if r['provenance']=='authenticated 36-module prefix':add_graft(relmod(r['module']),r['object'],r['object_sha256'],'verified-prefix')
 for r in s['records']:
  rel,obj,h=guarded_record(label,b,r);add_graft(rel,obj,h,label)
# Add accepted seed objects whose own closure excludes the changed sources, then the two rebuilt Pell targets.
ps=read(P/'state.json');assert ps['status']=='PASS';guard(P/'state.json',sha(P/'state.json'));pa=read(P/'audit.json');guard(P/'audit.json',sha(P/'audit.json'))
for r in pa['rows']:
 guard(r['source'],r['source_sha256']);guard(r['old_object'],r['object_sha256']);guard(r['new_object'],r['object_sha256']);guard(N/'lib/DiophantineConsistency'/(r['module']+'.olean'),r['object_sha256'])
for r in pa['seeds']:
 guard(r['source'],r['source_sha256']);guard(r['object'],r['object_sha256']);add_graft(Path('DiophantineConsistency')/(r['module']+'.olean'),r['object'],r['object_sha256'],'accepted-seed')
 records.append({'branch':'accepted-seed','namespace':'DiophantineConsistency','name':r['module'],'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'source':r['source'],'object':r['object']})
for r in ps['records']:
 rel,obj,h=guarded_record('pell-rebase',P,r);add_graft(rel,obj,h,'pell-rebase')
assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-assembly-recomposed-'));lib=w/'lib';lib.mkdir();shutil.copyfile(__file__,w/'driver.py');selected={}
for f in (N/'lib').rglob('*'):
 if f.is_file():
  rel=str(f.relative_to(N/'lib'));h=sha(f);dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());selected[rel]={'path':str(f),'sha256':h,'origin':'canonical-half-index'}
for rel,(obj,h,label) in sorted(grafts.items()):
 dest=lib/rel
 if dest.is_file():assert sha(dest)==h,(rel,'canonical overlap differs');continue
 dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(obj.resolve());selected[rel]={'path':str(obj),'sha256':h,'origin':label}
# Verify every project dependency used by prefix/machine branches against the actual chosen overlay.
for label,a in branch_audits:
 for r in a['rows']:
  obj=lib/relmod(r['module']);assert obj.is_file() and sha(obj)==r['object_sha256'],(label,r['module'],'chosen overlap differs')
# Reauthenticate *all* inherited sources, source anchors and objects after the overlay is built.
for path,h in checks.items():assert sha(path)==h,(path,'changed during composition')
for rel,r in selected.items():assert sha(r['path'])==r['sha256'] and sha(lib/rel)==r['sha256'],(rel,'changed during composition')
(w/'guards.json').write_text(json.dumps(checks,indent=2)+'\n');(w/'providers.json').write_text(json.dumps(selected,indent=2)+'\n')
state={'status':'PASS','private':str(w),'scope':'canonical current half-index base plus individually authenticated outputs from accepted Wang-independent branches and Pell rebase; every recorded inherited source and anchor rechecked at end; cache, Foundation and package internals inherited boundaries','canonical':str(N),'branches':{'independent-seven':str(I),'prefix':str(Q),'machine':str(M),'pell-rebase':str(P)},'records':records,'guards_sha256':sha(w/'guards.json'),'providers_sha256':sha(w/'providers.json'),'boundary':ns['boundary']};(w/'state.json').write_text(json.dumps(state,indent=2)+'\n');print('PASS',w,'objects',len(selected),'guards',len(checks),'records',len(records),flush=True)
