"""Authenticate the final two-leaf result and preserve every failed attempt."""
import hashlib,json,re,shutil,os
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
REV=D/'reviews'
RUN=Path(Path('/tmp/seed-gic-images222-current.txt').read_text().strip())
A=Path((RUN/'latest-attempt.txt').read_text().strip())
I=json.loads((RUN/'inputs.json').read_text())
ST=json.loads((A/'state.json').read_text())
STEM='validator-seed-gic-images222'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,msg):
    if not c:raise RuntimeError(msg)
def strip_comments(text):
    out=[];i=0;depth=0
    while i<len(text):
        if text.startswith('/-',i):depth+=1;out.extend('  ');i+=2
        elif depth and text.startswith('-/',i):depth-=1;out.extend('  ');i+=2
        elif not depth and text.startswith('--',i):
            j=text.find('\n',i);j=len(text) if j<0 else j
            out.extend(' '*(j-i));i=j
        else:out.append(text[i] if not depth or text[i]=='\n' else ' ');i+=1
    require(depth==0,'unclosed source comment')
    return ''.join(out)
def imports(path):
    body=strip_comments(Path(path).read_text())
    names=[] if re.search(r'^\s*prelude\s*$',body,re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',body,re.M):
        names.extend(re.findall(r'[\w.]+',line))
    return list(dict.fromkeys(names))
require(ST['status']=='PASS' and len(ST['records'])==2,'terminal pair')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
observations=[]
def pin(p,h):
    require(sha(p)==h,'drift: '+str(p));observations.append({'path':str(p),'sha256':h})
for r in ST['pre_observations']+ST['post_observations']:pin(r['path'],r['sha256'])
for r in ST['records']:
    for o in [r['source'],r['object'],r['log'],r['timing']]:pin(o['path'],o['sha256'])
    pin(r['source']['snapshot'],r['source']['snapshot_sha256'])
    require(r['exit_code']==0 and not Path(r['object']['path']).is_symlink(),'fresh regular output')
require(Path(ST['records'][0]['log']['path']).read_text()=='','empty main log')
checks=Path(ST['records'][1]['log']['path']).read_text()
require('warning:' not in checks and len(ST['records'][1]['axiom_reports'])==12,'clean12reports')
for name,ax in ST['records'][1]['axiom_reports']:
    require(set(re.findall(r'[A-Za-z_][\w.]*',ax))<= {'propext','Classical.choice','Quot.sound'},'axiom '+name)
by={r['module']:r for r in I['modules']};ext={r['module']:r for r in I['external']}
seen=set();bounds=set();headers=[]
def visit(n):
    if n in seen:return
    if n not in by:require(n in ext,'unlisted boundary '+n);bounds.add(n);return
    r=by[n];pin(r['source'],r['source_sha256']);actual=imports(r['source'])
    require(set(actual)==set(r.get('actual_imports',r['imports'])),'source header '+n)
    seen.add(n);headers.append({'module':n,'imports':actual,'source_sha256':sha(r['source'])})
    for x in actual:visit(x)
for n in ['ZFCinPA.ValidatorSeedMarkerRelativization222','ZFCinPA.ValidatorSeedTaggedCollection222',
          'ZFCinPA.NativeGicDelta1','ZFCinPA.NativePeel']:visit(n)
require(seen==set(by) and bounds==set(ext),'exact reachable closure')
search=ST['records'][0]['lean_path'].split(':')
providers=[];primaries=[]
for n,r in list(by.items())+list(ext.items()):
    for o in (r['objects'] if n in by else [r]):
        suffix=Path(o['path']).name[len(n.rsplit('.',1)[-1]):]
        rel=n.replace('.','/')+suffix
        p=next((Path(d)/rel for d in search if (Path(d)/rel).is_file()),None)
        require(p is not None and p.resolve()==Path(o['path']).resolve(),'first provider '+rel)
        pin(p,o['sha256'])
        entry={'module':n,'relative':rel,'path':str(p),'resolved':str(p.resolve()),'sha256':sha(p)}
        providers.append(entry)
        if suffix=='.olean':primaries.append(entry)
require(len(providers)==668 and len(primaries)==260,'exact668artifacts/260primaries')
bundle=REV/(STEM+'-author-replay');require(not bundle.exists(),'new evidence bundle');bundle.mkdir()
(bundle/'closure-reauth.json').write_text(json.dumps({'headers':headers,'first_providers':primaries,
 'artifact_providers':providers,'observations':observations,'counts':I['counts']},indent=2)+'\n')
# Preserve all records and both exact source snapshots, never copy cached objects.
for attempt in sorted((RUN/'attempts').iterdir()):
    dest=bundle/'attempts'/attempt.name;dest.mkdir(parents=True)
    for p in sorted(attempt.iterdir()):
        if p.is_file():os.link(p,dest/p.name)
for n in ['prepare','build','freeze']:
    shutil.copy2('/tmp/seed-gic-images222-'+n+'.py',bundle/(n+'.py'))
os.link(RUN/'inputs.json',bundle/'inputs.json')
shutil.copy2(RUN/'build-v1.py',bundle/'build-v1.py')
for r in ST['sources']:shutil.copy2(r['path'],bundle/Path(r['path']).name)
for p in sorted((D/'research').glob('validator-seed-gic-image-*')):
    if p.is_file():shutil.copy2(p,bundle/p.name)
manifest=[]
for p in sorted(bundle.rglob('*')):
    if p.is_file():manifest.append({'path':str(p.relative_to(bundle)),'sha256':sha(p),'bytes':p.stat().st_size})
(bundle/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n')
cache=REV/(STEM+'-cache.json');require(not cache.exists(),'new cache inventory')
os.link(RUN/'inputs.json',cache)
attempts=[]
for p in sorted((RUN/'attempts').iterdir()):
    st=json.loads((p/'state.json').read_text())
    exception=p/'postcheck-exception.json'
    attempts.append({'path':str(p),'status':st['status'],
      'terminal_qualification':json.loads(exception.read_text()) if exception.exists() else None,
      'state_sha256':sha(p/'state.json'),
      'records':st['records']})
summary={'status':'PASS','scope':'Every actual GicR instance has a guarded source proof in seedTheory, uniformly over all internally sized markers, matrices/free parameters and closure counts in each universe-zero I-Sigma1 model. Concrete AxiomImages gicTheory is proved. Swapped RELATIVIZED matrices; decreasing-marker Sigma1 closure. No Good/shift-fixed marker, raw CP, quotient/WF, ZF/ZFC or HA equivalence.',
 'inputs':I,'input_inventory_sha256':sha(cache),'completed':ST['records'],'final_run':str(A),
 'observation_count':len(observations),'bundle':str(bundle),'manifest_sha256':sha(bundle/'FILES.json'),
 'attempts':attempts,'development':'All three attempts preserved. First main failed on typed numeral casts, a missing atom simplifier, wrong free_val name and the existing NativePeel universe-zero API. Second both compiler commands passed but the driver rejected one unnecessarySimpa warning; original RUNNING state is retained with a separate terminal-exception record. Third final pair passed cleanly. NativePeel existing Type0 boundary was approved explicitly; arbitrary internal models/codes/closure counts retained. No import, cap or dependency refresh change.',
 'read_scope':'Full main/Checks and preparation/build/freezing drivers read before execution; all proof deltas fully read. Actual GIC skeleton and recognizer, Collection orientation, moving marker substitutions/free laws, internal closure induction and source proof contracts reviewed. NativePeel reused for two pure syntax identities and ordinary source derivable_mp only; no Good peel. Author checkpoint awaiting independent acceptance.'}
p=REV/(STEM+'-replay.json');require(not p.exists(),'new replay summary')
p.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'summary':str(p),'summary_sha256':sha(p),'cache_sha256':sha(cache),
 'manifest_sha256':sha(bundle/'FILES.json'),'files':len(manifest),'observations':len(observations),
 'sources':[{'module':r['module'],'source_sha256':r['source']['sha256'],'object':r['object'],
 'seconds':r['seconds']} for r in ST['records']]},indent=2))
