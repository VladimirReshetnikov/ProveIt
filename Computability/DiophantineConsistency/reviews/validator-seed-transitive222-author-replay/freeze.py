"""Authenticate the final two-leaf result and preserve every failed attempt."""
import hashlib,json,re,shutil,os
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
REV=D/'reviews'
RUN=Path(Path('/tmp/seed-transitive222-current.txt').read_text().strip())
A=Path((RUN/'latest-attempt.txt').read_text().strip())
I=json.loads((RUN/'inputs.json').read_text())
ST=json.loads((A/'state.json').read_text())
STEM='validator-seed-transitive222'
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
for r in I['inherited_observations']+I['observations']:pin(r['path'],r['sha256'])
for r in [I['compiler'],I['toolchain'],I['manifest'],I['plan'],I['plan_manifest']]:pin(r['path'],r['sha256'])
for phase in ['pre_authentication','post_authentication']:
    require(ST[phase]['count']==len(I['inherited_observations'])+len(I['observations'])+5,'authentication count')
    pin(ST[phase]['inputs']['path'],ST[phase]['inputs']['sha256'])
for r in ST['records']:
    for o in [r['source'],r['object'],r['log'],r['timing']]:pin(o['path'],o['sha256'])
    pin(r['source']['snapshot'],r['source']['snapshot_sha256'])
    require(r['exit_code']==0 and not Path(r['object']['path']).is_symlink(),'fresh regular output')
require(Path(ST['records'][0]['log']['path']).read_text()=='','empty main log')
checks=Path(ST['records'][1]['log']['path']).read_text()
require('warning:' not in checks and len(ST['records'][1]['axiom_reports'])==17,'clean17reports')
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
for n in ['ZFCinPA.ValidatorSeedLogicalImages222']:visit(n)
require(seen==set(by) and bounds==set(ext),'exact reachable closure')
search=ST['records'][0]['lean_path'].split(':')
PLAN=json.loads(Path(I['plan']['path']).read_text())
expectedproviders={(x['module'],x['relative']):x for x in PLAN['actual_first_artifact_providers']}
providers=[];primaries=[]
for n,r in list(by.items())+list(ext.items()):
    for o in (r['objects'] if n in by else [r]):
        suffix=Path(o['path']).name[len(n.rsplit('.',1)[-1]):]
        rel=n.replace('.','/')+suffix
        p=next((Path(d)/rel for d in search if (Path(d)/rel).is_file()),None)
        require(p is not None and p.resolve()==Path(expectedproviders[n,rel]['path']).resolve(),'first provider '+rel)
        pin(p,o['sha256'])
        entry={'module':n,'relative':rel,'path':str(p),'resolved':str(p.resolve()),'sha256':sha(p)}
        providers.append(entry)
        if suffix=='.olean':primaries.append(entry)
require(len(providers)==670 and len(primaries)==262,'exact670artifacts/262primaries')
bundle=REV/(STEM+'-author-replay');require(not bundle.exists(),'new evidence bundle');bundle.mkdir()
(bundle/'closure-reauth.json').write_text(json.dumps({'headers':headers,'first_providers':primaries,
 'artifact_providers':providers,'observations':observations,'counts':I['counts']},indent=2)+'\n')
# Preserve all records and both exact source snapshots, never copy cached objects.
for attempt in sorted((RUN/'attempts').iterdir()):
    dest=bundle/'attempts'/attempt.name;dest.mkdir(parents=True)
    for p in sorted(attempt.iterdir()):
        if p.is_file():os.link(p,dest/p.name)
for n in ['prepare','build','freeze']:
    shutil.copy2('/tmp/seed-transitive222-'+n+'.py',bundle/(n+'.py'))
for p in sorted(Path('/tmp').glob('seed-transitive222-repair*.py')):
    shutil.copy2(p,bundle/p.name)
for p in sorted(Path('/tmp').glob('seed-transitive222-*.log')):
    if 'freeze' not in p.name: shutil.copy2(p,bundle/p.name)
for name in ['validator-seed-transitive222-plan-root.md','validator-seed-transitive222-plan-root.json']:
    os.link(REV/name,bundle/name)
os.link(RUN/'inputs.json',bundle/'inputs.json')
for r in ST['sources']:shutil.copy2(r['path'],bundle/Path(r['path']).name)
for p in sorted((D/'research').glob('validator-seed-transitive-plan*')):
    if p.is_file():os.link(p,bundle/p.name)
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
summary={'status':'PASS','scope':'Actual source Proof certificates for raw transitive containers, tagged transitive containers under Empty(t) and t in a, and exact pairs on tagged tests under Empty(t). Arbitrary internal parameters in Type0 I-Sigma1 models; same full-seed container supplies raw transitivity. Total raw formula-constructor Sigma1 graphs are bound to the typed formulas; no claim that proof selectors have Sigma1 graphs. No CP/container schema, coded Eqv/Member, QHyp/quotient/WF, ZF/ZFC or HA endpoint is asserted.',
 'inputs':I,'input_inventory_sha256':sha(cache),'completed':ST['records'],'final_run':str(A),
 'observation_count':len(observations),'bundle':str(bundle),'manifest_sha256':sha(bundle/'FILES.json'),
 'attempts':attempts,
 'development':'Five attempts preserved. Attempts1-3 main failures concern opaque-helper unfolding, nested free/bound normalization, context-preserving simplification, finite proof-search resource elaboration, quote/vector and numeral-cast bindings, and metadata syntax parentheses. The longer propositional chains were replaced by actual finite-context deduction/MP. Attempt4 main passed cleanly and checks printed17 standard reports but two literal expansion controls failed at rfl. Attempt5 changes only those controls to explicit simp and both leaves pass cleanly. No import, cap, public theorem-premise, or dependency-refresh change.',
 'plan_correction':'The frozen original plan used incorrect downstream ProfilePairs terminology. The separate preserved addendum records that ProfilePairs.Pair uses ClassMember and Same, not the later interpreted Member/coded Eqv. No profile conversion theorem is claimed by this pair.',
 'read_scope':'Complete main/Checks and preparation/build/freezing drivers read before execution; all proof deltas fully read. Actual full-seed request and closure, singleton uniqueness, guarded truth cut, raw/tagged binder order, source proof-code certificates and total raw constructor bindings reviewed. Sole import accepted LogicalImages; no prerequisites compiled. Author checkpoint awaiting independent acceptance.',
 'storage':'Immutable terminal inputs and attempt records are preserved as regular hardlinks. Fresh compiled objects were independently produced in each attempt and never overwrite cache symlinks. Per-attempt pre/post metadata records exact authentication counts and pinned immutable inputs inventory rather than duplicate complete inventories.'}
p=REV/(STEM+'-replay.json');require(not p.exists(),'new replay summary')
p.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'summary':str(p),'summary_sha256':sha(p),'cache_sha256':sha(cache),
 'manifest_sha256':sha(bundle/'FILES.json'),'files':len(manifest),'observations':len(observations),
 'sources':[{'module':r['module'],'source_sha256':r['source']['sha256'],'object':r['object'],
 'seconds':r['seconds']} for r in ST['records']]},indent=2))
