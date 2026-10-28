import hashlib,json,shutil,re
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
REV=D/'reviews'
OUT=Path('/tmp/validator-seed-tagged-collection222-author-3wmh9dnm')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
    if not c:raise RuntimeError(m)
def strip_comments(text):
    # Preserve newlines; nested Lean block comments and line comments are both
    # ignored before reading the import header. These sources have no imports
    # inside multiline strings before the first declaration.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            out.extend('  ')
            i += 2
        elif not depth and text.startswith('--', i):
            j = text.find('\n', i)
            j = len(text) if j == -1 else j
            out.extend(' ' * (j - i))
            i = j
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    if depth:
        raise RuntimeError('unclosed Lean block comment')
    return ''.join(out)


def imports(path):
    text = strip_comments(Path(path).read_text())
    result = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        result.extend(re.findall(r'[\w.]+', line))
    return list(dict.fromkeys(result))

last=Path((OUT/'latest-run').read_text().strip())
state=json.loads((last/'state.json').read_text())
require(state['status']=='PASS' and len(state['completed'])==2,'final pair')
data=json.loads((OUT/'inputs.json').read_text())
cache=REV/'validator-seed-tagged-collection222-cache.json'
require(sha(cache)=='377db7c77dec3e9d1570419a08aa4cd23e8b7504d14d3f6153a9d582f27a22b0','frozen cache')
for r in json.loads((last/'pins.json').read_text())+data['inherited_observations']:
    require(sha(r['path'])==r['sha256'],'final observation '+r['path'])
for r in state['completed']:
    for p,h in [(r['source'],r['source_sha256']),(r['snapshot'],r['snapshot_sha256']),
      (r['object']['path'],r['object']['sha256']),(r['log'],r['log_sha256']),
      (r['timing'],r['timing_sha256'])]:require(sha(p)==h,'final artifact '+p)
    require(not Path(r['object']['path']).is_symlink(),'regular new object')
require(Path(state['completed'][0]['log']).read_text()=='','clean main')
require(len(state['completed'][1]['axiom_reports'])==13,'thirteen audits')
require('warning:' not in Path(state['completed'][1]['log']).read_text(),'no final warning')
# Independently re-read every selected header and actual first object provider.
byname={r['module']:r for r in data['modules']}
external={r['module']:r for r in data['external']}
search=data['lean_path'].split(':')+[str(Path(data['compiler']).parent.parent/'lib/lean')]
headers=[];providers=[];seen=set();boundary=set()
def visit(n):
    if n in seen:return
    if n not in byname:
        require(n in external,'unlisted boundary '+n);boundary.add(n);return
    r=byname[n];actual=imports(r['source'])
    require(set(actual)==set(r.get('actual_imports',r['imports'])),'current header '+n)
    seen.add(n)
    headers.append({'module':n,'imports':actual,'source_sha256':sha(r['source'])})
    for x in actual:visit(x)
for n in ['ZFCinPA.ValidatorSeedGuardedComprehension222','ZFCinPA.SetCongruence']:visit(n)
require(seen==set(byname) and boundary==set(external),'exact reachable closure')
for n,r in list(byname.items())+list(external.items()):
    path=next((Path(d)/(n.replace('.','/')+'.olean') for d in search
      if (Path(d)/(n.replace('.','/')+'.olean')).is_file()),None)
    require(path is not None,'missing first provider '+n)
    obj=next(o for o in r['objects'] if o['path'].endswith('.olean')) if n in byname else r
    require(path.resolve()==Path(obj['path']).resolve() and sha(path)==obj['sha256'],'first provider '+n)
    providers.append({'module':n,'first_path':str(path),'resolved':str(path.resolve()),'sha256':sha(path)})
artifact_providers=[]
for n,r in list(byname.items())+list(external.items()):
    for obj in (r['objects'] if n in byname else [r]):
        suffix=Path(obj['path']).name[len(n.rsplit('.',1)[-1]):]
        rel=n.replace('.','/')+suffix
        path=next((Path(d)/rel for d in search if (Path(d)/rel).is_file()),None)
        require(path is not None and path.resolve()==Path(obj['path']).resolve() and sha(path)==obj['sha256'],'first artifact '+rel)
        artifact_providers.append({'module':n,'relative':rel,'first_path':str(path),'resolved':str(path.resolve()),'sha256':sha(path)})
require(len(artifact_providers)==660,'all660actualfirstartifacts')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
bundle=REV/'validator-seed-tagged-collection222-author-replay';require(not bundle.exists(),'new freeze path')
bundle.mkdir()
(bundle/'closure-reauth.json').write_text(json.dumps({'headers':headers,'first_providers':providers,'first_artifact_providers':artifact_providers,'reachable_modules':len(seen),'boundaries':len(boundary)},indent=2)+'\n')
shutil.copytree(OUT/'attempts',bundle/'attempts')
for name in ['prepare','build','freeze']:
    shutil.copy2('/tmp/seed-tagged-collection222-'+name+'.py',bundle/(name+'.py'))
shutil.copy2(OUT/'inputs.json',bundle/'inputs.json')
for r in state['completed']:shutil.copy2(r['source'],bundle/Path(r['source']).name)
for p in sorted((D/'research').glob('validator-seed-tagged-collection-*')):
    if p.is_file():shutil.copy2(p,bundle/p.name)
for p in sorted(Path('/tmp').glob('tagged-collection-repair*.py')):
    shutil.copy2(p,bundle/p.name)
for p in sorted(Path('/tmp').glob('seed-tagged-collection222-*.log')):
    shutil.copy2(p,bundle/p.name)
manifest=[]
for p in sorted(bundle.rglob('*')):
    if p.is_file():manifest.append({'path':str(p.relative_to(bundle)),'sha256':sha(p),'bytes':p.stat().st_size})
(bundle/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n')
attempts=[]
for a in sorted((OUT/'attempts').iterdir()):
    st=json.loads((a/'state.json').read_text())
    attempts.append({'path':str(a),'status':st['status'],'state_sha256':sha(a/'state.json'),
      'runs':[{'module':r['module'],'source_sha256':r['source_sha256'],'exit_code':r['exit_code'],
      'seconds':r['seconds'],'log_sha256':r['log_sha256']} for r in st['completed']]})
summary={'status':'PASS',
 'scope':'Actual all-internal finite source proof of tagged global-image Collection from concrete full-seed theory under I-Sigma1, arbitrary internally typed binary matrix/free parameters. Exact Empty(t) and t-in-a source antecedents, unrestricted support input, actual equality transport, three fixed total Sigma1 raw syntax graphs and actual source Proof certificate. No CP/GIC, Good, marker interpretation, quotient, ZF/ZFC or HA endpoint. No Sigma1 graph for the whole proof-code map.',
 'inputs':data,'input_inventory_sha256':sha(cache),
 'completed':state['completed'],'final_run':str(last),'observation_count':state['observation_count'],
 'bundle':str(bundle),'manifest_sha256':sha(bundle/'FILES.json'),
 'attempts':attempts,
 'development':'Every compiler attempt is retained with exact source snapshots, driver, pins, logs and timing. All repairs concern proof elaboration, quotation/finite-context normalization, explicit wrapper conversions and finite propositional proof search; exact details are in the author receipt and attempt logs. No import, resource cap or mathematical endpoint assumption was widened.',
 'read_scope':'The complete final main and Checks, every edited proof delta, preparation/build/freezing drivers, actual typed source proof rules, equality quotations, term/formula binders, full seed member-closure, raw augmentation, singleton, actual set equality replacement and tagged Collection contracts were fully read before their relevant execution. This author result awaits independent root review/replay.'}
p=REV/'validator-seed-tagged-collection222-replay.json';require(not p.exists(),'new summary')
p.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'summary':str(p),'summary_sha256':sha(p),'manifest_sha256':sha(bundle/'FILES.json'),
 'files':len(manifest),'observations':state['observation_count'],
 'inherited_observations':len(data['inherited_observations']),
 'sources':[{k:r[k] for k in ['module','source_sha256','seconds','object']} for r in state['completed']]},indent=2))
