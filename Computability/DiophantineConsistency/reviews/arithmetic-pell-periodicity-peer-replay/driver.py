from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT/'Computability/DiophantineConsistency'
REV = DC/'reviews'
PLAN = DC/'research/arithmetic-pell-periodicity-cache-plan.json'
PACKET = REV/'arithmetic-pell-periodicity-replay.json'
MANIFEST = REV/'arithmetic-pell-periodicity-author-replay/FILES.json'
RECEIPT = REV/'arithmetic-pell-periodicity-author.md'
observations = []

def rec(p):
    p = Path(p)
    return dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest(), bytes=p.stat().st_size)

def require(ok, msg):
    if not ok:
        raise RuntimeError(msg)

def save(p, obj):
    Path(p).write_text(json.dumps(obj, indent=2)+'\n')

def check(r):
    actual = rec(r['path'])
    require(actual['sha256']==r['sha256'], 'hash '+r['path'])
    if 'bytes' in r:
        require(actual['bytes']==r['bytes'], 'size '+r['path'])
    observations.append(actual)
    return actual

def guard():
    require(shutil.disk_usage('/tmp').free>=512*1024**2, '512 MiB reserve')

def imports(p):
    s=Path(p).read_text(); out=[]; i=depth=0
    while i<len(s):
        pair=s[i:i+2]
        if depth:
            if pair=='/-': depth+=1; i+=2
            elif pair=='-/': depth-=1; i+=2
            else: out.append('\n' if s[i]=='\n' else ' '); i+=1
        elif pair=='/-': depth=1; i+=2
        elif pair=='--':
            while i<len(s) and s[i]!='\n': i+=1
        else: out.append(s[i]); i+=1
    require(depth==0, 'balanced comments')
    s=''.join(out)
    names=[] if re.search(r'^\s*prelude\s*$',s,re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M):
        names.extend(line.split())
    return list(dict.fromkeys(names))

guard()
private=Path(tempfile.mkdtemp(prefix='arithmetic-pell-periodicity-controller-peer-'))
lib=private/'lib'; lib.mkdir()
state=dict(status='PREFLIGHT',private=str(private),driver=rec(__file__),records=[])
save(private/'PEER.json',state)
marker=Path('/tmp/arithmetic-pell-periodicity-controller-peer-attempts.json')
attempts=json.loads(marker.read_text()) if marker.exists() else []
attempts.append(str(private)); save(marker,attempts)
shutil.copyfile(__file__,private/'driver.py')
print('PRIVATE',private,flush=True)
try:
    for p,h in [(PLAN,'cf4cb17c055461bfcf7977b5e7ff3b1c2e4ab3f362ceedd6a12264cc8c552238'),
                (PACKET,'a6a7c5f47e3b36748213b4f3b31e6c6aa18c710a03b1b758f3576be97192ad26'),
                (MANIFEST,'85235f722a77322ad687ff847a130f828cfc68010d5cb7186464f40067b23fa0'),
                (RECEIPT,'acf00e1102c1d99f0554ab0c39f51129358a4c0c0a852243d8ec439957290580')]:
        check(dict(path=str(p),sha256=h))
    for item in json.loads(MANIFEST.read_text()):
        check(dict(item,path=str(ROOT/item['path'])))
    author=json.loads(PACKET.read_text()); plan=json.loads(PLAN.read_text())
    require(author['status']=='PASS', 'author PASS')
    for key in ['plan','proposal','inputs','providers','authentication','compiler']:
        check(author[key])
    for a in author['attempts']:
        check(a['state'])
        prior=json.loads(Path(a['state']['path']).read_text())
        for row in prior['records']:
            require(row['snapshot']['sha256']==row['source']['sha256'],'prior source snapshot')
            for key in ['snapshot','object','log','timing']:
                if key in row: check(row[key])
    for row in author['records']:
        for key in ['source','snapshot','object','log','timing']: check(row[key])
    counts=dict(custom=98,Foundation=95,artifacts=383,external=38,external_companions=114,fresh_prerequisites=0)
    require(plan['counts']==author['counts']==counts,'counts')
    for pin in plan['pins']: check(pin)
    mods={r['module']:r for r in plan['modules']}
    edge={r['module']:r for r in plan['external']}
    require(len(mods)==98 and sum(n.startswith('Foundation.') for n in mods)==95,'module counts')
    require(sum(len(r['objects']) for r in mods.values())==383 and len(edge)==38,'artifact counts')
    require(sum(len(r['artifacts']) for r in edge.values())==114,'boundary artifacts')
    for n,r in mods.items():
        check(r['source']); require(imports(r['source']['path'])==r['imports'],'header '+n)
        for obj in r['objects']: check(obj)
    for r in edge.values():
        check(r['source'])
        for obj in r['artifacts']: check(obj)
    seen=set(); external=set()
    def visit(n):
        if n not in mods:
            require(n in edge,'unknown import '+n); external.add(n); return
        if n in seen: return
        seen.add(n)
        for k in mods[n]['imports']: visit(k)
    for n in plan['direct_imports']: visit(n)
    require(seen==set(mods) and external==set(edge),'exact reachable DAG')
    for n,r in mods.items():
        for obj in r['objects']:
            dest=lib/Path(*n.split('.')[:-1])/Path(obj['path']).name
            dest.parent.mkdir(parents=True,exist_ok=True)
            require(not dest.exists(),'duplicate target')
            dest.symlink_to(Path(obj['path']).resolve())
    paths=[str(lib),*plan['boundary_search']]
    require(all('/.lake/packages/' in p or p=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean' for p in paths[1:]),'no shared project cache')
    providers=[]
    for n,r in {**mods,**edge}.items():
        for obj in r.get('objects',r.get('artifacts',[])):
            rel=Path(*n.split('.')[:-1])/Path(obj['path']).name
            first=next((Path(p)/rel for p in paths if (Path(p)/rel).is_file()),None)
            require(first is not None and rec(first)['sha256']==obj['sha256'],'first provider '+n)
            providers.append(dict(module=n,actual=rec(first),expected=obj))
    sources=[r['source'] for r in author['records']]
    require(imports(sources[0]['path'])==['Init',*plan['direct_imports']],'main import')
    require(imports(sources[1]['path'])==['Init',sources[0]['module']],'Checks import')
    require(all(s['module'] not in mods for s in sources),'targets excluded')
    check(plan['compiler'])
    save(private/'inputs.json',dict(plan=rec(PLAN),author=rec(PACKET),manifest=rec(MANIFEST),
        receipt=rec(RECEIPT),modules=plan['modules'],external=plan['external'],counts=counts,
        compiler=plan['compiler'],LEAN_PATH=paths,sources=sources,pins=list(observations),providers=providers))
    state.update(status='RUNNING',counts=counts,inputs=rec(private/'inputs.json'),preflight_observations=len(observations))
    save(private/'PEER.json',state)
    env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
    for source,expected,old in zip(sources,[0,10],author['records']):
        guard();check(source)
        n=source['module'];short=n.split('.')[-1]
        out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        require(not out.exists() and not out.is_symlink(),'fresh output')
        snapshot=private/(short+'.lean');shutil.copyfile(source['path'],snapshot)
        log=private/(short+'.log');timing=private/(short+'.time')
        command=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),source['path']]
        start=time.monotonic()
        with log.open('w') as f:
            code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
        row=dict(module=n,source=source,snapshot=rec(snapshot),command=command,exit_code=code,
            seconds=time.monotonic()-start,log=rec(log),timing=rec(timing))
        state['records'].append(row);save(private/'PEER.json',state)
        require(code==0,'compile '+n)
        require(out.is_file() and not out.is_symlink(),'regular output')
        text=log.read_text();require(not re.search(r'\b(?:error|warning|sorryAx)\b',text),'diagnostics')
        reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
        require(len(reports)==expected,'report count')
        for _,axs in reports:
            require(set(re.findall(r'[A-Za-z][A-Za-z.]*',axs))<={'propext','Classical.choice','Quot.sound'},'axioms')
        row.update(object=rec(out),axiom_reports=reports,
            object_byte_identical=rec(out)['sha256']==old['object']['sha256'],
            log_byte_identical=rec(log)['sha256']==old['log']['sha256'],
            reports_identical=[list(x) for x in reports]==old['axiom_reports'])
        check(source);guard();save(private/'PEER.json',state)
        print('PASS',n,round(row['seconds'],3),'object identical',row['object_byte_identical'],flush=True)
    for pin in list({x['path']:x for x in observations}.values()):check(pin)
    save(private/'observations.json',observations)
    state.update(status='PASS',observations=len(observations),distinct_paths=len({r['path'] for r in observations}),
        authentication=rec(private/'observations.json'),free_bytes=shutil.disk_usage('/tmp').free)
    save(private/'PEER.json',state);print('PASS',private,flush=True)
except BaseException as e:
    state.update(status='FAILED',failure=str(e));save(private/'PEER.json',state);raise
