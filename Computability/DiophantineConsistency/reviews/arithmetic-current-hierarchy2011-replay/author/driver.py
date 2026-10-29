"""Exact current-source rebuild and two new hierarchy leaves; private outputs only."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys, tempfile, time

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
H = D / 'research'
B = D / 'Lean/DiophantineConsistency'
PLAN = H / 'arithmetic-current-hierarchy2011-cache-plan.json'
SUPP = H / 'arithmetic-current-hierarchy2011-current-supplement.json'
NAMES = ['ArithmeticCurrentHierarchy2011', 'ArithmeticCurrentHierarchy2011Checks']
TARGETS = ['DiophantineConsistency.' + n for n in NAMES]

def need(ok, message):
    if not ok: raise RuntimeError(message)
def rec(p):
    p = Path(p); b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))
def save(p, value):
    Path(p).write_text(json.dumps(value, indent=2) + '\n')
def guard():
    need(shutil.disk_usage('/tmp').free >= 512*1024**2, '512MiB disk reserve')
def check(x):
    y = rec(x['path'])
    need(y['sha256'] == x['sha256'], 'hash ' + x['path'])
    need('bytes' not in x or y['bytes'] == x['bytes'], 'size ' + x['path'])
    return y
def imports(path):
    raw = Path(path).read_text(); out = []; i = depth = 0
    while i < len(raw):
        two = raw[i:i+2]
        if depth:
            if two == '/-': depth += 1; i += 2
            elif two == '-/': depth -= 1; i += 2
            else: out.append('\n' if raw[i] == '\n' else ' '); i += 1
        elif two == '/-': depth = 1; i += 2
        elif two == '--':
            while i < len(raw) and raw[i] != '\n': i += 1
        else: out.append(raw[i]); i += 1
    need(depth == 0, 'balanced comments')
    text = ''.join(out)
    result = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        result.extend(line.split())
    return list(dict.fromkeys(result))

guard()
private = Path(sys.argv[1]) if len(sys.argv) == 2 else Path(tempfile.mkdtemp(prefix='current-hierarchy2011-author-'))
resume = (private/'AUTHOR.json').exists()
lib = private/'lib'; lib.mkdir(exist_ok=True)
state = json.loads((private/'AUTHOR.json').read_text()) if resume else dict(status='PREFLIGHT', private=str(private), records=[], attempts=[])
attempt = private/'attempts'/str(len(state['attempts'])+1).zfill(3)
attempt.mkdir(parents=True)
attempt_record = dict(path=str(attempt), driver=rec(__file__), started=time.time(), status='PREFLIGHT')
state['attempts'].append(attempt_record)
save(private/'AUTHOR.json', state)
shutil.copyfile(__file__, attempt/'driver.py')
Path('/tmp/current-hierarchy2011-author-location.txt').write_text(str(private)+'\n')
print('PRIVATE', private, 'ATTEMPT', len(state['attempts']), flush=True)
try:
    check(dict(path=str(PLAN), sha256='b5170702be3f9d00916436b1fe26af3edc1db2defe02303d6c0bf1e671ac1c3f'))
    check(dict(path=str(SUPP), sha256='079d66899d794f1ea17dfa1cd4ff940763b273d8e16d6032060654687ee65549'))
    metadata = [
        (H/'arithmetic-current-hierarchy2011-plan-FILES.json', '09406e1e120e1f986cef50d44cfe0304c2e4583d2dd36cfcbac1ff2ea7b34fcc'),
        (H/'arithmetic-current-hierarchy2011-read-scope-amendment.md', 'abbbeb39ad499c9d3b42605794ce4309e2961839d9cd49b007e023c9449d3499'),
        (D/'reviews/arithmetic-current-hierarchy2011-plan-peer.md', '83695876853e23e86f8962c20a3ba71af56f17406aa39331246382e0112246d6')]
    for p,h in metadata: check(dict(path=str(p),sha256=h))
    mf=json.loads(metadata[0][0].read_text())
    for x in mf['files']: check(x)
    plan=json.loads(PLAN.read_text()); supp=json.loads(SUPP.read_text())
    need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()==supp['snapshot_head'],'snapshot HEAD')
    for p in supp['comparisons']: check(p)
    for key in ['historical_snapshot','complete_diff','script']: check(supp[key])
    mods={m['module']:m for m in plan['modules']}
    mods[supp['module']]={**mods[supp['module']], 'source':supp['current_source']}
    bounds={m['module']:m for m in plan['external']}
    need(len(mods)==430 and len(plan['fresh_prerequisites'])==92 and len(plan['reused_modules'])==338,'exact module counts')
    seen=set(); active=set(); used=set(); order=[]
    def visit(n):
        if n not in mods: need(n in bounds,'unknown import '+n); used.add(n); return
        if n in seen:return
        need(n not in active,'acyclic'); active.add(n)
        check(mods[n]['source']); need(imports(mods[n]['source']['path'])==mods[n]['imports'],'header '+n)
        for child in mods[n]['imports']:visit(child)
        active.remove(n); seen.add(n); order.append(n)
    for n in plan['direct_imports']:visit(n)
    need(order==plan['topological_order'] and seen==set(mods) and used==set(bounds),'exact reachable DAG')
    for n in plan['reused_modules']:
        m=mods[n]
        for obj in m['objects']:
            check(obj)
            dest=lib/Path(*n.split('.')[:-1])/Path(obj['path']).name
            dest.parent.mkdir(parents=True,exist_ok=True)
            if not resume: need(not dest.exists() and not dest.is_symlink(),'new cached link');dest.symlink_to(Path(obj['path']).resolve())
            need(dest.is_file() and rec(dest)['sha256']==obj['sha256'],'cached link '+n)
    paths=[str(lib),*plan['boundary_search']]
    need(all('/.lake/packages/' in p or p=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean' for p in paths[1:]),'external-only fallback')
    providers=[]
    for n,m in [(n,mods[n]) for n in plan['reused_modules']]+list(bounds.items()):
        if n in bounds:check(m['source'])
        for obj in m['objects']:
            check(obj); rel=Path(*n.split('.')[:-1])/Path(obj['path']).name
            first=next((Path(p)/rel for p in paths if (Path(p)/rel).is_file()),None)
            need(first is not None and rec(first)['sha256']==obj['sha256'],'first provider '+n)
            providers.append(dict(module=n,relative=str(rel),expected=obj,actual=rec(first)))
    need(len(providers)==983,'all cached providers')
    check(plan['compiler'])
    successful={r['module']:r for r in state['records'] if r.get('status')=='PASS'}
    for row in successful.values():
        for obj in row['objects']:check(obj)
        if row['module'] not in TARGETS:check(row['source'])
    sources=[dict(module=n,**mods[n]['source']) for n in plan['fresh_prerequisites']]
    sources += [dict(module=n,**rec(B/(n.split('.')[-1]+'.lean'))) for n in TARGETS]
    need(imports(sources[-2]['path'])==['Init',*plan['direct_imports']],'target main imports')
    need(imports(sources[-1]['path'])==['Init',TARGETS[0]],'target checks imports')
    for s in sources:
        check(s)
        dst=attempt/'src'/Path(*s['module'].split('.')).with_suffix('.lean')
        dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(s['path'],dst)
        s['snapshot']=rec(dst);need(s['snapshot']['sha256']==s['sha256'],'snapshot')
    inputs=dict(plan=rec(PLAN),supplement=rec(SUPP),metadata=[rec(p) for p,_ in metadata],sources=sources,compiler=plan['compiler'],LEAN_PATH=paths,counts=plan['counts'],providers=providers)
    save(attempt/'inputs.json',inputs);attempt_record['inputs']=rec(attempt/'inputs.json')
    attempt_record['status']='RUNNING';state['status']='RUNNING';save(private/'AUTHOR.json',state)
    env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
    for s in sources:
        n=s['module']
        if n in successful:
            need(successful[n]['source']['sha256']==s['sha256'],'successful source changed '+n)
            continue
        guard();check(s);check(s['snapshot'])
        out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        for suffix in ['.olean','.olean.server','.olean.private','.ir']:
            existing=out.with_name(out.stem+suffix)
            if existing.exists() or existing.is_symlink():
                need(not existing.is_symlink(),'fresh output must not be symlink')
                previous=attempt/'previous-failed-output'/Path(*n.split('.')[:-1])/existing.name
                previous.parent.mkdir(parents=True,exist_ok=True);existing.rename(previous)
        log=attempt/(n+'.log');timing=attempt/(n+'.time')
        command=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-R',str(attempt/'src'),'-o',str(out),s['snapshot']['path']]
        row=dict(module=n,source=s,snapshot=s['snapshot'],command=command,status='RUNNING',started=time.time())
        state['records'].append(row);save(private/'AUTHOR.json',state)
        print('BUILD',n,flush=True);start=time.monotonic()
        with log.open('w') as f:
            code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
        row.update(exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing),objects=[])
        for suffix in ['.olean','.olean.server','.olean.private','.ir']:
            obj=out.with_name(out.stem+suffix)
            if obj.is_file():need(not obj.is_symlink(),'fresh regular object');row['objects'].append(rec(obj))
        row['status']='FAILED' if code else 'COMPILED';save(private/'AUTHOR.json',state)
        need(code==0,'compiler failure '+n)
        need(out.is_file() and not out.is_symlink(),'primary output')
        txt=log.read_text();need('sorryAx' not in txt and not re.search(r'\berror:',txt),'invalid diagnostics')
        reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",txt)
        row['axiom_reports']=reports;row['warnings']=re.findall(r'^.*warning:.*$',txt,re.M)
        for _,ax in reports:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'unexpected axioms')
        if n in TARGETS:
            need(not row['warnings'],'target warning')
            expected=4 if n==TARGETS[1] else 0
            need(len(reports)==expected,'target axiom report count')
        check(s);check(s['snapshot']);row['status']='PASS';save(private/'AUTHOR.json',state)
        guard();print('PASS',n,round(row['seconds'],3),'warnings',len(row['warnings']),flush=True)
    for p in supp['comparisons']:check(p)
    for row in state['records']:
        if row['status']=='PASS':
            for obj in row['objects']:check(obj)
    for s in sources:check(s);check(s['snapshot'])
    need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()==supp['snapshot_head'],'final HEAD')
    state['status']='PASS';attempt_record.update(status='PASS',finished=time.time());state['free_bytes']=shutil.disk_usage('/tmp').free
    save(private/'AUTHOR.json',state);print('PASS_ALL',private,flush=True)
except BaseException as e:
    state['status']='FAILED';attempt_record.update(status='FAILED',failure=str(e),finished=time.time())
    save(private/'AUTHOR.json',state);raise
