from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
PLAN = DC / 'research/arithmetic-pell-first-index-cache-plan.json'
PROPOSAL = DC / 'research/arithmetic-pell-first-index-proposal.md'
observations = {}


def require(ok, message):
    if not ok: raise RuntimeError(message)


def record(path):
    p = Path(path); data = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def check(pin):
    actual = record(pin['path'])
    require(actual['sha256'] == pin['sha256'], 'hash: '+pin['path'])
    if 'bytes' in pin: require(actual['bytes'] == pin['bytes'], 'size: '+pin['path'])
    observations[actual['path']] = actual
    return actual


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2)+'\n')


def imports(path):
    text = Path(path).read_text(); out=[]; i=depth=0
    while i<len(text):
        pair=text[i:i+2]
        if depth:
            if pair=='/-': depth+=1; i+=2
            elif pair=='-/': depth-=1; i+=2
            else: out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif pair=='/-': depth=1; i+=2
        elif pair=='--':
            while i<len(text) and text[i]!='\n': i+=1
        else: out.append(text[i]); i+=1
    require(depth==0,'comment balance')
    clean=''.join(out)
    initial=[] if re.search(r'^\s*prelude\s*$',clean,re.M) else ['Init']
    return list(dict.fromkeys(initial+[n for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',clean,re.M)
        for n in line.split()]))


AP=DC/'reviews/arithmetic-pell-first-index-replay.json'
check(dict(path=str(AP),sha256='5fedfc6a25af2ed24729fc5e07ddc5145d582f69cfdb912b0ee91ce633235e00'))
author=json.loads(AP.read_text());require(author['status']=='PASS','author PASS')
check(dict(path=str(DC/'reviews/arithmetic-pell-first-index-author.md'),sha256='fb5e9ed4aeca84ddcaf16947a1543e6f517eeea015207f0ce6dbcfe4f00d3ef6'))
mf=author['manifest'];check(mf)
require(mf['sha256']=='c158488bfa2194420ea7e00fe806373972fea14046fb660e097d349401342b69','frozen manifest')
rows=json.loads(Path(mf['path']).read_text());require(len(rows)==44,'44 evidence files')
for row in rows:check(dict(row,path=str(ROOT/row['path'])))
for row in author['records']:
    require(row['exit_code']==0,'successful author leaf')
    for key in ['source','snapshot','object','log','timing']:check(row[key])

for attempt in author['attempts']:
    check(attempt['state']);check(attempt['durable'])
    old=json.loads(Path(attempt['state']['path']).read_text())
    for row in old['records']:
        for key in ['snapshot','log','timing']:check(row[key])
        if 'object'in row:check(row['object'])

check(dict(path=str(PLAN),sha256='0dd6cb70b70619b87f1c9986a1f6f3bc6c37d76bb575e461e19c21dafc7bc3a1'))
check(dict(path=str(PROPOSAL),sha256='c4dd423c70e19d0a303f8182b1c77d2815808c76b094303bce216322927c3940'))
plan=json.loads(PLAN.read_text())
require(plan['counts']==dict(custom=108,Foundation=95,artifacts=393,external=38,
    boundary_artifacts=114,boundary_primaries=38,boundary_companions=76,actual_first_providers=507,fresh_prerequisites=0),'scope')
for pin in plan['pins']: check(pin)
plan_manifest=DC/'research/arithmetic-pell-first-index-plan-FILES.json'
check(dict(path=str(plan_manifest),sha256='361f9bf9d83ef43bd671b146aeb890c2ac7c3bb099a96a2c8fbd8450e4e0534e'))
for pin in json.loads(plan_manifest.read_text()):check(dict(pin,path=str(ROOT/pin['path'])))
modules={x['module']:x for x in plan['modules']}

boundary={x['module'] for x in plan['external']}
visited=set(); active=set(); edges=set()


def visit(name):
    if name not in modules:
        require(name in boundary,'unknown boundary '+name); edges.add(name); return
    if name in visited: return
    require(name not in active,'cycle '+name); active.add(name)
    item=modules[name]; check(item['source'])
    require(imports(item['source']['path'])==item['imports'],'header '+name)
    for obj in item['objects']: check(obj)
    for dep in item['imports']: visit(dep)
    active.remove(name); visited.add(name)


for name in plan['direct_imports']: visit(name)
require(visited==set(modules) and edges==boundary,'exact DAG')
for item in plan['external']:
    check(item['source'])
    for obj in item['artifacts']: check(obj)
check(plan['compiler'])
names=['ArithmeticPellFirstIndex','ArithmeticPellFirstIndexChecks']
sources=[check(record(DC/('Lean/DiophantineConsistency/'+n+'.lean'))) for n in names]
require(imports(sources[0]['path'])==['Init',*plan['direct_imports']],'main imports')
require(imports(sources[1]['path'])==['Init','DiophantineConsistency.'+names[0]],'checks imports')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'initial reserve')
private=Path(tempfile.mkdtemp(prefix='arithmetic-pell-first-index-root-'))
lib=private/'lib'; logs=private/'logs'; lib.mkdir(); logs.mkdir()
shutil.copyfile(__file__,private/'driver.py')
shutil.copyfile(PLAN,private/'plan.json')
shutil.copyfile(PROPOSAL,private/'proposal.md')
for source in sources: shutil.copyfile(source['path'],logs/Path(source['path']).name)
for item in plan['modules']:
    folder=lib/Path(item['module'].replace('.','/')).parent
    folder.mkdir(parents=True,exist_ok=True)
    for obj in item['objects']:
        (folder/Path(obj['path']).name).symlink_to(Path(obj['path']).resolve())
lean_path=[str(lib),*plan['boundary_search']]
require(all('/.lake/packages/'in p or p=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'for p in lean_path[1:]),'package-only fallback')
providers=[]
for item in plan['modules']+plan['external']:
    for expected in item.get('objects',item.get('artifacts')):
        rel=Path(*item['module'].split('.')[:-1])/Path(expected['path']).name
        actual=next((Path(root)/rel for root in lean_path if (Path(root)/rel).is_file()),None)
        require(actual is not None,'missing provider '+str(rel))
        providers.append(dict(module=item['module'],expected=expected,
            actual=check(dict(expected,path=str(actual)))))
require(len(providers)==507,'all first providers')
save(private/'providers.json',providers)
save(private/'authentication.json',dict(pins=list(observations.values())))
inputs=dict(plan=record(PLAN),proposal=record(PROPOSAL),counts=plan['counts'],sources=sources,
    compiler=plan['compiler'],LEAN_PATH=lean_path,providers=record(private/'providers.json'),
    authentication=record(private/'authentication.json'))
save(private/'inputs.json',inputs)
state=dict(status='RUNNING',private=str(private),driver=record(__file__),inputs=record(private/'inputs.json'),records=[])
save(private/'state.json',state)
with Path('/tmp/arithmetic-pell-first-index-root-runs.txt').open('a') as stream:
    stream.write(str(private)+'\n')
env=dict(os.environ,LEAN_PATH=':'.join(lean_path),LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH',None)
print('PRIVATE '+str(private),flush=True)
try:
    for name,source in zip(names,sources):
        check(source)
        require(shutil.disk_usage(private).free>=512*1024**2,'command reserve')
        output=lib/'DiophantineConsistency'/(name+'.olean')
        output.parent.mkdir(parents=True,exist_ok=True)
        require(not output.exists() and not output.is_symlink(),'fresh output')
        snapshot=logs/(name+'.lean'); shutil.copyfile(source['path'],snapshot)
        log=logs/(name+'.log'); timing=logs/(name+'.time')
        command=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(output),source['path']]
        print('START '+name,flush=True); start=time.monotonic()
        with log.open('w') as stream:
            code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],cwd=ROOT,env=env,
                stdout=stream,stderr=subprocess.STDOUT).returncode
        rec=dict(module='DiophantineConsistency.'+name,source=source,snapshot=record(snapshot),
            command=command,exit_code=code,seconds=time.monotonic()-start,log=record(log),timing=record(timing))
        state['records'].append(rec); save(private/'state.json',state)
        print(log.read_text(),flush=True)
        require(code==0,'compile '+name)
        require(not re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text()),'clean diagnostics '+name)
        reports=[list(x) for x in re.findall(
            r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())]
        for theorem,axioms in reports:
            require(set(re.findall('[A-Za-z][A-Za-z.]*',axioms))<=
                {'propext','Classical.choice','Quot.sound'},'standard axioms '+theorem)
        require(len(reports)==(5 if name.endswith('Checks') else 0),'report count')
        require(output.is_file() and not output.is_symlink(),'regular output')
        rec.update(object=record(output),axiom_reports=reports)
        expected=next(r for r in author['records'] if r['module']==rec['module'])
        for key in ['source','object','log']:
            require(rec[key]['sha256']==expected[key]['sha256'],'author matching '+key)
        require(reports==expected['axiom_reports'],'all report equality')
        rec['author_object_and_full_log_equal']=True
        save(private/'state.json',state); check(source)
    for pin in list(observations.values()): check(pin)
    require(shutil.disk_usage(private).free>=512*1024**2,'final reserve')
    state.update(status='PASS',final_free_bytes=shutil.disk_usage(private).free,
        final_observed_paths=len(observations))
    save(private/'state.json',state); print('PASS '+str(private),flush=True)
except BaseException as error:
    state.update(status='FAILED',failure=str(error)); save(private/'state.json',state)
    raise
