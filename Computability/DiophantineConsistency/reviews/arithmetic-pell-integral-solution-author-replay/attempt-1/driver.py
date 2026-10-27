from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
PLAN = DC / 'research/arithmetic-pell-integral-solution-cache-plan.json'
PROPOSAL = DC / 'research/arithmetic-pell-integral-solution-plan.md'
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


check(dict(path=str(PLAN),sha256='27b365f34e47feeaaaa6e32c3987ed2cebbb3a6e333673c4d4717b52b3afcee2'))
check(dict(path=str(PROPOSAL),sha256='a99ddd196895b3dfabf41a976d9628e69481c308ab0dcef31a7abdcfda7e98a8'))
plan=json.loads(PLAN.read_text())
require(plan['counts']==dict(custom=101,Foundation=95,artifacts=386,external=38,
    boundary_artifacts=114,boundary_primaries=38,boundary_companions=76,fresh_prerequisites=0),'scope')
for pin in plan['pins']: check(pin)
SUPPLEMENT = DC / 'research/arithmetic-pell-integral-solution-accepted-strong-divisibility.json'
check(dict(path=str(SUPPLEMENT),sha256='05fefd83261e8d29c8dd652190f92e0f952f049cfad6cc9f00dbfd1509168aa9'))
supplement=json.loads(SUPPLEMENT.read_text())
for pin in supplement['pins']: check(pin)
require(supplement['original_plan']==record(PLAN),'original plan unchanged')
modules={x['module']:x for x in plan['modules']}
accepted=modules[supplement['module']]
require(accepted['source']==supplement['source'] and accepted['objects']==[supplement['old_object']],
    'one accepted supplement')
check(supplement['accepted_object'])
accepted['objects']=[supplement['accepted_object']]
accepted['provenance']='ROOT accepted provider supplement; original frozen plan preserved'

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
names=['ArithmeticPellIntegralSolution','ArithmeticPellIntegralSolutionChecks']
sources=[check(record(DC/('Lean/DiophantineConsistency/'+n+'.lean'))) for n in names]
require(imports(sources[0]['path'])==['Init',*plan['direct_imports']],'main imports')
require(imports(sources[1]['path'])==['Init','DiophantineConsistency.'+names[0]],'checks imports')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'initial reserve')
private=Path(tempfile.mkdtemp(prefix='arithmetic-pell-integral-solution-author-'))
lib=private/'lib'; logs=private/'logs'; lib.mkdir(); logs.mkdir()
shutil.copyfile(__file__,private/'driver.py')
shutil.copyfile(PLAN,private/'plan.json')
shutil.copyfile(PROPOSAL,private/'proposal.md')
shutil.copyfile(SUPPLEMENT,private/'accepted-strong-divisibility.json')
for source in sources: shutil.copyfile(source['path'],logs/Path(source['path']).name)
for item in plan['modules']:
    folder=lib/Path(item['module'].replace('.','/')).parent
    folder.mkdir(parents=True,exist_ok=True)
    for obj in item['objects']:
        (folder/Path(obj['path']).name).symlink_to(Path(obj['path']).resolve())
lean_path=[str(lib),*plan['boundary_search']]
providers=[]
for item in plan['modules']+plan['external']:
    for expected in item.get('objects',item.get('artifacts')):
        rel=Path(*item['module'].split('.')[:-1])/Path(expected['path']).name
        actual=next((Path(root)/rel for root in lean_path if (Path(root)/rel).is_file()),None)
        require(actual is not None,'missing provider '+str(rel))
        providers.append(dict(module=item['module'],expected=expected,
            actual=check(dict(expected,path=str(actual)))))
require(len(providers)==500,'all first providers')
save(private/'providers.json',providers)
save(private/'authentication.json',dict(pins=list(observations.values())))
inputs=dict(plan=record(PLAN),proposal=record(PROPOSAL),accepted_supplement=record(SUPPLEMENT),counts=plan['counts'],sources=sources,
    compiler=plan['compiler'],LEAN_PATH=lean_path,providers=record(private/'providers.json'),
    authentication=record(private/'authentication.json'))
save(private/'inputs.json',inputs)
state=dict(status='RUNNING',private=str(private),driver=record(__file__),inputs=record(private/'inputs.json'),records=[])
save(private/'state.json',state)
with Path('/tmp/arithmetic-pell-integral-solution-author-runs.txt').open('a') as stream:
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
        save(private/'state.json',state); check(source)
    for pin in list(observations.values()): check(pin)
    require(shutil.disk_usage(private).free>=512*1024**2,'final reserve')
    state.update(status='PASS',final_free_bytes=shutil.disk_usage(private).free,
        final_observed_paths=len(observations))
    save(private/'state.json',state); print('PASS '+str(private),flush=True)
except BaseException as error:
    state.update(status='FAILED',failure=str(error)); save(private/'state.json',state)
    raise
