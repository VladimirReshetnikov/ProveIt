from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT/'Computability/DiophantineConsistency'
V = D/'reviews'
observed = {}
comparisons = 0


def need(ok, message):
    if not ok: raise RuntimeError(message)


def rec(path):
    p = Path(path); b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))


def pin(x):
    global comparisons
    a = rec(x['path']); need(a['sha256'] == x['sha256'], 'hash '+x['path'])
    if 'bytes' in x: need(a['bytes'] == x['bytes'], 'size '+x['path'])
    need(a['path'] not in observed or observed[a['path']] == a, 'drift '+a['path'])
    observed[a['path']] = a; comparisons += 1
    return a


def load(path, expected):
    pin(dict(path=str(path), sha256=expected))
    return json.loads(Path(path).read_text())


def save(path, data):
    Path(path).write_text(json.dumps(data, indent=2)+'\n')


def imports(path):
    s = Path(path).read_text(); out = []; i = depth = 0
    while i < len(s):
        pair = s[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; i += 2
        elif pair == '--':
            while i < len(s) and s[i] != '\n': i += 1
        else: out.append(s[i]); i += 1
    need(depth == 0, 'balanced comments')
    s = ''.join(out)
    initial = [] if re.search(r'^\s*prelude\s*$', s, re.M) else ['Init']
    return list(dict.fromkeys(initial+[n for row in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', s, re.M) for n in row.split()]))


plan_path = D/'research/arithmetic-pell-residue-classes-cache-plan.json'
proposal_path = D/'research/arithmetic-pell-residue-classes-plan.md'
plan = load(plan_path, '542ca22a1f4f3a26ea5c987ae0c4b915d7be71275c560df8405786b97846c388')
pin(dict(path=str(proposal_path), sha256='75f3656e88aa76b1623fc93a1bc809b17780cce0299d39fe43f5b6cdb386b578'))
author = load(V/'arithmetic-pell-residue-classes-replay.json',
              'b578bdc2a2e77c0ce105e5e4efa81bd8ed5a10ba06cfd7586e26ffc75f7debac')
pin(dict(path=str(V/'arithmetic-pell-residue-classes-author.md'),
         sha256='ccf775e24e452c15f8f84947c7688c9c264085a3dac0a33990e21898d41b39ef'))
mf = load(V/'arithmetic-pell-residue-classes-author-replay/FILES.json',
          '3324e6d7b07a248f48acc58378d7703fc1fecc2bf4d3bb5e31308862f96f5d5a')
need(len(mf) == 38, 'author evidence count')
for x in mf:
    p = Path(x['path']); pin(dict(x, path=str(p if p.is_absolute() else ROOT/p)))
need(author['status'] == 'PASS' and len(author['attempts']) == 3, 'author state')
for k in ['driver', 'final_state', 'inputs', 'providers', 'authentication']: pin(author[k])
need(json.loads(Path(author['final_state']['path']).read_text())['records'] == author['records'], 'final author records')
need(plan['counts'] == dict(custom=99, Foundation=95, artifacts=384,
    external=38, external_companions=114, fresh_prerequisites=0), 'exact scope')
for x in plan['pins']: pin(x)
mods = {x['module']:x for x in plan['modules']}
ext = {x['module']:x for x in plan['external']}
seen = set(); active = set(); boundaries = set()


def visit(n):
    if n not in mods:
        need(n in ext, 'missing boundary '+n); boundaries.add(n); return
    if n in seen: return
    need(n not in active, 'cycle '+n); active.add(n)
    m = mods[n]; pin(m['source'])
    need(imports(m['source']['path']) == m['imports'], 'current header '+n)
    for x in m['objects']: pin(x)
    for k in m['imports']: visit(k)
    active.remove(n); seen.add(n)


for n in plan['direct_imports']: visit(n)
need(seen == set(mods) and boundaries == set(ext), 'exact reachable DAG')
for e in ext.values():
    pin(e['source'])
    for x in e['artifacts']: pin(x)
pin(plan['compiler'])
names = ['ArithmeticPellResidueClasses', 'ArithmeticPellResidueClassesChecks']
hashes = ['a6d523d2b60b8bd4098ab2b058dc8efff8af922f0dcd4b9c8b637b3a23c1e384',
          '480cfe347c4f8cd585a036ddf74b5fc4637e96102c2c43793ae5312f600c79ff']
sources = [pin(dict(path=str(D/'Lean/DiophantineConsistency'/(n+'.lean')), sha256=h))
           for n,h in zip(names,hashes,strict=True)]
need(imports(sources[0]['path']) == ['Init', *plan['direct_imports']], 'main imports')
need(imports(sources[1]['path']) == ['Init', 'DiophantineConsistency.'+names[0]], 'Checks imports')
need(shutil.disk_usage('/tmp').free >= 512*1024**2, 'initial reserve')
private = Path(tempfile.mkdtemp(prefix='arithmetic-pell-residue-classes-root-'))
lib = private/'lib'; logs = private/'logs'; lib.mkdir(); logs.mkdir()
for p,name in [(Path(__file__),'driver.py'),(plan_path,'plan.json'),(proposal_path,'proposal.md')]:
    shutil.copyfile(p,private/name)
for m in mods.values():
    folder = lib/Path(*m['module'].split('.')[:-1]); folder.mkdir(parents=True,exist_ok=True)
    for x in m['objects']: (folder/Path(x['path']).name).symlink_to(Path(x['path']).resolve())
lean_path = [str(lib), *plan['boundary_search']]
providers = []
for m in [*mods.values(), *ext.values()]:
    for expected in m.get('objects',m.get('artifacts')):
        relative = Path(*m['module'].split('.')[:-1])/Path(expected['path']).name
        first = next((Path(p)/relative for p in lean_path if (Path(p)/relative).is_file()), None)
        need(first is not None, 'missing artifact '+str(relative))
        providers.append(dict(module=m['module'],expected=expected,
                              actual=pin(dict(expected,path=str(first)))))
need(len(providers) == 498, 'all first artifact providers')
save(private/'providers.json', providers)
save(private/'authentication.json', list(observed.values()))
inputs = dict(plan=rec(plan_path), proposal=rec(proposal_path), counts=plan['counts'],
    sources=sources, author_packet=rec(V/'arithmetic-pell-residue-classes-replay.json'),
    compiler=plan['compiler'], LEAN_PATH=lean_path, providers=rec(private/'providers.json'),
    authentication=rec(private/'authentication.json'))
save(private/'inputs.json', inputs)
state = dict(status='RUNNING', private=str(private), driver=rec(__file__),
             inputs=rec(private/'inputs.json'), records=[])
save(private/'state.json', state)
print('PRIVATE '+str(private),flush=True)
env = dict(os.environ, LEAN_PATH=':'.join(lean_path), LEAN_NUM_THREADS='1'); env.pop('LEAN_SRC_PATH',None)
try:
    for i,(name,source) in enumerate(zip(names,sources,strict=True)):
        pin(source); need(shutil.disk_usage(private).free >= 512*1024**2, 'command reserve')
        target = lib/'DiophantineConsistency'/(name+'.olean')
        need(not target.exists() and not target.is_symlink(), 'fresh output')
        snapshot = logs/(name+'.lean'); shutil.copyfile(source['path'],snapshot)
        log = logs/(name+'.log'); timing = logs/(name+'.time')
        cmd = [plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(target),source['path']]
        print('START '+name,flush=True); start = time.monotonic()
        with log.open('w') as stream:
            code = subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=ROOT,
                                  env=env,stdout=stream,stderr=subprocess.STDOUT).returncode
        row = dict(module='DiophantineConsistency.'+name,source=source,snapshot=rec(snapshot),
            command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing))
        state['records'].append(row); save(private/'state.json',state)
        text = log.read_text(); print(text,flush=True)
        need(code == 0 and not re.search(r'\b(?:warning|error|sorryAx)\b',text),'clean compile '+name)
        need(target.is_file() and not target.is_symlink(), 'regular output')
        reports = [list(x) for x in re.findall(
            r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
        need(len(reports) == (15 if i else 0), 'report count')
        for _,axs in reports:
            need(set(re.findall(r'[A-Za-z][A-Za-z.]*',axs)) <= {'propext','Classical.choice','Quot.sound'},'axioms')
        row.update(object=rec(target),axiom_reports=reports)
        ar = author['records'][i]
        need(ar['module'] == row['module'] and ar['source']['sha256'] == source['sha256'],'author leaf')
        for k in ['source','snapshot','log','object']: pin(ar[k]); need(ar[k]['sha256'] == row[k]['sha256'],'author equality '+k)
        need(ar['axiom_reports'] == reports, 'complete author reports')
        row['author_object_and_full_log_equal'] = True
        save(private/'state.json',state); pin(source)
    for x in list(observed.values()): pin(x)
    need(shutil.disk_usage(private).free >= 512*1024**2, 'final reserve')
    state.update(status='PASS',final_free_bytes=shutil.disk_usage(private).free,
                 observations=len(observed),comparisons=comparisons)
    save(private/'state.json',state); print('PASS '+str(private),flush=True)
except BaseException as error:
    state.update(status='FAILED',failure=str(error)); save(private/'state.json',state)
    raise
