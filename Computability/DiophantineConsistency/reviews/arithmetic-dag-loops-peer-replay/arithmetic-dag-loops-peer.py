from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile, time

ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=ROOT/'Computability/DiophantineConsistency'
PACKET=DC/'reviews/arithmetic-dag-loops-replay.json'
RECEIPT=DC/'reviews/arithmetic-dag-loops-author.md'

def require(b,m):
    if not b: raise RuntimeError(m)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def record(p):
    p=Path(p)
    return dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
def save(p,v): p.write_text(json.dumps(v,indent=2)+'\n')
def imports(p):
    s=Path(p).read_text(); out=[]; i=0; depth=0
    while i<len(s):
        pair=s[i:i+2]
        if depth:
            if pair=='/-': depth+=1; i+=2
            elif pair=='-/': depth-=1; i+=2
            else: out.append('\n' if s[i]=='\n' else ' '); i+=1
        elif pair=='/-': depth=1; out.append(' '); i+=2
        elif pair=='--':
            while i<len(s) and s[i]!='\n': i+=1
        else: out.append(s[i]); i+=1
    require(depth==0,'unclosed comment')
    return list(dict.fromkeys(['Init']+[n for line in re.findall(
        r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M) for n in line.split()]))

require(sha(PACKET)=='26c0ebcee1bad71b6b613a4ffeda3e4e912299bfbf71679104a79421087ee0e5','packet hash')
require(sha(RECEIPT)=='9a704e1a252cff7e1b3189152ed76d610586b64ae38e1274ff41146ec3c342c3','author hash')
packet=json.loads(PACKET.read_text()); observations=[]
def check(x):
    require(sha(x['path'])==x['sha256'],'hash '+x['path'])
    observations.append(dict(path=x['path'],sha256=x['sha256']))
for p in [PACKET,RECEIPT,Path(__file__)]: check(record(p))
check(packet['inputs']); base=json.loads(Path(packet['inputs']['path']).read_text())
check(packet['driver']); check(packet['bundle_manifest']); check(packet['preflight'])
manifest_path=Path(packet['bundle_manifest']['path']); manifest=json.loads(manifest_path.read_text())
require(len(manifest)==45,'45 author artifacts')
for item in manifest:
    path=manifest_path.parent/item['path']
    check(dict(path=str(path),sha256=item['sha256']))
for attempt in packet['attempts']:
    check(attempt)
    old=json.loads(Path(attempt['path']).read_text())
    check(old['inputs'])
    old_inputs=json.loads(Path(old['inputs']['path']).read_text())
    for item in old_inputs['pins']: check(item)
check(base['cache']); audit=json.loads(Path(base['cache']['path']).read_text())
check(audit['compiler']); check(audit['audit_script'])
for item in audit['provider_records']: check(item)
modules={m['module']:m for m in audit['modules']}
require(audit['counts']==dict(custom=136,Foundation=95,source_matching_reuse=130,
    reused_artifacts=415,planned_unchanged_source_refresh=6,external=39),'exact counts')
for m in modules.values():
    check(m['source']); require(imports(m['source']['path'])==m['imports'],'header '+m['module'])
    for obj in m.get('objects',[]): check(obj)
for e in audit['external']:
    if 'path' in e: check(e)
    else:
        check(e['object'])
        for x in e['companions']: check(x)
        check(e['observed_source'])
seen=set(); boundaries=set(); active=set()
def visit(n):
    if n not in modules: boundaries.add(n); return
    if n in seen: return
    require(n not in active,'import cycle'); active.add(n)
    for k in modules[n]['imports']: visit(k)
    active.remove(n); seen.add(n)
for n in audit['direct_imports']: visit(n)
require(seen==set(modules) and boundaries=={e['module'] for e in audit['external']},'closed DAG/boundary')
expected={r['module']:r for r in packet['records']}
order=audit['refresh_order']+['BusyBeaver.ZFC.ArithmeticDagLoops','BusyBeaver.ZFC.ArithmeticDagLoopsChecks']
require(len(order)==8 and set(order)==set(expected),'eight builds')
require(all(not n.startswith('Foundation.') for n in order),'no Foundation refresh')
for n in order:
    r=expected[n]
    for key in ['source','snapshot','log','timing','object']: check(r[key])
    if n in modules:
        require(r['source']==modules[n]['source'] and not modules[n].get('objects'),'exclude old prerequisite object')
    else:
        wanted=['Init','BusyBeaver.ZFC.ArithmeticDagRun','BusyBeaver.ZFC.DagPerm'] if n.endswith('ArithmeticDagLoops') else ['Init','BusyBeaver.ZFC.ArithmeticDagLoops']
        require(imports(r['source']['path'])==wanted,'new header')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'initial reserve')
private=Path(tempfile.mkdtemp(prefix='arithmetic-dag-loops-peer-'));lib=private/'lib';lib.mkdir()
for n,m in modules.items():
    for obj in m.get('objects',[]):
        dst=lib/Path(*n.split('.')[:-1])/Path(obj['path']).name
        dst.parent.mkdir(parents=True,exist_ok=True)
        require(not dst.exists() and not dst.is_symlink(),'duplicate cache destination')
        dst.symlink_to(Path(obj['path']).resolve())
paths=base['lean_path'].split(':')[1:]
require(all('/.lake/packages/' in p or p=='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean' for p in paths),'package/toolchain paths only')
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*paths]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
inputs=dict(author_packet=record(PACKET),author_receipt=record(RECEIPT),driver=record(__file__),
    cache=base['cache'],counts=audit['counts'],modules=audit['modules'],external=audit['external'],
    expected=[expected[n] for n in order],compiler=audit['compiler'],lean_path=env['LEAN_PATH'],
    initial_observations=observations.copy())
save(private/'inputs.json',inputs)
state=dict(status='RUNNING',private=str(private),inputs=record(private/'inputs.json'),
    driver=record(__file__),records=[],scope='130 authenticated cached modules plus independent six current prerequisite rebuilds and two new leaves; no Foundation or complete closure rebuild.')
save(private/'PEER.json',state)
Path('/tmp/arithmetic-dag-loops-peer-latest').write_text(str(private)+'\n')
print('PRIVATE '+str(private)+' observations '+str(len(observations)),flush=True)
try:
    for n in order:
        require(shutil.disk_usage(private).free>=512*1024**2,'reserve before '+n)
        r=expected[n];check(r['source']);src=Path(r['source']['path'])
        snap=private/src.name;shutil.copyfile(src,snap)
        out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        require(not out.exists() and not out.is_symlink(),'fresh output '+n)
        log=private/(src.stem+'.log');timing=private/(src.stem+'.time')
        command=[audit['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)]
        print('START '+n,flush=True);start=time.monotonic()
        with log.open('w') as f:
            code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
        entry=dict(module=n,source=record(src),snapshot=record(snap),command=command,exit_code=code,
            seconds=time.monotonic()-start,log=record(log),timing=record(timing))
        state['records'].append(entry);save(private/'PEER.json',state)
        if code: print(log.read_text(),flush=True)
        require(code==0,'compile '+n)
        require(not out.is_symlink() and out.is_file(),'regular fresh object')
        check(r['source']);require(sha(src)==sha(snap),'source unchanged')
        entry['object']=record(out);entry['author_object']=r['object']
        entry['byte_identical']=sha(out)==r['object']['sha256']
        require(entry['byte_identical'],'object mismatch '+n)
        reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())
        require(not re.search(r'\b(?:error|warning):|sorryAx',log.read_text()),'diagnostic '+n)
        for name,ax in reports:
            require(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'axioms '+name)
        require(reports==r['axiom_reports'],'report mismatch '+n)
        entry['axiom_reports']=reports;save(private/'PEER.json',state)
        print(json.dumps(dict(module=n,seconds=entry['seconds'],byte_identical=True,reports=len(reports))),flush=True)
    for item in inputs['initial_observations']: check(item)
    require(shutil.disk_usage(private).free>=512*1024**2,'final reserve')
    state.update(status='PASS',final_free_bytes=shutil.disk_usage(private).free,observations=observations)
    save(private/'PEER.json',state);print('PASS '+str(private),flush=True)
except BaseException as e:
    state.update(status='FAILED',failure=str(e),observations=observations);save(private/'PEER.json',state);raise
