#!/usr/bin/env python3
"""Compile the focused semantic-coverage refactor against a pinned ProveIt tree.

No existing project object is used. Incremental retries bind the entire
transitive source/import closure as well as each direct dependency object.
This checks KSim and typed compatibility clients, not the K215 endpoint.
"""
from pathlib import Path
import argparse, fcntl, hashlib, importlib.util, json, os, re, subprocess, time

def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def value_digest(v): return hashlib.sha256(json.dumps(v, sort_keys=True).encode()).hexdigest()
def save(p, v): p.write_text(json.dumps(v, indent=2) + '\n')

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo', type=Path, help='ProveIt checkout; omit to use bundled checked-sources')
parser.add_argument('--lean', type=Path, required=True)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
repo = args.repo.resolve() if args.repo else None
out, lean = args.out.resolve(), args.lean.resolve()
here = Path(__file__).resolve().parent
if repo:
    driver = repo/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py'
    spec = importlib.util.spec_from_file_location('maintained_builder', driver)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    mod.TARGET = 'BusyBeaver.ZFC.KSim'
    inv = mod.inventory(repo)
    base_commit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
else:
    manifest = json.loads((here/'evidence/source-manifest.json').read_text())
    for row in manifest:
        assert digest(here/row['path']) == row['sha256'], ('Changed snapshot', row['path'])
    inv = {'modules':[dict(row,source=str(here/row['path'])) for row in manifest
                     if row['module'] != 'SemanticCoverageAudit'], 'external_imports':['Init']}
    base_commit = json.loads((here/'evidence/metrics.json').read_text())['base_commit']
out.mkdir(parents=True, exist_ok=True)
work = out/'workspace'; work.mkdir(exist_ok=True)
logs = out/'logs'; logs.mkdir(exist_ok=True)
env = dict(os.environ, LEAN_PATH=str(work), LEAN_NUM_THREADS='1')
records = []
lockpath = Path('/tmp/proveit-k215-proof-build.lock')
with lockpath.open('a+') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
identity = {'version':version, 'binary_sha256':digest(lean),
            'library_sha256':digest(lean.parent.parent/'lib/lean/libleanshared.so'),
            'Init_olean_sha256':digest(lean.parent.parent/'lib/lean/Init.olean')}
if (out/'toolchain.json').exists():
    assert json.loads((out/'toolchain.json').read_text()) == identity
else: save(out/'toolchain.json', identity)

def compile_one(name, source, imports):
    dest = work/(name.replace('.','/')+'.lean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(source.read_bytes())
    deps = {r['module']: {'source_closure':r['source_closure'], 'object_sha256':r['object_sha256']}
            for r in records if r['module'] in imports}
    source_closure = value_digest({'source':digest(dest), 'imports':imports, 'dependencies':deps})
    obj=dest.with_suffix('.olean')
    base={'module':name, 'source_sha256':digest(dest), 'imports':imports,
          'source_closure':source_closure, 'dependencies':deps}
    recpath=logs/(name+'.json')
    if recpath.exists():
        old=json.loads(recpath.read_text())
        if (all(old.get(k)==v for k,v in base.items()) and old.get('status')=='PASS'
                and obj.exists() and old['object_sha256']==digest(obj)
                and (logs/old['log']).is_file() and old['log_sha256']==digest(logs/old['log'])):
            records.append(old); print('REUSE',name,flush=True); return
    index=len(list(logs.glob(name+'.attempt*.log')))+1
    logfile=logs/(name+f'.attempt{index}.log')
    sourcecopy=logs/(name+f'.attempt{index}.lean'); sourcecopy.write_bytes(dest.read_bytes())
    cmd=[str(lean),'-j1','-M8192','--root='+str(work),'-o',str(obj),str(dest)]
    print('CHECK',name,flush=True)
    with lockpath.open('a+') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        start=time.monotonic()
        with logfile.open('wb') as log:
            proc=subprocess.run(cmd,cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600)
        seconds=time.monotonic()-start
    rec=dict(base,status='PASS' if proc.returncode==0 else 'FAIL',exit_code=proc.returncode,
             seconds=seconds,command=cmd,log=logfile.name,log_sha256=digest(logfile))
    if proc.returncode==0: rec['object_sha256']=digest(obj)
    save(recpath,rec)
    print(rec['status'],name,round(seconds,3),flush=True)
    if proc.returncode:
        print(logfile.read_text()); raise SystemExit(proc.returncode)
    records.append(rec)

for row in inv['modules']:
    name=row['module']
    source=here/'candidate'/(name.replace('.','/')+'.lean')
    if not source.exists(): source=Path(row['source'])
    compile_one(name,source,row['imports'])

compile_one('SemanticCoverageAudit',here/'SemanticCoverageAudit.lean',['BusyBeaver.ZFC.KSim'])
audit_text=(logs/records[-1]['log']).read_text()
axioms = {word.strip() for block in re.findall(r'depends on axioms: \[(.*?)\]',audit_text,re.S)
          for word in block.split(',') if word.strip()}
assert axioms <= {'propext','Classical.choice','Quot.sound'}, axioms
assert audit_text.count('depends on axioms:') + audit_text.count('does not depend on any axioms') == 12
assert 'warning:' not in audit_text
save(out/'verification.json',{'status':'PASS','scope':'KSim source closure and semantic/old-API typed audit only',
    'base_commit':base_commit,
    'toolchain':identity,'modules':records,'external_imports':inv['external_imports'],
    'project_module_count':len(inv['modules']),'typed_clients':1})
print('COMPLETE',len(inv['modules']),'project modules and semantic/compatibility audit',flush=True)
