#!/usr/bin/env python3
"""Read-only replay of this pinned own-code scientific packet.
Never invokes recipe-assets code, upstream Lean, or saved ant schedules.
"""
if not __debug__:raise RuntimeError('Optimized replay wrapper unsupported')
import argparse,hashlib,json,os,pathlib,stat,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parent

def obj(pairs):
    out={}
    for k,v in pairs:
        if k in out:raise ValueError('Duplicate JSON key')
        out[k]=v
    return out

def nofloat(x):raise ValueError('Nonfinite JSON constant')
def read_json(text):return json.loads(text,object_pairs_hook=obj,parse_constant=nofloat)
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)
def verify_manifest():
    manifest_path=ROOT/'MANIFEST.json'
    if not stat.S_ISREG(manifest_path.lstat().st_mode):raise ValueError('Manifest must be a regular file')
    manifest=read_json(manifest_path.read_text());files=manifest['files']
    actual=set()
    for p in ROOT.rglob('*'):
        mode=p.lstat().st_mode
        if stat.S_ISLNK(mode):raise ValueError('Symlink in source tree')
        if stat.S_ISDIR(mode):continue
        if not stat.S_ISREG(mode):raise ValueError('Nonregular entry in source tree')
        if p!=manifest_path:actual.add(p.relative_to(ROOT).as_posix())
    if actual!=set(files):raise ValueError('Source inventory mismatch')
    for rel,entry in files.items():
        q=pathlib.PurePosixPath(rel)
        if q.is_absolute() or '..' in q.parts or str(q)!=rel:raise ValueError('Unsafe manifest path')
        if type(entry['bytes']) is not int or entry['bytes']<0:raise ValueError('Invalid byte count')
        b=(ROOT/rel).read_bytes()
        if len(b)!=entry['bytes'] or hashlib.sha256(b).hexdigest()!=entry['sha256']:raise ValueError('Source hash mismatch: '+rel)
    # The included compact recipe assets are authenticated, never executed.
    assets=read_json((ROOT/'recipe_assets/ASSET_MANIFEST.json').read_text())
    for record in assets['files']:
        b=(ROOT/'recipe_assets'/record['path']).read_bytes()
        if hashlib.sha256(b).hexdigest()!=record['recipe_asset_sha256'] or len(b)!=record['recipe_asset_bytes']:raise ValueError('Recipe asset mismatch')
    return len(files),hashlib.sha256((ROOT/'MANIFEST.json').read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--verify-only',action='store_true');a=p.parse_args()
    n,pin=verify_manifest()
    if a.verify_only:
        print(json.dumps({'status':'PASS_HASHES','files':n,'manifest_sha256':pin},indent=2));return
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env.pop('PYTHONOPTIMIZE',None)
    pair=str(ROOT/'data/pair_inline-dag.json')
    commands=[('check_bridge.py',[],'verification.json',False),('bridge_dag.py',['--full-stream'],'full_empty_dag_receipt.json',False),('compose_initialization.py',['--pair-dag',pair],'composed_initialization_receipt.json',False),('check_composition.py',['--pair-dag',pair],'composition_verification.json',False),('audit_degree.py',['--pair-dag',pair],'degree_receipt.json',False),('polynomial_initialization.py',['--pair-dag',pair],'polynomial_receipt.json',False),('dilation/dilation_check.py',['--verify-dir',str(ROOT/'dilation/final-evidence')],'dilation/final-evidence/check_receipt.json',True)]
    results=[]
    with tempfile.TemporaryDirectory(prefix='literal-ant-init-replay-') as temporary:
        for name,args,expected,unwrap in commands:
            got=subprocess.run([sys.executable,'-B',str(ROOT/name),*args],cwd=temporary,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=180,check=True)
            data=read_json(got.stdout)
            if unwrap:data=data['result']
            if canonical(data)!=canonical(read_json((ROOT/expected).read_text())):raise ValueError('Receipt mismatch: '+name)
            results.append({'script':name,'status':'PASS_EXACT_RECEIPT'})
        # Guard checks execute only our own entry points and must fail before work.
        guards=[]
        for name in ['bridge_dag.py','check_bridge.py','compose_initialization.py','check_composition.py','audit_degree.py','polynomial_initialization.py']:
            got=subprocess.run([sys.executable,'-B','-O',str(ROOT/name),'--help'],cwd=temporary,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=15)
            if got.returncode==0 or 'Optimized mode unsupported' not in got.stderr:raise ValueError('Optimization guard absent: '+name)
            guards.append(name)
        # The separately authored recoder intentionally supports optimized mode.
        got=subprocess.run([sys.executable,'-B','-O',str(ROOT/'dilation/dilation_check.py'),'--verify-dir',str(ROOT/'dilation/final-evidence')],cwd=temporary,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=180,check=True)
        if canonical(read_json(got.stdout)['result'])!=canonical(read_json((ROOT/'dilation/final-evidence/check_receipt.json').read_text())):raise ValueError('Optimized recoder receipt mismatch')
    if verify_manifest()!=(n,pin):raise ValueError('Source tree changed during replay')
    print(json.dumps({'status':'PASS_READ_ONLY_REPLAY','files':n,'manifest_sha256':pin,'commands':results,'optimized_rejections':guards,'optimized_recoder':'PASS_EXACT_RECEIPT','recipe_assets_executed':False,'upstream_code_executed':False,'saved_ant_schedule_executed':False},indent=2))
if __name__=='__main__':main()
