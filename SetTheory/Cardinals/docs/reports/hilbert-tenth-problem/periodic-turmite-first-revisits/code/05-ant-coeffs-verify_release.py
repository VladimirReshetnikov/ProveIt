#!/usr/bin/env python3
"""Authenticated isolated replay for Report47. Authenticate externally first."""
import argparse,hashlib,json,os,pathlib,shutil,stat,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parent

def need(p,m):
    if not p:raise RuntimeError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strict_object(pairs):
    out={}
    for k,v in pairs:
        need(k not in out,'Duplicate JSON key');out[k]=v
    return out
def load(p):return json.loads(p.read_text(),object_pairs_hook=strict_object,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
def snapshot(root):
    out={}
    for p in [root]+sorted(root.rglob('*')):
        s=p.lstat();need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Unsafe nonregular path: '+str(p))
        out[p.relative_to(root).as_posix()]=(sha(p) if stat.S_ISREG(s.st_mode) else None,stat.S_IMODE(s.st_mode),s.st_mtime_ns)
    return out

def authenticate(expected):
    need(type(expected)is str and len(expected)==64 and all(c in '0123456789abcdef' for c in expected),'Invalid trusted manifest hash')
    p=ROOT/'MANIFEST.json';need(p.is_file() and not p.is_symlink(),'Missing regular manifest')
    need(sha(p)==expected,'Manifest SHA256 differs from trusted value')
    data=load(p);need(set(data)=={'schema','files'} and data['schema']=='report47-inventory-v1' and type(data['files'])is dict,'Bad manifest schema')
    actual=snapshot(ROOT);files={n for n,v in actual.items() if v[0] is not None}
    need(files==set(data['files'])|{'MANIFEST.json'},'Missing or unexpected release file')
    dirs={'.'}
    for name,e in data['files'].items():
        q=pathlib.PurePosixPath(name)
        need(not q.is_absolute() and all(x not in ('..','.') for x in q.parts) and q.as_posix()==name,'Unsafe inventory path')
        need(set(e)=={'sha256','bytes','mode'} and type(e['bytes'])is int and type(e['mode'])is int,'Bad inventory entry')
        f=ROOT/name;s=f.stat();need(sha(f)==e['sha256'] and s.st_size==e['bytes'] and stat.S_IMODE(s.st_mode)==e['mode'],'Inventory mismatch: '+name)
        dirs.update(x.as_posix() for x in q.parents)
    need({n for n,v in actual.items() if v[0] is None}==dirs,'Unexpected directory')
    return data

def external_new(raw):
    raw=pathlib.Path(raw);need(not os.path.lexists(raw),'Output already exists')
    parent=raw.parent.resolve(strict=True);out=parent/raw.name
    need(out!=ROOT and ROOT not in out.parents,'Output must be external to release')
    need(not os.path.lexists(out),'Output already exists');return out

def command(script,args=(),optimized=False,local_import=False):
    flags=['-I','-B']+(['-O'] if optimized else [])
    if local_import:
        launch="import sys,runpy;sys.path.insert(0,sys.argv[1]);p=sys.argv[2];sys.argv=sys.argv[2:];runpy.run_path(p,run_name='__main__')"
        return [sys.executable,*flags,'-c',launch,str(script.parent),str(script),*map(str,args)]
    return [sys.executable,*flags,str(script),*map(str,args)]

def run(cmd,cwd,log,guard=False):
    env=dict(os.environ);env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0',LC_ALL='C.UTF-8')
    p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,timeout=1800)
    log.with_suffix('.stdout').write_text(p.stdout);log.with_suffix('.stderr').write_text(p.stderr)
    if guard:
        need(p.returncode!=0 and 'Optimized Python' in p.stderr and not p.stdout,'Missing early optimized-mode guard')
        return {'status':'guarded rejection before scientific work','returncode':p.returncode}
    need(p.returncode==0,'Replay failed: '+str(log)+'\n'+p.stderr[-2000:]);return p.stdout

def audit_command(script,science,out,mode):
    # Import the authenticated checker unchanged and rebind only documented path
    # globals; its original bytes, functions, validation logic and hash remain.
    launch = """import importlib.util,sys
from pathlib import Path
p=Path(sys.argv[1]);s=Path(sys.argv[2]);o=Path(sys.argv[3]);mode=sys.argv[4]
spec=importlib.util.spec_from_file_location('verified_independent_audit',p)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.HERE=o
if mode=='profiles':
 m.ROOT=s/'data/recipe_assets';m.PROFILES=s/'geometry/profiles';m.run()
elif mode=='prefix':
 m.NEW=s;m.ASSETS=s/'data/recipe_assets';m.ANCHOR=s/'data/anchor_patch.json';m.PROFILES=s/'geometry/profiles';m.main()
elif mode=='join':
 m.RELEASE=s;m.main()
else:raise ValueError(mode)
"""
    return [sys.executable,'-I','-B','-c',launch,str(script),str(science),str(out),mode]

def replay(target):
    need(__debug__,'Optimized Python is not allowed for scientific replay')
    target.mkdir();work=target/'science';shutil.copytree(ROOT/'science',work)
    # This old independent sink expects the receipt in its prototype root.
    # Add an exact receipt alias only to the isolated, disposable copy.
    shutil.copy2(work/'verification/full-prefix-receipt.json',work/'full-prefix-receipt.json')
    before=snapshot(work);records={}
    prefix=target/'fresh-prefix.json'
    records['prefix']=json.loads(run(command(work/'full_prefix.py',['--assets',work/'data/recipe_assets','--anchor',work/'data/anchor_patch.json','--out',prefix,'--digest'],local_import=True),target,target/'prefix'))
    expected=load(ROOT/'science/verification/full-prefix-receipt.json')
    # The provenance pin keys contain absolute paths and must change on relocation.
    for key in expected:
        if key=='pins':continue
        need(records['prefix'][key]==expected[key],'Prefix receipt differs: '+key)
    expected_hashes=sorted(expected['pins'].values())
    need(sorted(records['prefix']['pins'].values())==expected_hashes,'Relocated prefix input pin contents differ')
    joined=target/'fresh-joined.json'
    records['joined']=json.loads(run(command(work/'join_strict.py',['--out',joined],local_import=True),target,target/'joined'))
    need(records['joined']==load(ROOT/'science/verification/joined-strict-receipt.json'),'Joined source receipt differs')
    generated=target/'generated-profiles'
    records['generated_profiles']=json.loads(run(command(work/'geometry/build_profiles.py',['--out',generated],local_import=True),target,target/'profiles-build'))
    original=ROOT/'science/geometry/profiles'
    need({p.name for p in generated.iterdir()}=={p.name for p in original.iterdir()},'Profile generated file inventory differs')
    for p in original.iterdir():need(p.read_bytes()==(generated/p.name).read_bytes(),'Generated profile bytes differ: '+p.name)
    audit=work/'verification/independent-prefix-audit';records['independent']={}
    for mode,script,receipt in [('profiles','check_profiles.py','profiles-receipt.json'),('prefix','check_emitted_source.py','emitted-source-receipt.json'),('join','check_join_independent.py','joined-independent-receipt.json')]:
        out=target/('independent-'+mode);out.mkdir()
        result=json.loads(run(audit_command(audit/script,work,out,mode),target,target/('independent-'+mode)))
        need(result==load(ROOT/'science/verification/independent-prefix-audit'/receipt),'Independent audit differs: '+mode)
        records['independent'][mode]=result
    need(snapshot(work)==before,'Replay mutated scientific source copy')
    return {'status':'PASS','authenticated_isolated_replay':True,'records':records,'all_profile_artifacts_byte_identical':True,'independent_checker_bytes_unchanged':True,'independent_relocation':'Only documented path globals rebound; no checker source edits','upstream_physical_recipe_or_saved_schedule_execution':False,'owned_report44_generator_reused':True}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--manifest-sha256',required=True);p.add_argument('--verify-only',action='store_true');p.add_argument('--output',type=pathlib.Path);a=p.parse_args()
    data=authenticate(a.manifest_sha256);before=snapshot(ROOT)
    if a.verify_only:
        need(a.output is None,'--verify-only takes no output');r={'status':'PASS','authenticated_inventory':True,'files':len(data['files'])}
    else:
        need(a.output is not None,'Supply a fresh external --output directory');target=external_new(a.output);r=replay(target)
    need(snapshot(ROOT)==before,'Release bytes/modes/mtimes changed');r['release_bytes_modes_mtimes_preserved']=True
    if a.output:(target/'replay_receipt.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(r,indent=2,sort_keys=True))
if __name__=='__main__':main()
