#!/usr/bin/env python3
"""Authenticated offline replay. Obtain the manifest SHA256 from a trusted delivery.
Authenticate this file with the external bootstrap before invoking it. No upstream
program, Lean library, literal ant schedule, or network action is executed.
"""
import argparse, hashlib, json, os, pathlib, shutil, stat, subprocess, sys
ROOT=pathlib.Path(__file__).resolve().parent

def need(ok,msg):
    if not ok: raise RuntimeError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strict_object(pairs):
    out={}
    for k,v in pairs:
        need(k not in out,'Duplicate JSON key');out[k]=v
    return out
def load(p):
    return json.loads(p.read_text(),object_pairs_hook=strict_object,parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
def snapshot(root):
    out={}
    for p in [root]+sorted(root.rglob('*')):
        s=p.lstat();need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Nonregular path '+str(p))
        out[p.relative_to(root).as_posix()]=(sha(p) if stat.S_ISREG(s.st_mode) else None,stat.S_IMODE(s.st_mode),s.st_mtime_ns)
    return out

def authenticate(expected):
    need(type(expected) is str and len(expected)==64 and all(c in '0123456789abcdef' for c in expected),'Invalid trusted manifest hash')
    mp=ROOT/'MANIFEST.json';need(mp.is_file() and not mp.is_symlink(),'Missing regular manifest')
    need(sha(mp)==expected,'Manifest SHA256 differs from trusted value')
    data=load(mp);need(set(data)=={'schema','files'},'Bad manifest fields')
    need(data['schema']=='report42-inventory-v1' and type(data['files']) is dict,'Bad manifest schema')
    actual=snapshot(ROOT);files={n for n,v in actual.items() if v[0] is not None}
    need(files==set(data['files'])|{'MANIFEST.json'},'Missing or unexpected release file')
    dirs={'.'}
    for name,entry in data['files'].items():
        p=pathlib.PurePosixPath(name)
        need(not p.is_absolute() and all(k not in ('..','.') for k in p.parts) and p.as_posix()==name,'Unsafe inventory path')
        need(set(entry)=={'sha256','bytes','mode'},'Bad inventory entry')
        need(type(entry['bytes']) is int and type(entry['mode']) is int,'Bad inventory numeric type')
        f=ROOT/name;s=f.stat()
        need(sha(f)==entry['sha256'] and s.st_size==entry['bytes'] and stat.S_IMODE(s.st_mode)==entry['mode'],'Inventory mismatch '+name)
        dirs.update(x.as_posix() for x in p.parents)
    need({n for n,v in actual.items() if v[0] is None}==dirs,'Unexpected directory')
    return data

def external_new(path):
    raw=pathlib.Path(path)
    need(not os.path.lexists(raw),'Output already exists')
    parent=raw.parent.resolve(strict=True);dest=parent/raw.name
    need(dest!=ROOT and ROOT not in dest.parents,'Output must be outside release')
    need(not os.path.lexists(dest),'Output already exists')
    return dest

def command(script,args=(),optimized=False,bridge=False):
    flags=['-I','-B']+(['-O'] if optimized else [])
    if bridge:
        launcher="import sys,runpy;sys.path.insert(0,sys.argv[1]);p=sys.argv[2];sys.argv=sys.argv[2:];runpy.run_path(p,run_name='__main__')"
        return [sys.executable,*flags,'-c',launcher,str(script.parent),str(script),*map(str,args)]
    return [sys.executable,*flags,str(script),*map(str,args)]

def run(cmd,cwd,log,expect_guard=False):
    env=dict(os.environ);env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0',LC_ALL='C.UTF-8')
    p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,timeout=240)
    log.with_suffix('.stdout').write_text(p.stdout);log.with_suffix('.stderr').write_text(p.stderr)
    if expect_guard:
        need(p.returncode!=0 and 'Optimized mode unsupported' in p.stderr and not p.stdout,'Missing optimized guard')
        return {'returncode':p.returncode,'status':'guarded rejection before scientific work'}
    need(p.returncode==0,'Replay failed '+str(log)+': '+p.stderr[-2000:])
    return json.loads(p.stdout)

def replay(target):
    target.mkdir();normal=target/'normal';normal.mkdir();optimized=target/'optimized';optimized.mkdir()
    shutil.copytree(ROOT/'science',normal/'science');shutil.copytree(ROOT/'recoder-degree',normal/'recoder-degree')
    b=normal/'science';d=b/'dilation';pair=b/'data/pair_inline-dag.json'
    sourcecopy_before=snapshot(b)
    degreecopy_before=snapshot(normal/'recoder-degree')
    records={}
    records['bridge']=run(command(b/'check_bridge.py',bridge=True),normal,normal/'bridge-check')
    need(records['bridge']==load(ROOT/'science/verification.json'),'Bridge receipt mismatch')
    records['empty']=run(command(b/'bridge_dag.py',['--full-stream'],bridge=True),normal,normal/'empty-stream')
    need({k:v for k,v in records['empty'].items() if k!='strict_constant_prefix'}==records['bridge']['full_literal_empty_dag'],'Empty stream mismatch')
    records['compose']=run(command(b/'compose_initialization.py',['--pair-dag',pair],bridge=True),normal,normal/'compose')
    need(records['compose']==load(ROOT/'science/composed_initialization_receipt.json'),'Composed receipt mismatch')
    records['composition']=run(command(b/'check_composition.py',['--pair-dag',pair],bridge=True),normal,normal/'composition-check')
    need(records['composition']==load(ROOT/'science/composition_verification.json'),'Composition check mismatch')
    dbefore=snapshot(d)
    records['dilation_normal']=run(command(d/'dilation_check.py'),normal,normal/'dilation-check')
    records['dilation_optimized']=run(command(d/'dilation_check.py',optimized=True),optimized,optimized/'dilation-check')
    need(records['dilation_normal']['result']==load(ROOT/'science/dilation/final-evidence/check_receipt.json'),'Dilation receipt mismatch')
    need(records['dilation_optimized']['result']==records['dilation_normal']['result'],'Optimized dilation differs')
    need(snapshot(d)==dbefore,'Dilation read-only verification mutated input')
    rebuilt=target/'rebuilt-dilation'
    run(command(d/'dilation_check.py',['--output-dir',rebuilt]),normal,normal/'dilation-rebuild')
    expected={p.name:sha(p) for p in (d/'final-evidence').iterdir()}
    need({p.name:sha(p) for p in rebuilt.iterdir()}==expected,'Fresh dilation evidence differs')
    records['initializer_degree']=run(command(b/'audit_degree.py',['--pair-dag',pair],bridge=True),normal,normal/'initializer-degree')
    need(records['initializer_degree']==load(ROOT/'science/degree_receipt.json'),'Initializer degree receipt mismatch')
    records['initializer_polynomial']=run(command(b/'polynomial_initialization.py',['--pair-dag',pair],bridge=True),normal,normal/'initializer-polynomial')
    need(records['initializer_polynomial']==load(ROOT/'science/polynomial_receipt.json'),'Initializer polynomial receipt mismatch')
    dc=normal/'recoder-degree/check_degree.py';evidence=d/'final-evidence'
    records['recoder_degree_normal']=run(command(dc,['--evidence',evidence]),normal,normal/'recoder-degree')
    records['recoder_degree_optimized']=run(command(dc,['--evidence',evidence],optimized=True),optimized,optimized/'recoder-degree')
    need(records['recoder_degree_normal']==load(ROOT/'recoder-degree/degree_receipt.json'),'Recoder degree receipt mismatch')
    need(records['recoder_degree_optimized']==records['recoder_degree_normal'],'Optimized degree differs')
    sourcecopy_after=snapshot(b)
    need(set(sourcecopy_before)==set(sourcecopy_after),'Isolated science inventory changed')
    for name,value in sourcecopy_before.items():
        later=sourcecopy_after[name]
        need(value[:2]==later[:2],'Isolated science bytes or modes changed: '+name)
        need(value==later,'Unexpected isolated source timestamp change: '+name)
    need(snapshot(normal/'recoder-degree')==degreecopy_before,'Degree checker source mutated')
    records['guards']={};before=snapshot(b)
    for name,args in [('bridge_dag.py',['--full-stream']),('check_bridge.py',[]),('compose_initialization.py',['--pair-dag',pair]),('check_composition.py',['--pair-dag',pair]),('audit_degree.py',['--pair-dag',pair]),('polynomial_initialization.py',['--pair-dag',pair])]:
        records['guards'][name]=run(command(b/name,args,optimized=True,bridge=True),optimized,optimized/name,expect_guard=True)
    need(snapshot(b)==before,'Optimized guarded invocations mutated input')
    return {'status':'PASS','full_initialization':records['compose'],'normal_scientific_scripts':8,'optimized_scientific_scripts':2,'optimized_guarded_rejections':6,'fresh_dilation_evidence_byte_identical':True,'upstream_or_saved_schedule_execution':False,'records':records}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--manifest-sha256',required=True);p.add_argument('--verify-only',action='store_true');p.add_argument('--output',type=pathlib.Path);a=p.parse_args()
    authenticate(a.manifest_sha256);before=snapshot(ROOT)
    if a.verify_only:
        need(a.output is None,'--verify-only does not take --output');result={'status':'PASS','authenticated_inventory':True,'files':len(load(ROOT/'MANIFEST.json')['files'])}
    else:
        need(a.output is not None,'Supply a new external --output directory');target=external_new(a.output);result=replay(target)
    need(snapshot(ROOT)==before,'Release bytes, modes or timestamps changed')
    result['release_bytes_modes_mtimes_preserved']=True
    if a.output:(target/'replay_receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
