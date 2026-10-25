#!/usr/bin/env python3
"""Offline normal/-O replay in isolated copies of this sealed research release.

Review code before execution. A manifest authenticates bytes, not mathematics.
No network, theorem enumeration, machine simulation or consistency search runs.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, platform, shutil, stat, subprocess, sys, tempfile, zipfile
ROOT=Path(__file__).resolve().parent

def need(value,message):
    if not value: raise ValueError(message)
def digest(raw):return hashlib.sha256(raw).hexdigest()
def safe(name):
    p=PurePosixPath(name)
    need(name and name!='.' and p.as_posix()==name and not p.is_absolute() and '..' not in p.parts and '\\' not in name and ':' not in name,'unsafe portable path: '+name)
    return p
def inventory(root):
    out={}
    for p in root.rglob('*'):
        need(not p.is_symlink(),'symlink in release: '+str(p))
        if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc':
            rel=p.relative_to(root).as_posix();safe(rel)
            if rel!='MANIFEST.json':out[rel]=p
    return out
def verify_manifest(root):
    data=json.loads((root/'MANIFEST.json').read_text());rows={}
    for row in data['files']:
        safe(row['path']);need(row['path'] not in rows,'duplicate manifest entry');rows[row['path']]=row
    actual=inventory(root);need(set(rows)==set(actual),'manifest inventory differs')
    for rel,p in actual.items():
        raw=p.read_bytes();need(len(raw)==rows[rel]['bytes'] and digest(raw)==rows[rel]['sha256'],'manifest mismatch: '+rel)
    return {'status':'PASS','files':len(rows),'bytes':sum(r['bytes'] for r in rows.values()),'manifest_sha256':digest((root/'MANIFEST.json').read_bytes())}
def verify_prior(root):
    old=root/'prior/wave16';rows=json.loads((old/'MANIFEST.json').read_text())['files']
    for row in rows:
        safe(row['path']);raw=(old/row['path']).read_bytes()
        need(len(raw)==row['bytes'] and digest(raw)==row['sha256'],'prior source mismatch: '+row['path'])
    return {'status':'PASS','files':len(rows),'scope':'Exact preceding release inventory. Historical programs are inert during this replay.'}
def verify_code(root):
    records=json.loads((root/'CODE_REVIEW.json').read_text())['files']
    for r in records:
        safe(r['path']);need(digest((root/r['path']).read_bytes())==r['sha256'],'reviewed code changed: '+r['path'])
    return {'status':'PASS','files':len(records)}
def verify_zip(root,path):
    with zipfile.ZipFile(path) as z:
        names=z.namelist();need(len(set(names))==len(names),'duplicate ZIP names')
        for info in z.infolist():
            safe(info.filename);need(not stat.S_ISLNK(info.external_attr>>16),'ZIP symlink')
        need(z.testzip() is None,'ZIP CRC error')
        prefix=root.name+'/';expected={prefix+n for n in inventory(root)}|{prefix+'MANIFEST.json'}
        need(set(names)==expected,'ZIP inventory differs')
        for name in names:need(z.read(name)==(root/name[len(prefix):]).read_bytes(),'ZIP byte mismatch: '+name)
    return {'status':'PASS','members':len(names),'bytes':Path(path).stat().st_size,'sha256':digest(Path(path).read_bytes())}
def controls(tree,temp):
    outcomes=[]
    targets=json.loads((tree/'REPRODUCE_PLAN.json').read_text())['negative_control_targets']
    safe(targets['equation']);safe(targets['coefficient'])
    victim=tree/targets['equation'];original=victim.read_bytes()
    for label,action in [('changed equation',lambda:victim.write_bytes(original+b' ')),('missing equation',lambda:victim.unlink())]:
        action()
        try:verify_manifest(tree)
        except (ValueError,FileNotFoundError):outcomes.append({'control':label,'status':'REJECTED'})
        else:raise ValueError('accepted '+label)
        finally:victim.write_bytes(original)
    victim=tree/targets['coefficient'];original=victim.read_bytes();victim.write_bytes(original[:-1]+bytes([original[-1]^1]))
    try:verify_manifest(tree)
    except ValueError:outcomes.append({'control':'changed coefficient payload','status':'REJECTED'})
    else:raise ValueError('accepted coefficient corruption')
    finally:victim.write_bytes(original)
    for bad in ['../escape','/absolute','C:/drive','a\\b']:
        try:safe(bad)
        except ValueError:outcomes.append({'control':'unsafe path '+bad,'status':'REJECTED'})
        else:raise ValueError('accepted unsafe path')
    zip_path=temp/'crc-control.zip'
    with zipfile.ZipFile(zip_path,'w',zipfile.ZIP_STORED) as z:z.writestr('control.txt',b'known CRC control payload')
    raw=bytearray(zip_path.read_bytes())
    with zipfile.ZipFile(zip_path) as z:
        i=z.getinfo('control.txt');offset=i.header_offset+30+len(i.filename.encode())+len(i.extra)
    raw[offset]^=1;zip_path.write_bytes(raw)
    with zipfile.ZipFile(zip_path) as z:need(z.testzip()=='control.txt','CRC control not detected')
    outcomes.append({'control':'corrupted stored ZIP member','status':'REJECTED'})
    return outcomes
def run_mode(tree,mode,plan,logs):
    prefix=[sys.executable,'-B']+(['-O'] if mode=='optimized' else [])
    env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONPATH',None);env.pop('PYTHONOPTIMIZE',None)
    commands=[];compared=[]
    def expand(value):return value.replace('{mode}',mode).replace('{mode_upper}',mode.upper()).replace('{check_suffix}','_OPTIMIZED' if mode=='optimized' else '')
    for rel in plan['rebuild_files']:
        rel=expand(rel);safe(rel);(tree/rel).unlink()
    for number,step in enumerate(plan['commands'],1):
        args=[expand(v) for v in step['args']];safe(args[0])
        if step.get('cwd'):safe(step['cwd'])
        command_root=tree/step.get('cwd','.')
        need((command_root/args[0]).is_file(),'missing command')
        work=tree
        if step.get('cwd'):
            safe(step['cwd']);work=tree/step['cwd']
        result=subprocess.run(prefix+args,cwd=work,env=env,capture_output=True,timeout=step.get('timeout_seconds',1200))
        log=f'{mode}_{number:02}.txt';(logs/log).write_bytes(result.stdout+b'\n--- STDERR ---\n'+result.stderr)
        need(result.returncode==0,'command failed: '+str(args)+'\n'+result.stderr.decode(errors='replace'))
        commands.append({'arguments':args,'returncode':0,'stdout_sha256':digest(result.stdout),'stderr_sha256':digest(result.stderr),'log':log})
        if step.get('stdout_reference'):
            rel=expand(step['stdout_reference']);safe(rel)
            need(result.stdout==(ROOT/rel).read_bytes(),'stdout differs: '+rel);compared.append(rel)
        print(mode+': '+' '.join(args)+' -> PASS',flush=True)
    for rel in plan['compare_files']:
        rel=expand(rel)
        safe(rel);need((tree/rel).read_bytes()==(ROOT/rel).read_bytes(),'regenerated file differs: '+rel);compared.append(rel)
    # The exact coefficient files and inherited reference packet remain unchanged.
    payloads=[]
    for rel,p in inventory(ROOT).items():
        if 'coefficients' in PurePosixPath(rel).parts:
            need((tree/rel).read_bytes()==p.read_bytes(),'coefficient changed: '+rel);payloads.append(rel)
    verify_prior(tree)
    return {'status':'PASS','commands':commands,'exact_byte_comparisons':sorted(set(compared)),'unchanged_coefficient_files':len(payloads)}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--archive',type=Path);ap.add_argument('--verify-only',action='store_true');ap.add_argument('--receipt',type=Path);a=ap.parse_args()
    receipt=(a.receipt or ROOT.parent/(ROOT.name+'_replay')/'REPRODUCE_CHECK.json').resolve()
    need(not receipt.is_relative_to(ROOT),'receipt must be outside release');receipt.parent.mkdir(parents=True,exist_ok=True)
    out={'schema':'round17_offline_replay_v1','status':'RUNNING','python':platform.python_version(),'scope':'Exact finite algebra, literal transcription, degree certificates, source integrity, deterministic replay and negative controls. Not a proof of consistency or a fresh transitive kernel theorem.'}
    out['manifest']=verify_manifest(ROOT);out['prior']=verify_prior(ROOT);out['reviewed_code']=verify_code(ROOT)
    if a.archive:out['archive']=verify_zip(ROOT,a.archive)
    if not a.verify_only:
        import sympy
        out['sympy']=sympy.__version__;plan=json.loads((ROOT/'REPRODUCE_PLAN.json').read_text())
        pinned=plan['environment_for_exact_receipt_bytes']
        need(platform.python_version()==pinned['python'] and sympy.__version__==pinned['sympy'],'exact receipt replay requires Python '+pinned['python']+' and SymPy '+pinned['sympy'])
        logs=receipt.parent/(receipt.stem+'_logs');logs.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='conzfc-round17-') as td:
            temp=Path(td)
            for mode in ['normal','optimized']:
                tree=temp/mode
                shutil.copytree(ROOT,tree,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
                verify_manifest(tree)
                if mode=='normal':out['negative_controls']=controls(tree,temp)
                out[mode]=run_mode(tree,mode,plan,logs)
    out['manifest_after']=verify_manifest(ROOT);out['status']='PASS'
    receipt.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'PASS','receipt':str(receipt)},indent=2))
if __name__=='__main__':main()
