#!/usr/bin/env python3
"""Check a selected Lean import closure in an isolated object directory.

Project objects are reused only when compiler, source, and every transitive
source/import fingerprint agree. This is a targeted check, not an endpoint
audit. All sources come from a pinned checkout plus explicit overlay roots.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import os
import re
import signal
import subprocess
import time

ROOTS = ('Computability/BusyBeaver/Lean', 'Logic/FirstOrder/Lean',
         'SetTheory/ZF/Lean', 'SetTheory/BoundedConsistency/Lean')

def digest(data):
    return hashlib.sha256(data).hexdigest()

def sha(path):
    return digest(Path(path).read_bytes())

def clean(text):
    # Preserve newlines while excluding nested comments and quoted strings.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1; i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1; i += 2
        elif depth:
            if text[i] == '\n': out.append('\n')
            i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i); i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\': i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
        else:
            out.append(text[i]); i += 1
    if depth: raise ValueError('Unclosed comment')
    return ''.join(out)

def save(path, data):
    tmp = path.with_suffix('.tmp')
    tmp.write_text(json.dumps(data, indent=2) + '\n')
    tmp.replace(path)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--lean', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--overlay', type=Path, action='append', default=[])
    ap.add_argument('--reuse', type=Path, action='append', default=[])
    ap.add_argument('--target', action='append', required=True)
    ap.add_argument('--timeout', type=float, default=900)
    ap.add_argument('--lock', type=Path, default=Path('/tmp/proveit-k215-proof-build.lock'))
    args = ap.parse_args()
    repo, out, lean = args.repo.resolve(), args.out.resolve(), args.lean.resolve()
    out.mkdir(parents=True, exist_ok=True)
    objdir, logdir = out/'objects', out/'logs'
    objdir.mkdir(exist_ok=True); logdir.mkdir(exist_ok=True)
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    shared = lean.parent.parent/'lib/lean/libleanshared.so'
    compiler = {'version': version, 'binary_sha256': sha(lean), 'shared_sha256': sha(shared)}
    roots = [p.resolve() for p in args.overlay] + [repo/p for p in ROOTS]
    rows, done, active = [], {}, set()
    external = set()
    def visit(mod):
        if mod in done: return done[mod]['transitive_source_sha256']
        if mod in active: raise ValueError(('Import cycle', mod))
        relative = Path(mod.replace('.', '/')+'.lean')
        found = [(r, r/relative) for r in roots if (r/relative).is_file()]
        if not found:
            if mod.split('.')[0] not in ('Init', 'Lean', 'Std', 'Lake'):
                raise ValueError(('Unbound project import',mod))
            external.add(mod)
            return digest(json.dumps([compiler,mod],sort_keys=True).encode())
        root, source = found[0]
        imports = [m for x in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)',clean(source.read_text())) for m in x.split()]
        active.add(mod)
        deps = [(m,visit(m)) for m in imports]
        active.remove(mod)
        ss = sha(source)
        transitive = digest(json.dumps([mod,ss,deps,compiler],sort_keys=True).encode())
        row = {'module':mod,'source':str(source),'source_root':str(root),
               'source_sha256':ss,'imports':imports,'transitive_source_sha256':transitive}
        done[mod]=row; rows.append(row)
        return transitive
    for mod in args.target: visit(mod)
    candidates = {}
    existing = out/'verification.json'
    reuse_files = [p.resolve()/'verification.json' for p in args.reuse]
    if existing.exists(): reuse_files.append(existing)
    for path in reuse_files:
        data=json.loads(path.read_text())
        if data.get('compiler') != compiler: continue
        for row in data.get('modules',[]):
            if row.get('status') in ('PASS','REUSED'):
                candidates[(row['module'],row['transitive_source_sha256'])]=row
    record = {'kind':'targeted Lean source-closure check','repo':str(repo),
              'commit':subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
              'compiler':compiler,'targets':args.target,'external_imports':sorted(external),
              'overlay_roots':[str(p.resolve()) for p in args.overlay],
              'modules':[],'status':'RUNNING'}
    env=os.environ.copy(); env['LEAN_PATH']=str(objdir); env['LEAN_NUM_THREADS']='1'
    started=time.monotonic()
    for row in rows:
        relative=Path(row['module'].replace('.','/'))
        obj=objdir/relative.with_suffix('.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
        old=candidates.get((row['module'],row['transitive_source_sha256']))
        if old and old.get('artifacts') and all(Path(x['path']).is_file() and sha(x['path'])==x['sha256'] for x in old['artifacts']):
            artifacts=[]
            for x in old['artifacts']:
                src=Path(x['path']); dst=obj.parent/src.name
                if src.resolve()!=dst.resolve():
                    if dst.exists() or dst.is_symlink(): dst.unlink()
                    dst.symlink_to(src.resolve())
                artifacts.append({'path':str(dst),'sha256':x['sha256']})
            row.update(status='REUSED',artifacts=artifacts,origin_log=old.get('log',old.get('origin_log')))
            print('REUSED',row['module'],flush=True)
        else:
            # Never overwrite an immutable provider via an old reuse symlink.
            for x in obj.parent.glob(relative.name+'.*'):
                if x.is_symlink(): x.unlink()
            attempt=1+len(list(logdir.glob(row['module']+'.*.log')))
            log=logdir/(row['module']+f'.{attempt:03d}.log')
            cmd=[str(lean),'-j1','-M8192','--root='+row['source_root'],'-o',str(obj),row['source']]
            t=time.monotonic(); timed_out=False
            with args.lock.open('a+') as lock:
                fcntl.flock(lock,fcntl.LOCK_EX)
                with log.open('wb') as stream:
                    process=subprocess.Popen(cmd,env=env,cwd=row['source_root'],stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
                    try: code=process.wait(timeout=args.timeout)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid,signal.SIGKILL); process.wait(); code=process.returncode; timed_out=True
                    except BaseException:
                        os.killpg(process.pid,signal.SIGKILL); process.wait(); raise
            artifacts=[{'path':str(p),'sha256':sha(p)} for p in sorted(obj.parent.glob(relative.name+'.*')) if p.is_file()]
            row.update(status='PASS' if code==0 else 'FAIL',exit_code=code,timed_out=timed_out,
                       seconds=time.monotonic()-t,command=cmd,log=str(log),log_sha256=sha(log),artifacts=artifacts)
            print(row['status'],row['module'],round(row['seconds'],3),flush=True)
            if code:
                print(log.read_text()[-12000:],flush=True)
        record['modules'].append(row); save(existing,record)
        if row['status']=='FAIL':
            record['status']='FAIL'; record['seconds']=time.monotonic()-started; save(existing,record); return 1
    record['status']='PASS'; record['seconds']=time.monotonic()-started; save(existing,record)
    print('PASS',len(rows),'modules',round(record['seconds'],3),'seconds',flush=True)
    return 0

if __name__=='__main__':
    raise SystemExit(main())
