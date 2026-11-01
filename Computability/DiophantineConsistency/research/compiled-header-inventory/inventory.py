#!/usr/bin/env python3
"""Rate-limited compiled-header object inventory; not source or runtime provenance."""
from collections import deque
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import select
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
READER = HERE/'stream_imports.lean'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SUFFIXES = ('.olean','.olean.private','.olean.server','.ir','.ilean',
            '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
HEADERS = ('.olean','.olean.server','.olean.private','.ir')
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")

class Throttle:
    def __init__(self, bytes_per_second):
        if bytes_per_second <= 0: raise ValueError('positive byte rate required')
        self.rate=bytes_per_second;self.next_time=time.monotonic();self.bytes=0
    def read(self, count):
        self.bytes += count
        self.next_time=max(self.next_time,time.monotonic())+count/self.rate
        delay=self.next_time-time.monotonic()
        if delay>0: time.sleep(delay)

def hash_file(path, throttle=None):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):
            h.update(block)
            if throttle: throttle.read(len(block))
    return h.hexdigest()

def meta(path):
    if not os.path.lexists(path): return None
    if not path.is_file(): raise RuntimeError(('broken or non-file artifact',str(path)))
    s=path.stat()
    return {'realpath':str(path.resolve(strict=True)),'device':s.st_dev,'inode':s.st_ino,
            'size':s.st_size,'mtime_ns':s.st_mtime_ns,'ctime_ns':s.st_ctime_ns}

def inspect(path, throttle=None):
    before=meta(path)
    if before is None: return None
    value=hash_file(path,throttle)
    if meta(path)!=before: raise RuntimeError(('artifact changed while hashing',str(path)))
    return {'metadata':before,'sha256':value}

def guard_metadata(entries):
    for name,item in entries.items():
        if meta(Path(name)) != (None if item is None else item['metadata']):
            raise RuntimeError(('artifact metadata changed',name))

def guard_full(entries,throttle=None):
    for name,item in entries.items():
        if inspect(Path(name),throttle)!=item:
            raise RuntimeError(('artifact changed',name))

def marker(root, top, throttle=None):
    directory=root/top; top_file=root/(top+'.olean')
    if os.path.lexists(directory) and not directory.exists():
        raise RuntimeError(('broken namespace directory',str(directory)))
    return {'directory':str(directory.resolve(strict=True)) if directory.is_dir() else None,
            'file':inspect(top_file,throttle)}

def root_observation(path):
    if not path.is_absolute(): raise RuntimeError(('relative search root',str(path)))
    if os.path.lexists(path):
        if not path.is_dir(): raise RuntimeError(('invalid or broken search root',str(path)))
        return {'present':True,'realpath':str(path.resolve(strict=True))}
    return {'present':False,'realpath':str(path.resolve(strict=False))}

class Reader:
    def __init__(self, env):
        self.errors=tempfile.TemporaryFile(mode='w+t')
        self.process=subprocess.Popen([str(LEAN),'-j1','--run',str(READER)],env=env,
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=self.errors,text=True,bufsize=1)
    def read(self,paths):
        if len(paths)!=4 or paths[0] is None: raise RuntimeError('invalid artifact group')
        values=['-' if path is None else str(path) for path in paths]
        if any(any(c in value for c in ('\n','\r','\t')) for value in values):
            raise RuntimeError(('unsupported artifact path',values))
        self.process.stdin.write('\t'.join(values)+'\n');self.process.stdin.flush()
        ready,_,_=select.select([self.process.stdout],[],[],300)
        if not ready: raise RuntimeError(('reader timeout',values[0]))
        line=self.process.stdout.readline()
        parts=line.rstrip('\n').split('\t')
        if len(parts)!=5 or parts[0]!='OK': raise RuntimeError(('invalid reader output',values[0],line))
        result={}
        for suffix,path,part in zip(HEADERS,paths,parts[1:]):
            if path is None:
                if part!='-':raise RuntimeError(('unexpected part output',suffix,part))
                continue
            flag,sep,names=part.partition(':')
            if not sep or flag not in ('true','false'):raise RuntimeError(('bad part output',suffix,part))
            imports=names.split(',') if names else []
            if any(not NAME.fullmatch(n) for n in imports):raise RuntimeError(('unsupported import name',suffix,imports))
            result[suffix]={'is_module':flag=='true','imports':imports}
        return result
    def close(self,success):
        if success:
            self.process.stdin.close()
            code=self.process.wait(timeout=30)
            remaining=self.process.stdout.read()
            self.errors.seek(0);errors=self.errors.read()
            if code or remaining or errors:
                raise RuntimeError(('reader terminal failure',code,remaining,errors))
        else:
            if self.process.poll() is None:
                self.process.terminate()
                try:self.process.wait(timeout=5)
                except subprocess.TimeoutExpired:self.process.kill();self.process.wait()
        self.errors.close()

def collect(seeds, policy, *, max_modules, bytes_per_second, progress_every=100):
    if not seeds or max_modules<=0: raise ValueError('nonempty seeds and positive module limit required')
    roots=[Path(r['path']) for r in policy['roots']]
    root_observations=[root_observation(p) for p in roots]
    if not roots or len({x['realpath'] for x in root_observations})!=len(roots):
        raise RuntimeError('empty or duplicate search roots')
    roles=[r['role'] for r in policy['roots']]
    if any(not role for role in roles): raise RuntimeError('empty search-root role')
    throttle=Throttle(bytes_per_second)
    baseline={'reader':hash_file(READER),'lean':hash_file(LEAN),'driver':hash_file(Path(__file__))}
    env=dict(os.environ,LEAN_NUM_THREADS='1')
    for key in ('LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
        env.pop(key,None)
    reader=Reader(env);success=False
    namespaces, artifacts, visited = {},{},{}
    pending=deque(dict.fromkeys(seeds));queued=set(pending)
    try:
        while pending and len(visited)<max_modules:
            name=pending.popleft();queued.remove(name)
            if name in visited: continue
            if not NAME.fullmatch(name): raise RuntimeError(('unsupported module name',name))
            top=name.split('.')[0]
            if top not in namespaces:
                marks=[marker(root,top,throttle) for root in roots]
                selected=next((i for i,x in enumerate(marks) if x['directory'] is not None or x['file'] is not None),None)
                if selected is None: raise RuntimeError(('unknown namespace',top))
                namespaces[top]={'selected':selected,'markers':marks}
            idx=namespaces[top]['selected'];obj=roots[idx].joinpath(*name.split('.')).with_suffix('.olean')
            stem=str(obj)[:-6]
            group={stem+s:inspect(Path(stem+s),throttle) for s in SUFFIXES}
            if group[str(obj)] is None: raise RuntimeError(('selected namespace lacks object',name,str(obj)))
            for path,item in group.items():
                if path in artifacts and artifacts[path]!=item: raise RuntimeError(('conflicting artifact observation',path))
                artifacts[path]=item
            paths=[Path(stem+suffix) if group[stem+suffix] is not None else None for suffix in HEADERS]
            guard_metadata(group);headers=reader.read(paths);guard_metadata(group)
            if headers['.olean']['is_module'] and ('.olean.private' not in headers or '.olean.server' not in headers):
                raise RuntimeError(('missing module object part',name))
            imports=sorted({n for row in headers.values() for n in row['imports']})
            visited[name]={'root':idx,'role':roles[idx],'path':str(obj),'imports':imports,'headers':headers}
            for dep in imports:
                if dep not in visited and dep not in queued:pending.append(dep);queued.add(dep)
            if progress_every and len(visited)%progress_every==0:
                print('PROGRESS',len(visited),'pending',len(pending),'bytes_hashed',throttle.bytes,flush=True)
        reader.close(True);success=True
        guard_full(artifacts,throttle)
        for top,observation in namespaces.items():
            if [marker(root,top,throttle) for root in roots]!=observation['markers']:
                raise RuntimeError(('namespace search changed',top))
        if [root_observation(root) for root in roots]!=root_observations:
            raise RuntimeError('search root presence or resolution changed')
        if baseline!={'reader':hash_file(READER),'lean':hash_file(LEAN),'driver':hash_file(Path(__file__))}:
            raise RuntimeError('reader, Lean or driver changed')
        return {'status':'COMPILED_HEADER_SURVEY' if not pending else 'PARTIAL_COMPILED_HEADERS',
                'seeds':seeds,'roots':[{'path':str(p),'role':r} for p,r in zip(roots,roles)],
                'root_observations':root_observations,
                'tool_sha256':baseline,'modules':visited,'artifacts':artifacts,
                'namespace_observations':namespaces,'frontier':list(pending),'max_modules':max_modules,
                'rate_bytes_per_second':bytes_per_second,'hash_bytes':throttle.bytes,
                'scope':'Point-in-time compiled .olean/private/server/IR header closure and object identity inventory. '
                        'It does not establish source-to-object provenance, runtime loads, dynamic libraries, '
                        'toolchain correctness or absence of transient mutation.'}
    finally:
        if not success:reader.close(False)

def main():
    p=argparse.ArgumentParser();p.add_argument('--policy',type=Path,required=True)
    p.add_argument('--seed',action='append',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--max-modules',type=int,default=5000);p.add_argument('--bytes-per-second',type=int,default=2*1024*1024)
    a=p.parse_args()
    if a.output.exists() or a.output.is_symlink():raise ValueError('refusing to overwrite output')
    identity=hash_file(a.policy)
    result=collect(a.seed,json.loads(a.policy.read_text()),max_modules=a.max_modules,bytes_per_second=a.bytes_per_second)
    if hash_file(a.policy)!=identity:raise RuntimeError('policy changed')
    result['policy_sha256']=identity
    with a.output.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(result['status'],len(result['modules']),'frontier',len(result['frontier']),hash_file(a.output),flush=True)

if __name__=='__main__':main()
