#!/usr/bin/env python3
"""Real Lean and mutation controls for the streaming object-header inventory."""
import os
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch
import inventory as inv

def reject(fn, reason):
    try: fn()
    except RuntimeError as exc:
        if reason not in str(exc): raise AssertionError((reason,str(exc)))
    else: raise AssertionError(('accepted invalid input',reason))

def compile_file(root,name,text):
    src=root.joinpath(*name.split('.')).with_suffix('.lean');obj=src.with_suffix('.olean')
    src.parent.mkdir(parents=True,exist_ok=True);src.write_text(text)
    env=dict(os.environ,LEAN_PATH=str(root),LEAN_NUM_THREADS='1')
    p=subprocess.run([str(inv.LEAN),'-j1','--root='+str(root),str(src),'-o',str(obj)],
                     env=env,capture_output=True,text=True,timeout=120)
    if p.returncode:raise RuntimeError((p.stdout,p.stderr))
    return obj

with tempfile.TemporaryDirectory(prefix='stream-header-control-') as td:
    root=Path(td);full=root/'full';full.mkdir();partial=root/'partial';partial.mkdir()
    a=compile_file(full,'Probe.A','prelude\naxiom p : Prop\n')
    b=compile_file(full,'Probe.B','prelude\nimport Probe.A\naxiom q : p\n')
    policy={'roots':[{'path':str(full),'role':'test'}]}
    got=inv.collect(['Probe.B'],policy,max_modules=5,bytes_per_second=10**9,progress_every=0)
    assert got['status']=='COMPILED_HEADER_SURVEY' and set(got['modules'])=={'Probe.A','Probe.B'}
    assert got['modules']['Probe.B']['imports']==['Probe.A'] and not got['frontier']
    capped=inv.collect(['Probe.B'],policy,max_modules=1,bytes_per_second=10**9,progress_every=0)
    assert capped['status']=='PARTIAL_COMPILED_HEADERS' and capped['frontier']==['Probe.A']
    missing=root/'absent';with_missing={'roots':[{'path':str(missing),'role':'absent'},*policy['roots']]}
    absent=inv.collect(['Probe.B'],with_missing,max_modules=5,bytes_per_second=10**9,progress_every=0)
    assert absent['status']=='COMPILED_HEADER_SURVEY' and not absent['root_observations'][0]['present']
    compile_file(partial,'Probe.A','prelude\naxiom p : Prop\n')
    wrong={'roots':[{'path':str(partial),'role':'partial'},{'path':str(full),'role':'full'}]}
    reject(lambda:inv.collect(['Probe.B'],wrong,max_modules=5,bytes_per_second=10**9,progress_every=0),
           'selected namespace lacks object')
    reject(lambda:inv.collect(['Probe/Bad'],policy,max_modules=5,bytes_per_second=10**9,progress_every=0),
           'unsupported module name')
    original=a.read_bytes();a.write_bytes(original+b'different')
    reject(lambda:inv.guard_full(got['artifacts']),'artifact changed')
    a.write_bytes(original)
    got=inv.collect(['Probe.B'],policy,max_modules=5,bytes_per_second=10**9,progress_every=0)
    ir=a.with_suffix('.ir');assert not os.path.lexists(ir);ir.write_bytes(b'unexpected')
    reject(lambda:inv.guard_metadata(got['artifacts']),'artifact metadata changed');ir.unlink()
    # A changed companion during the actual header-reading window fails closed.
    original_read=inv.Reader.read
    b_ir=b.with_suffix('.ir');assert not b_ir.exists()
    def mutate(reader,paths):
        answer=original_read(reader,paths)
        if paths[0]==b and not b_ir.exists():b_ir.write_bytes(b'late')
        return answer
    with patch.object(inv.Reader,'read',mutate):
        reject(lambda:inv.collect(['Probe.B'],policy,max_modules=5,bytes_per_second=10**9,progress_every=0),
               'artifact metadata changed')
    b_ir.unlink(missing_ok=True)
    def create_root(reader,paths):
        answer=original_read(reader,paths)
        missing.mkdir(exist_ok=True)
        return answer
    with patch.object(inv.Reader,'read',create_root):
        reject(lambda:inv.collect(['Probe.B'],with_missing,max_modules=5,bytes_per_second=10**9,progress_every=0),
               'search root presence or resolution changed')
    # All four Foundation object parts are parsed through the persistent reader.
    provider=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/.lake/build/lib/lean')
    env=dict(os.environ,LEAN_NUM_THREADS='1')
    for key in ('LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
    stem=provider/'Foundation/FirstOrder/Arithmetic/IOpen/Basic';reader=inv.Reader(env)
    try:
        rows=reader.read([Path(str(stem)+suffix) for suffix in inv.HEADERS])
        reader.close(True)
    except BaseException:
        reader.close(False);raise
    assert all('Foundation.FirstOrder.Arithmetic.Schemata' in row['imports'] for row in rows.values())
    # The fixture saves the same ModuleData object across three parts and
    # confirms pointer sharing after loading the ordered compacted regions.
    stem=root/'shared'
    fixture=subprocess.run([str(inv.LEAN),'-j1','--run',str(inv.HERE/'make_shared_fixture.lean'),str(stem)],
                           env=env,capture_output=True,text=True,timeout=120)
    assert fixture.returncode==0 and fixture.stdout.strip()=='SHARED_REGION_CONFIRMED',(fixture.stdout,fixture.stderr)
    reader=inv.Reader(env)
    try:
        shared=reader.read([Path(str(stem)+'.olean'),Path(str(stem)+'.olean.server'),
                            Path(str(stem)+'.olean.private'),None])
        reader.close(True)
    except BaseException:
        reader.close(False);raise
    assert set(shared)=={'.olean','.olean.server','.olean.private'}
    assert all(row['imports']==['Synthetic.Dependency'] for row in shared.values())
print('PASS: real Lean transitive/capped surveys, mutation guards, Foundation and shared-region headers')
