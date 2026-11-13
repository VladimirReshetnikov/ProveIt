#!/usr/bin/env python3
"""Check exact prefix driver pins and fail-closed guards without Lean."""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[4]
DRIVER=ROOT/'Computability/DiophantineConsistency/research/thirteen-model-parent-prefix/replay.py'
HASH='881f806b91c37ce596130a19e74a3c605c0ea3c11379f68b1f59bf641dada204'
def need(ok,msg):
    if not ok:raise ValueError(msg)
def reject(f,msg):
    try:f()
    except ValueError:return
    raise ValueError('guard accepted '+msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    blob=subprocess.run(['git','show','d486458873:'+DRIVER.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
    need(hashlib.sha256(blob).hexdigest()==sha(DRIVER)==HASH,'exact driver bytes')
    spec=importlib.util.spec_from_file_location('prefix_review',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    survey,parent=m.check_pins();order=m.prefix_order(survey,parent)
    need(len(order)==20 and len(set(order))==20 and order[-1]==m.ROOT_MODULE,'prefix order')
    bad=copy.deepcopy(survey);del bad['sources'][order[0]]
    reject(lambda:m.prefix_order(bad,parent),'missing project source')
    bad=copy.deepcopy(survey);bad['sources'][order[0]]['imports'].append(order[-1])
    reject(lambda:m.prefix_order(bad,parent),'cycle')
    old=m.PINS[m.SNAP/'manifest.json'];m.PINS[m.SNAP/'manifest.json']='0'*64
    reject(m.check_pins,'incorrect source manifest pin');m.PINS[m.SNAP/'manifest.json']=old
    with tempfile.TemporaryDirectory(prefix='prefix-guard-control-') as t:
        stem=Path(t)/'Input';file=Path(str(stem)+'.olean');file.write_bytes(b'one')
        guard=m.scan(stem);m.check_guard(guard)
        file.write_bytes(b'two');reject(lambda:m.check_guard(guard),'modified object')
        file.write_bytes(b'one');Path(str(stem)+'.ir').write_bytes(b'unexpected')
        reject(lambda:m.check_guard(guard),'unexpected companion')
        site=Path(t)/'site';site.mkdir();marker=Path(t)/'site-executed'
        (site/'sitecustomize.py').write_text('from pathlib import Path\nPath('+repr(str(marker))+').write_text("executed")\n')
        env=os.environ.copy();env.pop('PYTHONHOME',None);env['PYTHONPATH']=str(site)
        p=subprocess.run([sys.executable,'-c','pass'],env=env,capture_output=True,timeout=30)
        need(p.returncode==0 and marker.exists(),'site canary positive control')
        marker.unlink()
        p=subprocess.run([sys.executable,'-I','-S','-c','pass'],env=env,capture_output=True,timeout=30)
        need(p.returncode==0 and not marker.exists(),'isolated Python site canary')
    for args,fragment in [([sys.executable,'-I','-S','-O',str(DRIVER)],'optimized Python'),
                          ([sys.executable,'-S',str(DRIVER)],'python3 -I -S'),
                          ([sys.executable,'-I','-S',str(DRIVER),'--preflight-only','--output','/tmp/not-a-prefix'],'fresh direct')]:
        p=subprocess.run(args,capture_output=True,text=True,timeout=30)
        need(p.returncode!=0 and fragment in p.stderr,'CLI guard '+fragment)
    print(json.dumps({'status':'PASS_PREFIX_INDEPENDENT_GUARDS','driver_sha256':HASH,'prefix_modules':len(order),
       'negative_controls':['nonisolated','optimized','bad-output','bad-source-pin','missing-source','cycle','object-mutation','new-companion','site-hook-positive-and-isolated'],
       'scope':'In-memory mutations and harmless local controls; no real Lean build, live HEAD pin or continuous runtime protection.'},indent=2))

if __name__=='__main__':main()
