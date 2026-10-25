#!/usr/bin/env python3
"""Offline exact rebuild of all five sources and three selected centered charts."""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
PLAN=[('odd_t',[]),('odd_y',['--cofinal-y']),('self_radix',['--self-radix']),('self_radix_qf',['--self-radix','--quadratic-first']),('self_radix_min',['--self-radix','--quadratic-first','--max-support','32'])]
CENTER=[('self_radix','centered310'),('self_radix_qf','centered308'),('self_radix_min','centered307')]
def need(c,m):
    if not c:raise ValueError(m)
def is_cache(p):return '__pycache__' in p.parts or p.suffix in ('.pyc','.pyo')
def inventory(p):return {str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.rglob('*')) if f.is_file() and not is_cache(f.relative_to(p))}
def run(optimized=False):
    py=[sys.executable,'-B']+(['-O'] if optimized else [])
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');receipts={}
    with tempfile.TemporaryDirectory(prefix='round17-direct-rebuild-') as td:
        tmp=Path(td)
        clean=tmp/'cache_free_source'
        shutil.copytree(HERE,clean,ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.pyo'))
        need(not any(is_cache(f.relative_to(clean)) for f in clean.rglob('*')),'cache-free input copy')
        for n in json.loads((clean/'SOURCE_PINS.json').read_bytes())['files']:
            need(not is_cache(Path(n)),'no cache dependency in source pins '+n)
        for name,args in PLAN:
            r=subprocess.run(py+[str(clean/'build.py'),str(tmp/name)]+args,check=True,text=True,capture_output=True,env=env)
            need(inventory(tmp/name)==inventory(HERE/name),'whole deterministic source rebuild '+name)
            receipts[name]={'files':len(inventory(tmp/name)),'byte_identical':True};print(name,'PASS',flush=True)
        for source,name in CENTER:
            r=subprocess.run(py+[str(clean/'center.py'),str(tmp/source),str(tmp/name)],check=True,text=True,capture_output=True,env=env)
            need(inventory(tmp/name)==inventory(HERE/name),'whole deterministic centered rebuild '+name)
            receipts[name]={'files':len(inventory(tmp/name)),'byte_identical':True};print(name,'PASS',flush=True)
    return {'status':'PASS','optimized_python':optimized,'cache_free_source_copy':True,'rebuilds':receipts,'scope':'Exact bytes for local source transforms, Horn factoring, monic projections, complete sparse quartics and recorded finite centering.'}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--optimized',action='store_true');p.add_argument('--receipt',type=Path,required=True);a=p.parse_args();result=run(a.optimized);a.receipt.parent.mkdir(parents=True,exist_ok=True);a.receipt.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2))
