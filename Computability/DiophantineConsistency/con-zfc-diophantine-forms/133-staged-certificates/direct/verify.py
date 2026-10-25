#!/usr/bin/env python3
"""Exact finite artifact verification; no root search or consistency decision."""
from pathlib import Path
import argparse,hashlib,json,sys,tempfile
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream'))
from check_contraction import verify,canonical
from review_staged_independent import audit,regressions


def read(path):return json.loads(path.read_text())
def need(ok,msg):
 if not ok:raise ValueError(msg)


def check(rebuild=False):
 led=read(HERE/'SOURCE_LEDGER.json')
 for item in led['upstream_files']:
  p=HERE/item['path'];data=p.read_bytes()
  need(hashlib.sha256(data).hexdigest()==item['sha256'],'source hash changed: '+item['path'])
  need(len(data)==item['bytes'],'source bytes changed: '+item['path'])
 results={}
 for path in sorted((HERE/'equations').iterdir()):
  if not path.is_dir():continue
  source=read(path/'raw/equation.json');target=read(path/'natural/equation.json')
  cert=read(path/'natural/elimination_certificate.json');poly=read(path/'natural/expanded_polynomial.json')
  receipt,terms=verify(source,target,cert)
  need(terms==poly['terms'],'expanded polynomial differs')
  need(receipt==read(path/'natural/VERIFICATION.json'),'recorded metrics differ')
  independent=audit(path)
  independent['path']=path.relative_to(HERE).as_posix()
  results[path.name]={'contraction':receipt,'independent_rows_and_polynomial':independent}
 regenerated=[]
 if rebuild:
  import importlib.util
  spec=importlib.util.spec_from_file_location('staged_release_build',HERE/'build.py')
  build=importlib.util.module_from_spec(spec);spec.loader.exec_module(build)
  with tempfile.TemporaryDirectory(prefix='staged-cap-rebuild-') as td:
   out=Path(td)/'equations'
   build.build(out)
   for p in sorted((HERE/'equations').rglob('*.json')):
    rel=p.relative_to(HERE/'equations')
    need((out/rel).read_bytes()==p.read_bytes(),'rebuild bytes differ: '+str(rel))
    regenerated.append(rel.as_posix())
 return {'status':'PASS','scope':'new rows, complete expansions and all natural restoration certificates; not a new kernel proof or a full transitive logical reproof','upstream_files_authenticated':len(led['upstream_files']),'results':results,'arithmetic_regressions':regressions(),'byte_identical_regeneration':regenerated}


if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--rebuild',action='store_true');p.add_argument('--receipt',type=Path)
 a=p.parse_args();result=check(a.rebuild)
 body=json.dumps(result,indent=2)+'\n'
 if a.receipt:a.receipt.write_text(body)
 print(body,end='')
