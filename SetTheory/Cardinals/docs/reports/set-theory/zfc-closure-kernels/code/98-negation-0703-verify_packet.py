#!/usr/bin/env python3
"""Portable verification runner. Python 3.10+ standard library only.

Use --church-search to reproduce the full 7,500-trial negative control search.
The default reruns source, affine, and symbolic-negation verification only.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,tempfile

HERE=Path(__file__).resolve().parent

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--church-search',action='store_true');args=ap.parse_args()
 records=json.loads((HERE/'vendor_sources.json').read_text())
 for r in records:
  data=(HERE/r['path']).read_bytes()
  assert hashlib.sha256(data).hexdigest()==r['sha256'],r['path']
  blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
  assert blob==r['git_blob_sha1'],r['path']
 print('PASS',len(records),'vendored source hashes',flush=True)
 src=json.loads((HERE/'fine_source_ast.json').read_text())
 excerpt=json.loads((HERE/'negation_ast.json').read_text())
 dag=src['ast_dag']
 def tree(i):
  a=dag[i]
  return a if a[0]=='L' else ['N',tree(a[1]),tree(a[2])]
 for c,t in excerpt['tokens'].items():assert t==tree(src['token_ast'][c]),c
 print('PASS actual AST excerpts match compact full source AST',flush=True)
 env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
 def run(script,*params):
  subprocess.run([sys.executable,str(HERE/script),*map(str,params)],cwd=HERE,env=env,check=True)
 run('audit_negation_peephole.py','--words',HERE/'church-results/fine_words.json')
 run('audit_affine_commutation.py')
 run('audit_source_variants.py')
 if args.church_search:
  with tempfile.TemporaryDirectory(prefix='zfc-church-replay-') as d:
   run('church_basis_experiment.py','--seeds',50,'--output',d)
   got=json.loads((Path(d)/'results.json').read_text())['results']
   want=json.loads((HERE/'church-results/results.json').read_text())['results']
   assert got==want,'coarse compiler results changed'
   assert (Path(d)/'fine_words.json').read_bytes()==(HERE/'church-results/fine_words.json').read_bytes()
   for name,r in want.items():
    assert hashlib.sha256((Path(d)/name/'candidate.tm').read_bytes()).hexdigest()==r['sha256']
  print('PASS full 7,500-trial Church search, all ten table hashes, all50 fine words',flush=True)
 print('PASS packet checks; scope: register-source identities and compiler controls, no standalone ZFC-calibrated binary endpoint',flush=True)

if __name__=='__main__':main()
