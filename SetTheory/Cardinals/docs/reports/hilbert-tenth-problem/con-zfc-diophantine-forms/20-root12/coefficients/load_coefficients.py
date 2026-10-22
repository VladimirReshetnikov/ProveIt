"""Fast numeric integrity check by default; --rebuild reruns all finite proofs.
Import load() for the four Python integers in the documented port order.
"""
import argparse, hashlib, json, subprocess, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def check():
 spec=json.loads((ROOT/'COEFFICIENTS.json').read_text())
 manifest=json.loads((ROOT/'expanded/MANIFEST.json').read_text())
 for name in spec['polynomial_ports']:
  meta=spec['numeric_coefficients'][name];path=ROOT/meta['file']
  assert meta['sha256']==manifest['files'][name]['sha256'],name
  assert path.stat().st_size==meta['size_bytes'],name
  digest=hashlib.sha256()
  with path.open('rb') as f:
   first=f.read(1)
   assert first and first!=b'\0',name
   assert 8*(meta['size_bytes']-1)+first[0].bit_length()==meta['bit_length'],name
   digest.update(first)
   while chunk:=f.read(1024*1024):digest.update(chunk)
  assert digest.hexdigest()==meta['sha256'],name
 digest_input=''.join(spec['numeric_coefficients'][n]['sha256'] for n in spec['polynomial_ports']).encode('ascii')
 assert hashlib.sha256(digest_input).hexdigest()==spec['tuple_sha256']
 return {'status':'PASS','mode':'fast numeric integrity check','tuple_id':spec['tuple_id'],'tuple_sha256':spec['tuple_sha256'],'ports':spec['polynomial_ports'],'total_bytes':spec['numeric_total_bytes']}

def load():
 check()
 spec=json.loads((ROOT/'COEFFICIENTS.json').read_text())
 return tuple(int.from_bytes((ROOT/spec['numeric_coefficients'][n]['file']).read_bytes(),'big') for n in spec['polynomial_ports'])

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--rebuild',action='store_true',help='Re-enumerate tiles, independently audit geometry, and rebuild all four numeric files before checking.');args=ap.parse_args()
 if args.rebuild:
  for script,extra in [('build_coefficients.py',[]),('independent_count.py',[]),('audit_compact.py',['--materialize']),('build_coefficients.py',[])]:
   subprocess.run([sys.executable,str(ROOT/script),*extra],check=True)
 print(json.dumps(check(),indent=2))
