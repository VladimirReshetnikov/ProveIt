#!/usr/bin/env python3
"""Read-only offline verification, with byte-exact temporary rebuild."""
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse,hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parent

def read(p):return json.loads(p.read_text())
def run(script,*args):
 p=subprocess.run([sys.executable,'-B']+(['-O']if sys.flags.optimize else[])+[str(script)]+list(map(str,args)),cwd=ROOT,text=True,capture_output=True)
 if p.returncode:raise RuntimeError(p.stdout+'\n'+p.stderr)
 return json.loads(p.stdout)
def main(deep):
 receipts={'status':'PASS'};checks=run(ROOT/'check.py','--negative');receipts['independent_checks']=checks;receipts['bounded_contraction_obstructions']=run(ROOT/'check_local_contractions.py')
 with TemporaryDirectory(prefix='natural23-rebuild-')as d:
  run(ROOT/'build.py','--output',d);compared=[]
  for p in sorted(Path(d).rglob('*.json')):
   rel=p.relative_to(d)
   if p.read_bytes()!=(ROOT/rel).read_bytes():raise ValueError('rebuild differs: '+str(rel))
   compared.append(str(rel))
 receipts['byte_identical_rebuild']=compared
 names=['chart202']+list(read(ROOT/'PROFILES.json'))
 receipts['tex_roundtrips']={n:run(ROOT/'render_equation.py','--directory',ROOT/n,'--check') for n in names}
 import independent_algebra as A
 baseline=read(ROOT/'comparison/BASELINE.json');cm=[]
 for x in baseline['natural_forms']:
  p=ROOT/x['local_path']
  if hashlib.sha256(p.read_bytes()).hexdigest()!=x['sha256']:raise ValueError('comparison source bytes')
  e=read(p);m,ex=A.metrics(e)
  if (m['variables'],m.get('quadratic_rows',m.get('residual_rows')),m['exact_degree'],m['expanded_monomials'],m['max_abs_expanded_coefficient'])!=(x['variables'],x['rows'],x['degree'],x['terms'],x['height']):raise ValueError('current-source comparison')
  cm.append(x['local_path'])
 receipts['current_source_full_recollections']=cm
 for p,digest in read(ROOT/'SOURCE_PINS.json')['files'].items():
  if hashlib.sha256((ROOT/p).read_bytes()).hexdigest()!=digest:raise ValueError('source pin '+p)
 receipts['source_pins_verified']=True
 manifest=ROOT/'MANIFEST_SHA256.json'
 if manifest.exists():
  for p,digest in read(manifest).items():
   if hashlib.sha256((ROOT/p).read_bytes()).hexdigest()!=digest:raise ValueError('manifest mismatch '+p)
 receipts['manifest_verified_when_present']=True
 if deep:
  a=run(ROOT/'inherited/verify.py');b=run(ROOT/'inherited/inherited/verify.py','--rebuild')
  receipts['inherited_round22_replay']='PASS';receipts['complete_inherited_calibration_closure_rebuild']='PASS';receipts['deep_receipt_sha256']=hashlib.sha256(json.dumps([a,b],sort_keys=True,separators=(',',':')).encode()).hexdigest()
 print(json.dumps(receipts,sort_keys=True,indent=2))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--deep',action='store_true');args=ap.parse_args();main(args.deep)
