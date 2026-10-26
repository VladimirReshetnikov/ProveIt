#!/usr/bin/env python3
"""Read-only whole-package finite verification; standard library only."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
import check,check_row_basis,render_equation
ROOT=Path(__file__).resolve().parent
SELECTED={'natural202':'pooled202','natural202_lowheight':'pooled202','natural203':'pooled203','natural204':'pooled204'}
BASE=['dimension203','projected204','projected205','pooled202','pooled203','pooled204']
def command(path,*args):return subprocess.run([sys.executable,'-B']+([] if __debug__ else['-O'])+[str(path)]+list(args),check=True,text=True,capture_output=True).stdout
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--rebuild',action='store_true');args=ap.parse_args();result={}
 pins=check.read(ROOT/'SOURCE_PINS.json')
 for f in pins['files']:check.require(hashlib.sha256((ROOT/f['path']).read_bytes()).hexdigest()==f['sha256'],'inherited pin '+f['path'])
 result['source_pins']=len(pins['files']);result['semantic_stages']=json.loads(command(ROOT/'check.py',*(['--rebuild']if args.rebuild else [])))
 result['row_bases']={}
 for name,origin in SELECTED.items():
  src=check.read(ROOT/origin/'equation.json');target=check.read(ROOT/name/'equation.json');cert=check.read(ROOT/name/'row_basis_certificate.json')
  check.require(cert['source']=='../'+origin+'/equation.json' and cert['equation']==target,'basis source binding')
  check.require(cert['operations']==check.read(ROOT/name/'operations.json'),'basis operations file')
  check.require(src['domain']==target['domain']=='nonnegative integers','basis natural domain')
  mm,lead,exp=check_row_basis.verify(src,cert);p=check.read(ROOT/name/'expanded_polynomial.json')
  check.require(p==dict(schema='sparse_integer_polynomial_v1',domain='nonnegative integers',variables=len(target['variables']),terms=[[c,list(mon)]for mon,c in sorted(exp.items())]),'basis full coefficients')
  result['row_bases'][name]=json.loads(command(ROOT/'check_row_basis.py',str(ROOT/origin/'equation.json'),str(ROOT/name/'row_basis_certificate.json')))
 result['rendered']={}
 for name in BASE+list(SELECTED):
  e=check.read(ROOT/name/'equation.json')
  for fn,content in render_equation.generate(e).items():check.require((ROOT/name/fn).read_text()==content,'deterministic rendering '+name+'/'+fn)
  render_equation.ROOT=ROOT/name;result['rendered'][name]=render_equation.parse_tex(e)
 result['inherited']=json.loads(command(ROOT/'inherited/verify.py',*(['--rebuild']if args.rebuild else [])))
 if args.rebuild:
  with tempfile.TemporaryDirectory(prefix='natural21-')as d:
   command(ROOT/'build.py','--output',d);compared=[]
   for name in BASE+list(SELECTED):
    for file in (ROOT/name).glob('*.json'):
     check.require(file.read_bytes()==(Path(d)/name/file.name).read_bytes(),'byte-identical rebuild '+name+'/'+file.name);compared.append(name+'/'+file.name)
   check.require((ROOT/'SUMMARY.json').read_bytes()==(Path(d)/'SUMMARY.json').read_bytes(),'summary rebuild')
  result['byte_identical_rebuild']=compared
 result['verified']=True;result['scope']='Finite exact algebra, natural restoration identities, additive frame bounds, source pins, reversible row maps, and all coefficients. Unbounded semantic and logical equivalence is the ordinary proof in PROOF.md and retained calibration.'
 print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
