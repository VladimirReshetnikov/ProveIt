#!/usr/bin/env python3
"""Offline clean rebuild, literal comparisons, and independent check aggregate."""
from pathlib import Path
from tempfile import TemporaryDirectory
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parent
VARIANTS=['chart202','chart203','chart204','natural200_degree8','natural202','natural202_lowheight','natural203','natural204']

def run(args):
 flags=['-B']+(['-O'] if sys.flags.optimize else [])
 p=subprocess.run([sys.executable]+flags+args,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 if p.returncode:raise RuntimeError(p.stderr+'\n'+p.stdout)
 return json.loads(p.stdout)
def main():
 receipts={};compared=[]
 with TemporaryDirectory(prefix='round22-natural-rebuild-') as tmp:
  out=Path(tmp);run([str(ROOT/'build.py'),'--output',str(out)])
  for f in sorted(out.rglob('*.json')):
   rel=f.relative_to(out)
   if f.read_bytes()!=(ROOT/rel).read_bytes():raise ValueError('clean rebuild differs: '+str(rel))
   compared.append(str(rel))
 receipts['independent_charts_and_octic']=run([str(ROOT/'check.py')])
 receipts['chart_negative_controls']=run([str(ROOT/'check_mutations.py')])
 import check
 for v,origin in [('natural202','chart202'),('natural202_lowheight','chart202'),('natural203','chart203'),('natural204','chart204')]:
  receipts[v]=run([str(ROOT/'check_row_basis.py'),str(ROOT/origin/'equation.json'),str(ROOT/v/'row_basis_certificate.json')])
  e=json.loads((ROOT/v/'equation.json').read_text());c=json.loads((ROOT/v/'row_basis_certificate.json').read_text())
  if e!=c['equation']:raise ValueError('literal equation differs from row-basis certificate')
  met,ex=check.metrics(e)
  if ex!=check.load(json.loads((ROOT/v/'expanded_polynomial.json').read_text())['terms']):raise ValueError('literal expanded selected polynomial differs')
  met['elementary_unimodular_row_shears']=len(c['operations'])
  if met!=e['metrics']:raise ValueError('selected profile metrics')
 receipts['rendered']={v:run([str(ROOT/'render_equation.py'),'--directory',str(ROOT/v),'--check']) for v in VARIANTS}
 pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
 for p,digest in pins['sha256'].items():
  if hashlib.sha256((ROOT/p).read_bytes()).hexdigest()!=digest:raise ValueError('pin mismatch '+p)
 print(json.dumps({'status':'PASS','clean_rebuild_compared':compared,'source_pins_verified':len(pins['sha256']),'receipts':receipts},indent=2,sort_keys=True))
if __name__=='__main__':main()
