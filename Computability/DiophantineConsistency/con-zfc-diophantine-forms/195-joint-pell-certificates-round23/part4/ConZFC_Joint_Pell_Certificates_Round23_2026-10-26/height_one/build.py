#!/usr/bin/env python3
"""Regenerate fixed source refactorizations and final literal quartics."""
import sys,json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream'))
import factor_source,contract,literal
from pipeline import build

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 cfg=json.loads((HERE/'CONFIG.json').read_text());sources={};rows=[]
 for name,p in cfg['sources'].items():
  orig=HERE/p['original'];dest=HERE/p['refactored'];selection=set(json.loads((HERE/p['selection']).read_text())) if p.get('selection') else None
  src,fc=factor_source.factor(json.loads(orig.read_text()),selected=selection);fc['source_sha256']=digest(orig);contract.write(dest/'source.json',src);contract.write(dest/'factor_certificate.json',fc);sources[name]=(src,digest(dest/'source.json'))
 for p in cfg['controls']:
  src,dg=sources[p['source']];a,c,st=build(src,p['hubs'],p['seed'],dg,p['flow'],p.get('split',False),p.get('constant_products',False),p.get('scale_chains',False));out=HERE/p['path']
  contract.write(out/'polynomial.json',a);contract.write(out/'certificate.json',c);contract.write(out/'metrics.json',a['metrics'])
 for p in cfg['profiles']:
  src,dg=sources[p['source']];a,c,st=build(src,p['hubs'],p['seed'],dg,p['flow'],p.get('split',False),p.get('constant_products',False),p.get('scale_chains',False),p.get('normalization_profile'));out=HERE/'endpoints'/p['name']
  contract.write(out/'polynomial.json',a);contract.write(out/'certificate.json',c);contract.write(out/'metrics.json',a['metrics']);(out/'polynomial.txt').write_text(literal.render(a))
  rows.append({'name':p['name'],'source':p['source'],**a['metrics'],'sha256':{f:digest(out/f) for f in ['polynomial.json','certificate.json','metrics.json','polynomial.txt']}})
 contract.write(HERE/'ENDPOINTS.json',rows);print(json.dumps(rows,indent=2))
if __name__=='__main__':main()
