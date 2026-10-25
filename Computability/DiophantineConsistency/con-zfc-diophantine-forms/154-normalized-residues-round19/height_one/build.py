#!/usr/bin/env python3
"""Regenerate selected source transformations and literal polarized quartics."""
import sys,json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream'))
import factor_source,contract,literal
from network_compile import run
from spread import spread

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 config=json.loads((HERE/'CONFIG.json').read_text());sources={};endpoints=[]
 for name,p in config['sources'].items():
  orig=HERE/p['original'];dest=HERE/p['refactored'];s=json.loads(orig.read_text());selection=None if not p.get('selection') else set(json.loads((HERE/p['selection']).read_text()))
  f,c=factor_source.factor(s,selected=selection);c['source_sha256']=digest(orig);contract.write(dest/'source.json',f);contract.write(dest/'factor_certificate.json',c);sources[name]=(f,digest(dest/'source.json'))
 for p in config['profiles']:
  s,dg=sources[p['source']];a,c=run(s,p['hubs'],p['seed']);c['source_sha256']=dg
  if 'baseline_sha256' in p:
   for filename,obj in [('polynomial.json',a),('certificate.json',c)]:
    h=hashlib.sha256((json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()
    if h!=p['baseline_sha256'][filename]:raise ValueError('exact round18 baseline regeneration '+filename)
  a,c=spread(a,c);out=HERE/'endpoints'/p['name'];contract.write(out/'polynomial.json',a);contract.write(out/'certificate.json',c);contract.write(out/'metrics.json',a['metrics']);(out/'polynomial.txt').write_text(literal.render(a))
  endpoints.append({'name':p['name'],'source':p['source'],**a['metrics'],'sha256':{f:digest(out/f) for f in ['polynomial.json','certificate.json','metrics.json','polynomial.txt']}})
 contract.write(HERE/'ENDPOINTS.json',endpoints);print(json.dumps(endpoints,indent=2))
if __name__=='__main__':main()
