#!/usr/bin/env python3
"""Verify coherent new binding and exact free-port-template comparison."""
from pathlib import Path
import gzip,hashlib,json
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(b,m):
 if not b:raise ValueError(m)
def main():
 binding=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text())
 require(binding==json.loads((ROOT/'provenance/radix55/COEFFICIENT_BINDING.json').read_text()),'Changed accepted whole binding')
 out={'tuple':'radix55-only','equations':{},'ports':{}};total=0
 for mode in ('xy','q4','partial'):
  for suffix in ('v2','bv'):
   name=f'{mode}_{suffix}.json';new=json.loads((ROOT/name).read_text());old=json.loads((ROOT/'provenance/templates67'/name).read_text())
   for key in ('source','witnesses','fixed_numerals','operations','operation_breakdown','exact_degree','output','domain'):
    require(new[key]==old[key],f'Template change: {name} {key}')
   require(new['coefficient_binding']==binding,'Mixed or altered binding')
   require(new['tuple_selection']=='radix55-only; whole four-port binding','Ambiguous tuple default')
   out['equations'][name]={'radix55_sha256':sha(ROOT/name),'radix67_sha256':sha(ROOT/'provenance/templates67'/name),'same_complete_free_port_DAG':True,'same_domain':True,'operations':new['operations'],'exact_degree':new['exact_degree']}
 for port,meta in binding['ports'].items():
  path=ROOT/'coefficients'/meta['file'];raw=gzip.decompress(path.read_bytes());v=int.from_bytes(raw,'little');total+=len(raw)
  require(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'] and sha(path)==meta['gzip_sha256'],'Coefficient mismatch')
  require(v.bit_length()==meta['bits'],'Wrong bit count')
  require(hashlib.sha256(raw).hexdigest()!=old['coefficient_binding']['ports'][port]['raw_sha256'],'Unexpected unchanged numeric port')
  out['ports'][port]={'bits':v.bit_length(),'raw_bytes':len(raw),'sha256':meta['raw_sha256'],'different_from_radix67':True}
 require(total==242484==binding['raw_bytes'],'Wrong raw total')
 out.update(raw_bytes=total,radix67_raw_bytes=295388,saving_bytes=295388-total,status='PASS')
 text=json.dumps(out,indent=2)+'\n';(ROOT/'BINDING_CHECK.json').write_text(text);print(text,end='')
if __name__=='__main__':main()
