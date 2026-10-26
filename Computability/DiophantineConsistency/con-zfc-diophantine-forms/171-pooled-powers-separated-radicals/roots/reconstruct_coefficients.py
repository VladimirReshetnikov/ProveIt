#!/usr/bin/env python3
"""Rebuild all six fixed numerals using the inspected finite retained recipe."""
import gzip,hashlib,importlib.util,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def need(ok,msg):
 if not ok:raise ValueError(msg)
def main():
 base=ROOT/'inherited_round20/inherited/coefficients';p=base/'recipe/source34_builder.py'
 spec=importlib.util.spec_from_file_location('retained_finite_recipe',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 values,audit=m.construct();values={'beta':values['beta'],'K0':values['K'],'MC':values['MC'],'MF':values['MF_source'],'cone_A':2**1113,'cone_B':2**666104}
 binding=json.loads((base/'BINDING.json').read_text());rows=[]
 for key,v in values.items():
  e=binding['payloads'][key];rebuilt=v.to_bytes((v.bit_length()+7)//8,'little');raw=gzip.decompress((base/e['file']).read_bytes())
  h=hashlib.sha256(rebuilt).hexdigest();need(raw==rebuilt and h==e['raw_sha256'] and v.bit_length()==e['bits'],'coefficient '+key)
  rows.append({'port':key,'bits':v.bit_length(),'raw_bytes':len(raw),'raw_sha256':h})
 out={'status':'PASS','optimized':not __debug__,'all_six_raw_payloads_rebuilt':True,'recipe_audit':audit,'payloads':rows}
 (ROOT/('COEFFICIENT_REBUILD_OPTIMIZED.json' if not __debug__ else 'COEFFICIENT_REBUILD.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
