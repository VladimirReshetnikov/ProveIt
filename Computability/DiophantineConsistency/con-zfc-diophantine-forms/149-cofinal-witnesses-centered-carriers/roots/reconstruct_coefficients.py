#!/usr/bin/env python3
"""Rebuild every source34 integer from the retained machine/tiles recipe."""
import gzip,hashlib,importlib.util,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
# Import construct(), not the legacy __main__ entry point. All reachable recipe
# acceptance checks use explicit require/raise and remain active under -O.
s=importlib.util.spec_from_file_location('frozen_source34',ROOT/'inherited/recipe/source34_builder.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
v,a=m.construct();v={'beta':v['beta'],'K0':v['K'],'MC':v['MC'],'MF':v['MF_source'],'cone_A':2**1113,'cone_B':2**666104}
b=json.loads((ROOT/'inherited/baseline/coefficients/BINDING.json').read_text());out={}
for p,x in v.items():
 raw=x.to_bytes((x.bit_length()+7)//8,'little');r=b['payloads'][p];old=gzip.decompress((ROOT/'inherited/baseline/coefficients'/r['file']).read_bytes())
 if raw!=old or hashlib.sha256(raw).hexdigest()!=r['raw_sha256']:raise ValueError('reconstruction '+p)
 out[p]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
result={'status':'PASS','audit':a,'payloads':out};(ROOT/'COEFFICIENT_REBUILD.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
