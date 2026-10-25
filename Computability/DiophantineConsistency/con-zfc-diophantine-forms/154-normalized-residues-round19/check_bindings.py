#!/usr/bin/env python3
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parent
bindings=json.loads((ROOT/'height_one/SOURCE_BINDINGS.json').read_text());checked=[]
for b in bindings:
 a=ROOT/'height_one'/b['local'];p=ROOT/b['enclosing_source']
 if a.read_bytes()!=p.read_bytes() or hashlib.sha256(a.read_bytes()).hexdigest()!=b['sha256']:raise ValueError('Source binding mismatch: '+b['local'])
 checked.append({'source':b['local'],'enclosing_source':b['enclosing_source'],'sha256':b['sha256']})
a=ROOT/'signed/sources/common252.json';b=ROOT/'signed/inherited_common/equation/equation.json'
if a.read_bytes()!=b.read_bytes():raise ValueError('Common source not byte-identical')
print(json.dumps({'status':'PASS','height_source_bindings':checked,'signed_common_source_binding':'byte identical'},indent=2))
