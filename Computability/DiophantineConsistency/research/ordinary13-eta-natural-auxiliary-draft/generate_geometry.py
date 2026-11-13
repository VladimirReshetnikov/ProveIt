#!/usr/bin/env python3
"""Preserve upstream geometry draft, generalizing eta to all model naturals."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
src=root/'research/ordinary14-aux-geometry-model-draft/AuxGeometry.lean'
b=src.read_bytes();pin='88de9d4d0e92e43ca9483dcb90ae96a7e16284e69b8384cd41c9e16a7ad87b77'
assert hashlib.sha256(b).hexdigest()==pin
s=b.decode()
def once(old,new):
 global s
 assert s.count(old)==1,(old,s.count(old));s=s.replace(old,new,1)
once('positive-parameter geometry','eta-natural geometry')
once('Positive Y and eta plus the explicit first-ordinate lower bound give','Positive Y and an arbitrary natural eta plus the first-ordinate lower bound give')
once('(hY : 0<Y) (heta : 0<eta)','(hY : 0<Y)')
once('_<eta+Y*k := lt_add_of_pos_left _ heta','_≤eta+Y*k := le_add_of_nonneg_left (Arithmetic.zero_le eta)')
s=s.replace('AuxGeometryModelDraft','AuxGeometryEtaNaturalDraft')
assert 'heta' not in s
out=s.encode();p=here/'AuxGeometryEtaNatural.lean.src'
if '--write' in sys.argv:p.write_bytes(out)
else:assert p.read_bytes()==out
print(json.dumps({'upstream_sha256':pin,'draft_sha256':hashlib.sha256(out).hexdigest(),'match':True,'lean_elaborated':False},sort_keys=True,indent=2))
