#!/usr/bin/env python3
"""Cross-component source binding and required mathematical/license closure."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
def require(b,m):
 if not b:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
checked=[]
for name,digest in read('direct/SOURCE_AND_ARTIFACT_PINS.json').items():
 p=ROOT/'direct'/name;require(p.is_file() and sha(p)==digest,'direct source/artifact '+name);checked.append('direct/'+name)
for name in read('direct/CLOSURE.json')['shared_release_dependencies']:
 require((ROOT/name).is_file(),'missing shared arithmetic proof '+name)
for row in read('height_one/SOURCE_BINDINGS.json'):
 p=ROOT/'height_one'/row['local'];q=ROOT/row['enclosing_source'];require(p.read_bytes()==q.read_bytes() and sha(p)==row['sha256'],'height-one calibrated source binding');checked.append(row['enclosing_source'])
for name in ['direct/licenses/LICENSE.Mathlib','direct/licenses/LICENSE.ProveIt','direct/licenses/LICENSE.incoming_signed','architecture/proofs/inherited/calculus.tex','architecture/proofs/inherited/primitives.tex','architecture/proofs/inherited/crt.tex','architecture/proofs/inherited/direct_arithmetic.tex','architecture/proofs/inherited/calibration/inherited_onestack_section.tex']:
 require((ROOT/name).is_file(),'missing necessary proof/license '+name)
for name,digest in read('cap_audit/FROZEN_HASHES.json').items():
 require((ROOT/name).is_file() and sha(ROOT/name)==digest,'final semantic audit binding '+name);checked.append(name)
for row in read('ENDPOINTS.json')['endpoints']:
 for key in ['graph','equation','polynomial']:
  if key in row:require(sha(ROOT/row[key])==row[key+'_sha256'],'endpoint binding '+row[key])
print(json.dumps({'status':'PASS','cross_component_bindings':checked,'required_direct_calibration_and_licenses_present':True,'scope':'Byte identity and local dependency presence, not a new formal-kernel calibration.'},indent=2))
