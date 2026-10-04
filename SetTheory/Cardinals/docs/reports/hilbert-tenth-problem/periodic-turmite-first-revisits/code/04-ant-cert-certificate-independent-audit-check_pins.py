#!/usr/bin/env python3
"""Read-only validation of authenticated recovered component bytes."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,hashlib,json
R=Path(os.environ.get('ANT_CERTIFICATE_ROOT','/workspace/shared/complete-ant-certificate-recovered-20261004-v2')).resolve();H=Path(__file__).resolve().parent
pins=json.loads((R/'SOURCE_PINS.json').read_text());checked=[];compared=[];missing=[]
for rel,meta in pins['files'].items():
 b=(R/rel).read_bytes()
 if len(b)!=meta['bytes'] or hashlib.sha256(b).hexdigest()!=meta['sha256']:raise ValueError('Pinned component changed '+rel)
 checked.append(rel);o=Path(meta['authenticated_recovery_origin'])
 if o.exists():
  if b!=o.read_bytes():raise ValueError('Authenticated original differs '+rel)
  compared.append(rel)
 else:missing.append(str(o))
out={'status':'PASS_FRESH_AUTHENTICATED_RECOVERY_PINS','internal_component_hashes_verified':len(checked),'authenticated_original_byte_comparisons':len(compared),'optional_original_locations_absent':missing,'files':checked,'upstream_program_execution':False}
(H/'component-pin-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
