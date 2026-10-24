#!/usr/bin/env python3
"""Authenticate whole coefficient tuples directly from bundled original ZIPs."""
from pathlib import Path
import json,hashlib,zipfile,gzip
R=Path(__file__).resolve().parents[2]
def sha(b):return hashlib.sha256(b).hexdigest()
def require(v,msg):
 if not v: raise RuntimeError(msg)
results=[]
for component in ['low_degree','mixed_source']:
 b=json.loads((R/component/'COEFFICIENT_BINDING.json').read_text()); z=R/b['original_archive']
 require(sha(z.read_bytes())==b['archive_sha256'],'archive SHA')
 with zipfile.ZipFile(z) as f:
  require(sha(f.read(b['binding_member']))==b['binding_sha256'],'binding SHA')
  require(set(b['ports'])=={'beta','K0','MC','MF'},'whole tuple')
  for port,p in b['ports'].items():
   gz=f.read(p['archive_member']); raw=gzip.decompress(gz)
   require(sha(gz)==p['gzip_sha256'] and sha(raw)==p['sha256'],'payload SHA '+port)
   require(len(raw)==p.get('raw_bytes',p.get('bytes')),'raw bytes')
   value=int.from_bytes(raw,'little'); require(value>0 and value.bit_length()==p.get('bits',p.get('bit_length')),'bits')
   if port=='beta': require(value==(1<<value.bit_length())-1,'beta repunit')
  if component=='mixed_source':
   require(sha((R/component/'parent_source.json').read_bytes())==b['source_sha256'],'source SHA')
   proof=f.read(b['source_proof_member']).decode(); require(b['source_sha256'] in proof and 'coefficients/old_tuple' in proof,'source-selection provenance')
   require(len(f.read(b['adapter_proof_member']))>0,'adapter available')
 results.append({'component':component,'status':'passed','ports':4,'instance':b['instance']})
receipt={'status':'passed','scope':'Coefficient identity/provenance authentication only, not compiler theorem proof.','bindings':results}
(R/'review/positive/BINDINGS_CHECK.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
