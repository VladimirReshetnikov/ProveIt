#!/usr/bin/env python3
"""Replay compiler-only comparison on the identical Round17 refactored source."""
import hashlib,importlib.util,json
from pathlib import Path
from network_compile import run
from check_network import audit,require
HERE=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def check():
 loc=HERE/'comparison';cfg=json.loads((loc/'EXPECTED.json').read_text());raw=(loc/'source.json').read_bytes();source=json.loads(raw);dg=hashlib.sha256(raw).hexdigest();require(dg==cfg['source_sha256'],'matched source pin')
 require(sha(loc/'ROUND17_MANIFEST_SHA256.json')==cfg['old_manifest_sha256'],'historical manifest pin');manifest=json.loads((loc/'ROUND17_MANIFEST_SHA256.json').read_text())
 bindings=[('old_polynomial.json','endpoints/balanced806/polynomial.json','old_polynomial_sha256'),('old_certificate.json','endpoints/balanced806/certificate.json','old_certificate_sha256'),('old_audit.py','independent_audit.py','old_auditor_sha256')]
 for local,prior,key in bindings:require(sha(loc/local)==cfg[key]==manifest[prior],'historical byte binding: '+local)
 require(dg==manifest['sources/refactored287/source.json'],'historical identical source binding')
 olda=json.loads((loc/'old_polynomial.json').read_text());oldc=json.loads((loc/'old_certificate.json').read_text())
 # The retained historical auditor is producer-free and byte-bound above.
 spec=importlib.util.spec_from_file_location('round17_independent_audit',loc/'old_audit.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);oldresult=module.audit(source,olda,oldc,dg)
 require(oldresult['variables']==cfg['old_variables'] and oldresult['monomials']==cfg['old_monomials'] and oldresult['coefficient_height']==1 and oldresult['degree']==4,'independently recollected historical dimensions/support/height')
 a,c=run(source,cfg['hubs'],cfg['seed']);c['source_sha256']=dg
 b=(json.dumps(a,sort_keys=True,separators=(',',':'))+'\n').encode();require(hashlib.sha256(b).hexdigest()==cfg['new_polynomial_sha256'],'matched polynomial pin');result=audit(source,a,c,dg);require(result['variables']==cfg['new_variables'] and result['monomials']==cfg['new_monomials'],'matched counts');return {'status':'pass','comparison':cfg,'historical_independent_audit':oldresult,'independent_audit':result}
if __name__=='__main__':print(json.dumps(check(),indent=2))
