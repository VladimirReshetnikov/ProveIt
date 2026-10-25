#!/usr/bin/env python3
"""Rebuild and audit the compact retained matched-source comparison."""
import argparse,hashlib,json
from pathlib import Path
from contract import contract
from check import verify
from independent_audit import audit
HERE=Path(__file__).resolve().parent

def sha(x):return hashlib.sha256((json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--report',type=Path);a=p.parse_args();c=json.loads((HERE/'comparison/COMPARISON.json').read_text());raw=(HERE/'comparison/source442.json').read_bytes();source=json.loads(raw);digest=hashlib.sha256(raw).hexdigest()
 if digest!=c['source_sha256']:raise ValueError('Matched source binding')
 pol,cert=contract(source,**c['profile']);cert['source_sha256']=digest
 if pol['metrics']!=c['new']['metrics'] or sha(pol)!=c['new']['polynomial_sha256'] or sha(cert)!=c['new']['certificate_sha256']:raise ValueError('Matched exact regeneration')
 metrics=verify(source,pol,cert,digest);independent=audit(source,pol,cert,digest)
 result={'status':'pass','python_optimized':not __debug__,'metrics':metrics,'independent':independent,'historical_incoming':c['incoming'],'regenerated_polynomial_sha256':sha(pol),'regenerated_certificate_sha256':sha(cert)}
 text=json.dumps(result,sort_keys=True,indent=2)+'\n'
 if a.report:a.report.write_text(text)
 print(text,end='')
if __name__=='__main__':main()
