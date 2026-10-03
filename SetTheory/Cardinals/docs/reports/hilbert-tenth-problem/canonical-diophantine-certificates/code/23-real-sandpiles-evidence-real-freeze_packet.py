#!/usr/bin/env python3
"""Build a deterministic, self-contained local review archive; no uploads."""
from pathlib import Path
import gzip, hashlib, io, json, tarfile
HERE=Path(__file__).resolve().parent
PAYLOAD=(
 'README.md','PROOF.md','PUBLIC_PRIOR_ART.md','independent_math_review.md',
 'real_certificate.py','exact_checks.py','independent_coefficient_ledger_checks.py',
 'verification.json','verification_optimized.json',
 'independent_coefficient_ledger_receipt.json','independent_coefficient_ledger_receipt_optimized.json',
 'ENVIRONMENT.json','report35_integrity_check.txt',
 'approved_base/prism_certificate.py','approved_base/PROOF.md','freeze_packet.py')
def digest(b):return hashlib.sha256(b).hexdigest()
def require(ok,message):
 if not ok:raise RuntimeError(message)
def main():
 data={p:(HERE/p).read_bytes() for p in PAYLOAD}
 require(all(data.values()),'missing/empty payload')
 require(data['verification.json']==data['verification_optimized.json'],'main receipts differ')
 require(data['independent_coefficient_ledger_receipt.json']==data['independent_coefficient_ledger_receipt_optimized.json'],'independent receipts differ')
 review=json.loads(data['independent_coefficient_ledger_receipt.json'])
 require(review['real_compiler_sha256']==digest(data['real_certificate.py']),'reviewed compiler hash stale')
 require(review['checker_sha256']==digest(data['independent_coefficient_ledger_checks.py']),'independent checker hash stale')
 require(review['frozen_base_compiler_sha256']==digest(data['approved_base/prism_certificate.py']),'base source hash differs')
 require(all(line.endswith(': OK') for line in data['report35_integrity_check.txt'].decode().splitlines()),'Report 35 integrity check failed')
 manifest={'schema':1,'purpose':'Local root review and replay; unpublished strengthening, not an alteration of Report 35.','files':[{'path':p,'bytes':len(data[p]),'sha256':digest(data[p])} for p in sorted(data)]}
 data['MANIFEST.json']=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode()
 data['SHA256SUMS']=''.join(f'{digest(data[p])}  {p}\n' for p in sorted(data)).encode()
 for p in ('MANIFEST.json','SHA256SUMS'):(HERE/p).write_bytes(data[p])
 destination=HERE.parent/(HERE.name+'.tar.gz')
 with destination.open('wb') as raw:
  with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as gz:
   with tarfile.open(mode='w',fileobj=gz,format=tarfile.PAX_FORMAT) as tar:
    for p in sorted(data):
     info=tarfile.TarInfo(HERE.name+'/'+p);info.size=len(data[p]);info.mode=0o644;info.mtime=0;info.uid=info.gid=0;info.uname=info.gname=''
     tar.addfile(info,io.BytesIO(data[p]))
 checksum=digest(destination.read_bytes())
 destination.with_suffix(destination.suffix+'.sha256').write_text(f'{checksum}  {destination.name}\n')
 print(json.dumps({'archive':str(destination),'bytes':destination.stat().st_size,'sha256':checksum,'payload_files':len(PAYLOAD),'archived_files':len(data)},sort_keys=True))
if __name__=='__main__':main()
