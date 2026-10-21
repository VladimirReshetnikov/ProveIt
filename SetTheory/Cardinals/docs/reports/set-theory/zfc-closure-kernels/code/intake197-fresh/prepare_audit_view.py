"""Restore saved outputs/selected actual inputs for the unchanged record auditor.

No candidate is executed. Compressed outputs are expanded with exact byte pins;
the selected input snapshots are the recorded current inputs, not a fabricated
historical before/after map. Use a fresh output directory outside the repository.
"""
from pathlib import Path,PurePosixPath
import argparse,gzip,hashlib,json

def sha(b):return hashlib.sha256(b).hexdigest()
def safe(s):
 p=PurePosixPath(s)
 if p.is_absolute() or '..' in p.parts:raise ValueError('Unsafe saved relative path')
 return p

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--store',type=Path,default=Path(__file__).resolve().parents[2]/'data/intake197-fresh')
 ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 store=a.store.resolve();output=a.output.resolve();probe=Path(__file__).resolve().parent
 while probe.parent!=probe and not (probe/'.git').exists():probe=probe.parent
 if (probe/'.git').exists() and (output==probe or probe in output.parents):ap.error('Use an output outside the repository')
 output.mkdir(parents=True,exist_ok=False);index=json.loads((store/'archive-index.json').read_text());seen=set()
 for row in index['files']:
  src=store.joinpath(*safe(row['stored']).parts);rel=safe(row['restore'])
  if str(rel) in seen:raise ValueError('Duplicate restore path')
  seen.add(str(rel));data=src.read_bytes()
  if sha(data)!=row['stored_sha256']:raise ValueError('Stored byte drift: '+row['stored'])
  if row['encoding']=='gzip':data=gzip.decompress(data)
  elif row['encoding']!='identity':raise ValueError('Unknown encoding')
  if sha(data)!=row['sha256'] or len(data)!=row['bytes']:raise ValueError('Decoded byte drift: '+row['restore'])
  dst=output.joinpath(*rel.parts);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
 receipt={'status':'EXACT_SAVED_AUDIT_VIEW_PREPARED','files':len(seen),'archive_index_sha256':sha((store/'archive-index.json').read_bytes()),'view':str(output),'scope':'Saved output and selected current-input reconstruction only; no candidate execution or historical before-map claim.'}
 (output/'audit-view-preparation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
