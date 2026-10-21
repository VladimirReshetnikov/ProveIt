"""Restore recorded outputs and selected inputs; no candidate execution."""
from pathlib import Path,PurePosixPath
import argparse,gzip,hashlib,json

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 src=Path(__file__).resolve().parents[2]/'data/intake198-source160/saved';out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 rows=json.loads((src/'archive-index.json').read_text())['entries'];seen=set()
 for r in rows:
  p=PurePosixPath(r['path']);s=PurePosixPath(r['stored'])
  assert not p.is_absolute()and'..'not in p.parts and not s.is_absolute()and'..'not in s.parts
  assert r['path']not in seen;seen.add(r['path']);b=(src/r['stored']).read_bytes()
  assert hashlib.sha256(b).hexdigest()==r['stored_sha256']
  b=gzip.decompress(b)if r['gzip']else b
  assert len(b)==r['bytes']and hashlib.sha256(b).hexdigest()==r['sha256']
  dst=out/r['path'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
 print('EXACT_SAVED_AUDIT_VIEW_PREPARED',len(rows))
if __name__=='__main__':main()
