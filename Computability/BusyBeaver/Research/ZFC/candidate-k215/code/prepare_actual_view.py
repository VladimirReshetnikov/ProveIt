#!/usr/bin/env python3
"""Expand the exact archived root run to a fresh directory for the unchanged auditor."""
from pathlib import Path
import argparse,json,hashlib,gzip,shutil
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--candidate',type=Path,default=Path(__file__).resolve().parents[1]);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();root=a.candidate.resolve();a.out.mkdir(parents=True,exist_ok=False)
 pins=json.loads((root/'code/frozen-runtime-inputs.json').read_text());index=json.loads((root/'verification/evidence-index.json').read_text())
 for row in pins['files']:
  raw=(root/row['source']).read_bytes();assert sha(raw)==row['sha256'];dst=a.out/row['copy'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(raw)
 for row in index['files']:
  stored=(root/row['stored']).read_bytes();assert sha(stored)==row['stored_sha256'];raw=gzip.decompress(stored)if row['gzip']else stored
  assert sha(raw)==row['raw_sha256']and len(raw)==row['raw_bytes'];dst=a.out/row['run_path'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(raw)
 assert json.loads((a.out/'actual.json').read_text())['status']=='PASS'
 print(json.dumps({'status':'EXACT_ARCHIVED_RUN_VIEW_PREPARED','output':str(a.out.resolve()),'runtime_executed':False,'records':len(index['files'])},indent=2))
if __name__=='__main__':main()
