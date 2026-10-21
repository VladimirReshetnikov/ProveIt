#!/usr/bin/env python3
"""Reconcile only the encountered K215 build metadata, preserving its prior bytes."""
from pathlib import Path
import argparse, hashlib, json, shutil

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--extension',type=Path,required=True);ap.add_argument('--build',type=Path,required=True);a=ap.parse_args();e=a.extension.resolve();r=a.build.resolve()
 assert json.loads((r/'actual-review.json').read_text())['status']=='PASS_CLOSED_KERNEL'
 h=r/'history/metadata-before-finalization';h.mkdir(exist_ok=False)
 shutil.copyfile(e/'manifest.json',h/'manifest.json');shutil.copyfile(e/'coq/regeneration215.json',h/'regeneration215.json')
 m=json.loads((e/'manifest.json').read_text());allowed={'README.md','inputs/229/sites230.json','coq/215/DomRho8.v','coq/215/Sim230.v','regenerate215.py'}
 changed={n:{'before':digest,'after':sha(e/n)} for n,digest in m['files'].items() if sha(e/n)!=digest};assert set(changed)<=allowed
 inp=e/'inputs/229/sites230.json';old_input=inp.read_bytes();up=(r/'k230-rocq/machine/sites230.json').read_bytes();assert old_input==up.replace(b'\r\n',b'\n') and json.loads(old_input)==json.loads(up)
 generated=r/'regenerated-opacity/regeneration215.json';g=json.loads(generated.read_text());assert len(g['generated_source_sha256'])==42
 assert all(sha(e/'coq/215'/n)==digest for n,digest in g['generated_source_sha256'].items())
 for n,d in changed.items():m['files'][n]=d['after']
 (e/'manifest.json').write_text(json.dumps(m,indent=2)+'\n');shutil.copyfile(generated,e/'coq/regeneration215.json')
 assert inp.read_bytes()==old_input and all(sha(e/n)==digest for n,digest in m['files'].items())
 result={'status':'PASS_NARROW_METADATA_RECONCILIATION','changed_manifest_entries':changed,'all42_generated_sources_match_current':True,'regeneration_receipt_sha256':sha(e/'coq/regeneration215.json'),'manifest_sha256':sha(e/'manifest.json'),'legacy229_input_unchanged':True,'legacy229_scope':'Pin committed LF JSON bytes, preserving upstream CRLF pin and exact parsed-source equality in the observation; no input rewrite or broader normalization.','history':str(h)}
 (r/'metadata-finalization.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
