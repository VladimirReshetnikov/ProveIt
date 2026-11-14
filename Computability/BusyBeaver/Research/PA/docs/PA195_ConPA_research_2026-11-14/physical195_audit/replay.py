#!/usr/bin/env python3
"""Verify the manifest, rederive physical proofs, and compare exact receipts."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys

HERE=Path(__file__).resolve().parent
if not __debug__:raise RuntimeError('Replay requires assertions enabled')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('family',choices=['195S','195C','both'],nargs='?',default='both')
    args=ap.parse_args()
    manifest=json.loads((HERE/'MANIFEST.json').read_text())
    for rel,expected in manifest['sha256'].items():
        assert hashlib.sha256((HERE/rel).read_bytes()).hexdigest()==expected,('Artifact hash mismatch',rel)
    for family in (['195S','195C']if args.family=='both'else[args.family]):
        subprocess.run([sys.executable,HERE/'verify_physical.py',family],check=True)
        for name in ['receipt.json','contracts.json','list_lemmas.json','blank_seed.json']:
            assert(HERE/'results'/family/name).read_bytes()==(HERE/'recorded'/family/name).read_bytes(),('Reproduction mismatch',family,name)
        print(family,'all four complete certificate files reproduced exactly',flush=True)

if __name__=='__main__':main()
