#!/usr/bin/env python3
"""Recheck identities, replay both certificates, compare exact recorded results."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parent
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not run with -O')

def main():
    manifest=json.loads((HERE/'MANIFEST.json').read_text())
    for rel,want in manifest['sha256'].items():
        assert hashlib.sha256((HERE/rel).read_bytes()).hexdigest()==want,('Hash mismatch',rel)
    for script in ['verify_physical.py','check_commands.py']:
        subprocess.run([sys.executable,str(HERE/script)],check=True)
    for name in ['receipt.json','contracts.json','list_lemmas.json','blank_seed.json','composite_commands.json']:
        assert (HERE/'results'/name).read_bytes()==(HERE/'recorded'/name).read_bytes(),('Reproduction mismatch',name)
    print('PASS: all five full certificate files reproduced exactly',flush=True)

if __name__=='__main__':main()
