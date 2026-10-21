#!/usr/bin/env python3
"""Portable, standard-library-only reproduction of the encoding results."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
from source_experiments import reconstruct
from check_arithmetic import check

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,required=True)
    out=parser.parse_args().output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
    source=reconstruct(out)
    arithmetic=check(out/'arithmetic.json')
    subprocess.run([sys.executable,str(Path(__file__).resolve().parent/'audit_counter_salt_source.py'),
                    '--sites',str(out/'counter_salt_208.sites.json'),
                    '--output',str(out/'counter_salt_source_audit.json')],check=True,stdout=subprocess.DEVNULL)
    audit=json.loads((out/'counter_salt_source_audit.json').read_text())
    receipt={'status':'PASS_ENCODING_REPRODUCTION','source':source['status'],
             'arithmetic':arithmetic['status'],'literal_source_macro_audit':audit['status'],
             'reconstructed_source_sha256':source['output_sha256'],
             'scope':'Source generation and arithmetic/compiler-block diagnostics; no <=218-state result is asserted.'}
    (out/'encoding_reproduction.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
