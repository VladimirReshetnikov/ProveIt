#!/usr/bin/env python3
"""Re-execute the universal runtime proof and compare all frozen results."""
from pathlib import Path
import argparse,gzip,json,subprocess,sys
ROOT=Path(__file__).resolve().parent
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();out=a.out.resolve()
 assert not out.exists(),'Choose a nonexistent output directory.'
 subprocess.run([sys.executable,'-B',str(ROOT/'code/verify_zero_spare.py'),'--base',str(ROOT/'baseline'),'--out',str(out)],check=True)
 subprocess.run([sys.executable,'-B',str(ROOT/'code/review_zero_spare.py'),str(out)],check=True)
 for fn in ('z215.native.tm','z215.tm','sites215.json','canonicalization.json'):assert (out/fn).read_bytes()==(ROOT/'machine'/fn).read_bytes(),fn
 for fn in ('runtime_cases.json.gz','startup.json.gz'):assert gzip.decompress((out/fn).read_bytes())==gzip.decompress((ROOT/'verification'/fn).read_bytes()),fn
 actual=json.loads((out/'runtime.json').read_text());expected=json.loads((ROOT/'verification/runtime.json').read_text())
 actual.pop('seconds');expected.pop('seconds');assert actual==expected
 assert (out/'independent_review.json').read_bytes()==(ROOT/'verification/independent_review.json').read_bytes()
 print('PASS: full symbolic proof, exact cases, complete startup, and independent audit reproduced.')
if __name__=='__main__':main()
