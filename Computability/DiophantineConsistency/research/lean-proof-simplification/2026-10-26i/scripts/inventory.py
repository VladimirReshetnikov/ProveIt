#!/usr/bin/env python3
"""Write a reproducible CSV inventory of the active Lean sources to stdout."""
from pathlib import Path
import argparse,csv,hashlib,sys
p=argparse.ArgumentParser(description=__doc__);p.add_argument('repository',type=Path);a=p.parse_args()
root=a.repository.resolve();files=sorted((root/'Computability/DiophantineConsistency/Lean').rglob('*.lean'))
w=csv.writer(sys.stdout);w.writerow(['path','physical_lines','bytes','git_blob','sha256'])
for f in files:
 b=f.read_bytes();w.writerow([str(f.relative_to(root)),len(b.splitlines()),len(b),hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),hashlib.sha256(b).hexdigest()])
