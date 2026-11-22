#!/usr/bin/env python3
"""Run every supplied exact verification and save a readable transcript."""
import subprocess, sys
from pathlib import Path

root=Path(__file__).resolve().parents[1]
commands=[
 ['code/exact_sections.py','--json','certificates/section_witnesses.json'],
 ['code/verify_central_reduction.py'],
 ['certificates/icosahedron/verify_icosahedron.py'],
 ['certificates/dodecahedron/verify_dodecahedron.py'],
 ['code/verify_small_solids.py'],
]
parts=[]
for command in commands:
    p=subprocess.run([sys.executable,*command],cwd=root,text=True,capture_output=True)
    entry='$ python3 '+' '.join(command)+'\n'+p.stdout+p.stderr
    parts.append(entry)
    print(entry,end='')
    if p.returncode:
        (root/'verification.log').write_text('\n'.join(parts))
        raise SystemExit(p.returncode)
parts.append('ALL FIVE VERIFICATION PROGRAMS PASSED.\n')
(root/'verification.log').write_text('\n'.join(parts))
print(parts[-1],end='')
