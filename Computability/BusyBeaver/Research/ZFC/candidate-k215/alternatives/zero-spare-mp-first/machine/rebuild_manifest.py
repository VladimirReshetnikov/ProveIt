#!/usr/bin/env python3
"""Assembly helper. Recompute only this packet's file inventory."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
files=[dict(path=str(p.relative_to(R)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in sorted(R.rglob('*'))if p.is_file()and p!=R/'manifest.json'and '__pycache__'not in p.parts]
(R/'manifest.json').write_text(json.dumps(dict(format=1,files=files),indent=2)+'\n')
