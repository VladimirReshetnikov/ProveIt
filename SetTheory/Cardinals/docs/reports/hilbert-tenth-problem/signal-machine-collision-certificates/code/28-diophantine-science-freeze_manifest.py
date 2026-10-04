#!/usr/bin/env python3
"""Hash only the fresh certificate packet; execute no referenced file."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
entries=[]
for path in sorted(HERE.rglob('*')):
    if path.is_file() and path.name!='PACKET_MANIFEST.json' and '__pycache__' not in path.parts:
        entries.append(dict(path=str(path.relative_to(HERE)),bytes=path.stat().st_size,
                            sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
manifest=dict(schema='research-source-packet-manifest-v1',
              description='Five-signal ordinary-positive-integer Diophantine certificate; all dependency sources inert',
              files=entries)
(HERE/'PACKET_MANIFEST.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
print(json.dumps(dict(files=len(entries),manifest_sha256=hashlib.sha256((HERE/'PACKET_MANIFEST.json').read_bytes()).hexdigest()),sort_keys=True))
