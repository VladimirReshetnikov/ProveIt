#!/usr/bin/env python3
"""Release-maintenance helper, not a proof checker. Rebuilds the exact inventory."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
# Nested manifests are evidence too: exclude only the root manifest.
files={p.relative_to(root).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
       for p in sorted(root.rglob('*')) if p.is_file()
       and p!=root/'manifest.json' and '__pycache__' not in p.parts}
(root/'manifest.json').write_text(json.dumps({'schema':1,'files':files},indent=2)+'\n')
print('Manifest files:',len(files))
