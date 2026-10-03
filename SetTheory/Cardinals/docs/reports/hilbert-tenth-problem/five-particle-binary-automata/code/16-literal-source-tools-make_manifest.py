#!/usr/bin/env python3
"""Build the exact deliverable inventory; no network or third-party dependencies."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
SPECIAL={'manifest.json','SHA256SUMS'}
def shipped(p):
    rel=p.relative_to(ROOT)
    return p.is_file() and not any(x.startswith('.') or x=='__pycache__' for x in rel.parts) and rel.as_posix() not in SPECIAL
files={p.relative_to(ROOT).as_posix():{'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(ROOT.rglob('*')) if shipped(p)}
manifest={'release':'literal-universal-reversible-source-report16','date':'2026-10-03','integrity_files_excluded_from_self_inventory':sorted(SPECIAL),'source_sha256':'38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a','files':files}
(ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(ROOT/'SHA256SUMS').write_text(''.join(v['sha256']+'  '+k+'\n' for k,v in files.items())+hashlib.sha256((ROOT/'manifest.json').read_bytes()).hexdigest()+'  manifest.json\n')
print(json.dumps({'files':len(files),'bytes':sum(v['bytes'] for v in files.values()),'manifest_sha256':hashlib.sha256((ROOT/'manifest.json').read_bytes()).hexdigest()},indent=2))
