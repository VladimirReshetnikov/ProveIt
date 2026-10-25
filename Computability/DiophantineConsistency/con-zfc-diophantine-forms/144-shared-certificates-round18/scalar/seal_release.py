#!/usr/bin/env python3
"""Explicit relative-path whitelist and SHA256 seal, excluding scratch work."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
paths=sorted(p for p in ROOT.rglob('*') if p.is_file() and not {'__pycache__','research'}&set(p.relative_to(ROOT).parts) and p.name not in ['MANIFEST_SHA256.json','RELEASE_WHITELIST.json'])
names=[str(p.relative_to(ROOT)) for p in paths]
(ROOT/'RELEASE_WHITELIST.json').write_text(json.dumps({'schema':'explicit-relative-release-paths-v1','files':names+['MANIFEST_SHA256.json','RELEASE_WHITELIST.json'],'exclude':['research/**','**/__pycache__/**']},indent=2)+'\n')
paths.append(ROOT/'RELEASE_WHITELIST.json')
(ROOT/'MANIFEST_SHA256.json').write_text(json.dumps({'files':{str(p.relative_to(ROOT)):{'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths}},indent=2)+'\n')
print(json.dumps({'status':'PASS','authenticated_files':len(paths)}))
