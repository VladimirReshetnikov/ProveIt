#!/usr/bin/env python3
"""Release-maintainer tool: seal the current static tree after all edits are done."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
EXCLUDED={'MANIFEST.json'}
def ignored(p):
    rel=p.relative_to(ROOT)
    return rel.as_posix() in EXCLUDED or '__pycache__' in rel.parts or p.suffix=='.pyc'
def main():
    files=[]
    for p in sorted(ROOT.rglob('*')):
        if p.is_symlink():raise ValueError('symlink not allowed: '+str(p))
        if p.is_file() and not ignored(p):
            raw=p.read_bytes();files.append({'path':p.relative_to(ROOT).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
    manifest={'schema':'research_release_manifest_v1','exclusions':['MANIFEST.json (self)','__pycache__/ and *.pyc (never distributed)'],'files':files}
    (ROOT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'sealed_files':len(files),'bytes':sum(r['bytes'] for r in files)}))
if __name__=='__main__':main()
