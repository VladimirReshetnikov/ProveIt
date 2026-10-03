"""Create a release manifest after authorized authoring; not a verifier."""
from hashlib import sha256
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
files={}
for p in sorted(ROOT.rglob('*')):
    rel=p.relative_to(ROOT)
    if any(x in ('.build','replay-output','__pycache__') for x in rel.parts):continue
    if p.is_file() and p.name not in ('release-manifest.json','release-manifest.json.sha256'):
        raw=p.read_bytes();files[rel.as_posix()]={'sha256':sha256(raw).hexdigest(),'bytes':len(raw)}
manifest={'release':'Report19 exact lazy reversible binary CA evaluator','format_version':1,'files':files,
          'primary_pins':{'evaluator':'42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61','compiler':'f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f','source':'fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'},
          'generated_unmanifested_directories':['.build','replay-output'],'symlinks_allowed':False}
raw=(json.dumps(manifest,indent=2)+'\n').encode();(ROOT/'release-manifest.json').write_bytes(raw)
(ROOT/'release-manifest.json.sha256').write_text(sha256(raw).hexdigest()+'  release-manifest.json\n')
print('Manifested',len(files),'files')
