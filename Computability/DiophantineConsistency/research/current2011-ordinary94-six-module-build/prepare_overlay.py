#!/usr/bin/env python3
"""Create a private combined overlay for the already checked 94 syntax and five missing modules."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json,os,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=Path('/tmp/normalized106-fresh-model-build-v2-20261105/lib')
OUT=Path('/tmp/current2011-ordinary94-six-overlay-20261105'); LIB=OUT/'lib'
SYNTAX=Path('/tmp/current2011-ordinary67-94-syntax-fresh-check01/Carrier94Syntax.olean')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise RuntimeError(m)
need(not OUT.exists(),'output already exists');need(sha(SYNTAX)=='b0a4f82738eb22627c3631b0cfc48053b8051682fb7ed5c2b958281a7e29c76b','syntax object drift')
state=json.loads(Path('/tmp/current2011-ordinary67-94-syntax-fresh-check01/result.json').read_text());need(state['status']=='PASS' and state['guards_stable'],'syntax producer not PASS')
OUT.mkdir();LIB.mkdir(); links={}
for root,dirs,files in os.walk(BASE,followlinks=False):
    rel=Path(root).relative_to(BASE); need(not any((Path(root)/d).is_symlink() for d in dirs),'base symlink dir')
    for d in dirs:(LIB/rel/d).mkdir(parents=True,exist_ok=True)
    for f in files:
        src=Path(root)/f;target=LIB/rel/f;need(src.is_file(),'non-file');target.parent.mkdir(parents=True,exist_ok=True)
        resolved=src.resolve(strict=True);target.symlink_to(resolved);links[str(target)]=str(resolved)
target=LIB/'DiophantineConsistency/Carrier94Syntax.olean';need(not os.path.lexists(target),'syntax path occupied')
with SYNTAX.open('rb') as i,target.open('xb') as o:shutil.copyfileobj(i,o)
need(sha(target)==sha(SYNTAX),'syntax copy mismatch')
record={'status':'PASS','base':str(BASE),'overlay':str(LIB),'syntax_sha256':sha(target),'syntax_source':str(SYNTAX),
 'links':links,'preparer_sha256':sha(__file__), 'scope':'private symlink overlay; direct provider and stage guards required; no complete transitive or dynamic load trace'}
(OUT/'overlay.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','links':len(links),'overlay_receipt_sha256':sha(OUT/'overlay.json'),'syntax_sha256':sha(target)}))
