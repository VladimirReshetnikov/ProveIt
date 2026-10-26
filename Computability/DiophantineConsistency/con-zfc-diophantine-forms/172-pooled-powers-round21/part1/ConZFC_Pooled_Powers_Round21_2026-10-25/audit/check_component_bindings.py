"""Independent exact-byte binding between final height sources and their
retained direct calibrated source equations; no producer imports."""
import hashlib,json,sys
from pathlib import Path,PurePosixPath
root=Path(sys.argv[1])if len(sys.argv)>1 else Path('/release')
def need(ok,msg):
 if not ok:raise ValueError(msg)
def safe(s):
 p=PurePosixPath(s);need(not p.is_absolute()and'..'not in p.parts,'non-escaping source path');return p
height=root/'height_one';bindings=json.loads((height/'SOURCE_BINDINGS.json').read_text());cfg=json.loads((height/'CONFIG.json').read_text());records=[]
need({b['local']for b in bindings}=={s['original']for s in cfg['sources'].values()},'complete selected original source bindings')
for b in bindings:
 local=height/safe(b['local']);enclosing=root/safe(b['enclosing_source']);a=local.read_bytes();p=enclosing.read_bytes();h=hashlib.sha256(a).hexdigest()
 need(b['binding']=='byte_identical'and a==p and h==b['sha256'],'same calibrated source bytes '+b['local'])
 records.append({'local':str(local.relative_to(root)),'enclosing_source':str(enclosing.relative_to(root)),'sha256':h,'bytes':len(a)})
print(json.dumps({'status':'PASS','source_bindings':records,'boundary':'Literal selected-source identity; unbounded calibration is supplied by retained ordinary proofs and separately reviewed.'},indent=2))
