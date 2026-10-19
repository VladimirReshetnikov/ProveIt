import sys,json,time
from pathlib import Path
BASE=Path(__file__).resolve().parent/'base/zfc245-proof-20261018'
sys.path[:0]=[str(BASE/'code'),str(BASE/'reference/context246/code')]
import rebuild_machines as rebuild
import parametric_prefix_affine as affine
from parametric_affine_driver import check_sites
table,start=rebuild.read_table(BASE/'machine/zfc245_old.tm')
table[41,0]=(0,'L',84)
table={k:v for k,v in table.items() if k[0]!=58}
assert 58 not in {x[2] for x in table.values()}
out=Path(__file__).resolve().parent/'shorter_scanner244_old.tm'
out.write_text(rebuild.encode(table,95))
sites=json.loads((BASE/'certificate/sites_physical.json').read_text())
affine.PADDING=64
current={}
run=affine.run
def wrapped(*args,**kw):
 current.update(pc=args[1],branch=args[2]);return run(*args,**kw)
affine.run=wrapped
try:
 result=check_sites(affine,{(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in table.items()},sites,64)
 print(json.dumps({'status':'PASS',**result},indent=2))
except Exception as e:
 print(json.dumps({'status':'FAIL', 'current':current,'error':repr(e)},indent=2))
