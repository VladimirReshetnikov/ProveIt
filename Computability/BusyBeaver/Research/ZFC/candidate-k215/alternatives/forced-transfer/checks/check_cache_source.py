"""Owned exact source binding, independent from the provisional allocator."""
from pathlib import Path
import json,hashlib,argparse
if not __debug__: raise RuntimeError("Assertions must be enabled")
O=Path(__file__).resolve().parent;R=O.parent
parser=argparse.ArgumentParser(description='Exact source binding for the cache-return ST-layout companion')
parser.add_argument('--old',type=Path,default=O/'st215.reference.sites.json')
parser.add_argument('--new',type=Path,default=O/'cache_stlayout.sites.json')
parser.add_argument('--output',type=Path,default=O/'CACHE_STLAYOUT_SOURCE_AUDIT.json')
args=parser.parse_args();oldpath=args.old;newpath=args.new
assert hashlib.sha256(oldpath.read_bytes()).hexdigest()=='212cf0ffde43c1cc22c183dd8bf0b3a699396f96c9942ee92a7cc372cd273ca9'
assert hashlib.sha256(newpath.read_bytes()).hexdigest()=='11e5b1173ca24b406999880c1d874b1e40e74b12334c5db3559440e535384bb9' 
def tree(rows):
 leaves={p:(o,k)for p,o,k in rows}
 def walk(p):return leaves[p]if p in leaves else(walk(p+'0'),walk(p+'1'))
 return walk('')
def at(t,p):
 for b in p:t=t[int(b)]
 return t
def replace(t,p,n):
 if not p:return n
 k=int(p[0]);return tuple(replace(t[j],p[1:],n)if j==k else t[j]for j in(0,1))
def leaves(t):return 1 if isinstance(t[0],str) else leaves(t[0])+leaves(t[1])
a=tree(json.loads(oldpath.read_text()));b=tree(json.loads(newpath.read_text()))
move=(('CD',4),(('CI',5),('CC',2)))
assert b==replace(a,'00110111',move)
assert leaves(at(a,'00110111'))==26
assert leaves(at(b,'00110111'))==3
# A closed CD4 loop decrements D once, increments H once, and loops.
# Starting H=0, it therefore terminates at H=D_initial,D=0.
rec={'status':'EXACT_SOURCE_SPLICE_PASS','old_sha256':hashlib.sha256(oldpath.read_bytes()).hexdigest(),'new_sha256':hashlib.sha256(newpath.read_bytes()).hexdigest(),'path':'00110111','old_leaves':leaves(a),'new_leaves':leaves(b),'old_success_leaves':26,'new_success_leaves':3,'replacement':move,'scope':'Literal equality outside sole success branch. Loop contract follows induction on arbitrary natural D, with H=0 from unchanged equality comparator. Physical runtime and blank startup are separate obligations.'}
args.output.write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
