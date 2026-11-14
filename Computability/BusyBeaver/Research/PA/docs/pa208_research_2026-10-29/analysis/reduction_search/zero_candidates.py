from pathlib import Path
import sys,json,functools
sys.dont_write_bytecode=True;sys.path.insert(0,'analysis/comparison');import source_inventory as I
L=I.L;rs=json.load(open(I.base/'machine/variant_plain/u208.sites.json'));root=L.tree(rs)
stats={int(a[0]):tuple(map(int,a[1:]))for line in Path('analysis/reduction_search/source_zero.txt').read_text().splitlines()[1:]if(a:=line.split())}
@functools.lru_cache(None)
def size(n):return 1 if L.leaf(n)else size(n[0])+size(n[1])
results=[]
def visit(n,p='',start=0):
 if L.leaf(n):return
 if L.leaf(n[0]) and n[0][0]=='CD' and n[1]==('CC',1):
  r=n[0][1];count,z,pos=stats[start]
  if z>>r&1:results.append({'path':p,'start':start,'end':start+2,'register':r,'contexts':count})
 visit(n[0],p+'0',start);visit(n[1],p+'1',start+size(n[0]))
visit(root)
Path('analysis/reduction_search/zero_clear_candidates.json').write_text(json.dumps(results,indent=2)+'\n');print(len(results));print(json.dumps(results,indent=2))
