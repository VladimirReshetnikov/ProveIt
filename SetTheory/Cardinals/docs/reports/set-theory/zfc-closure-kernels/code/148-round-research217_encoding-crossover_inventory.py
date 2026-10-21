"""Owned inventory only: shared closed ordinal intervals across two218 layouts."""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
P=ROOT/'latest218_baseline/candidate-k218';Q=ROOT/'research217_review/contextual/selected/machine'
s=A.P.tree(json.load(open(P/'sites218.json')));t=A.P.tree(json.load(open(Q/'sites218.json')))
g,pm,e=A.P.allocation(A.R.table(P/'k218.native.tm'),s);h,qm,ee=A.P.allocation(A.R.table(Q/'k218.native.tm'),t)
assert A.continuation_cfg(s)==A.continuation_cfg(t)
def intervals(root):
 out={}
 def visit(n,p,i):
  j=i+A.length(n);out[i,j]=(p,n)
  if not A.P.leaf(n):visit(n[0],p+'0',i);visit(n[1],p+'1',i+A.length(n[0]))
 visit(root,'',0);return out
si=intervals(s);ti=intervals(t);rows=[]
interesting={19,218,111,179,119,129,203,135,180,183,201,149,132,221,101,213,85,96,212}
for lohi in sorted(si.keys()&ti.keys()):
 p,n=si[lohi];q,m=ti[lohi]
 if n==m or A.boundary(n)!=(0,0,False)or A.boundary(m)!=(0,0,False):continue
 def affected(p,mp):return sorted({v for k,v in mp.items()if k.startswith(p)})
 pp=affected(p,pm);qq=affected(q,qm)
 rows.append(dict(interval=lohi,leaves=lohi[1]-lohi[0],primary_path=p,alternate_path=q,primary_entry=pm[p],alternate_entry=qm[q],primary_ast_sha256=hashlib.sha256(repr(n).encode()).hexdigest(),alternate_ast_sha256=hashlib.sha256(repr(m).encode()).hexdigest(),primary_unique_internal=len(A.P.nodes(n)),alternate_unique_internal=len(A.P.nodes(m)),primary_affected_entries=pp,alternate_affected_entries=qq,interesting_entries=sorted(interesting&set(pp+qq))))
for r in rows:
 lo,hi=r['interval'];r['proper_differing_subintervals']=sum(lo<=a['interval'][0]and a['interval'][1]<=hi and a is not r for a in rows);r['minimal_difference']=r['proper_differing_subintervals']==0
out=dict(primary_source_sha256=hashlib.sha256((P/'sites218.json').read_bytes()).hexdigest(),alternate_source_sha256=hashlib.sha256((Q/'sites218.json').read_bytes()).hexdigest(),shared_intervals=len(si.keys()&ti.keys()),differing_shared_closed_intervals=len(rows),minimal_differing_closed_intervals=sum(r['minimal_difference']for r in rows),rows=rows,scope='Inventory only, no crossovers constructed or priced. Both full sources have identical ordinal CFG. Each listed interval is closed and halt-free on both sides; its two literal subtrees differ. Mixed source/helper roles still prevent inferring a physical splice from an interval splice.')
(OUT/'CROSSOVER_INTERVAL_INVENTORY.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='rows'},indent=2));print(json.dumps([{k:v for k,v in r.items()if k not in('primary_ast_sha256','alternate_ast_sha256','primary_affected_entries','alternate_affected_entries')}for r in rows],indent=2))
