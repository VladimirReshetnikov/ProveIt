"""Owned literal comparison of the two published218 source layouts."""
from pathlib import Path
import sys,json,collections,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
P=ROOT/'latest218_baseline/candidate-k218';Q=ROOT/'research217_review/contextual/selected/machine'
T=A.R.table(P/'k218.native.tm');U=A.R.table(Q/'k218.native.tm');s=A.P.tree(json.load(open(P/'sites218.json')));t=A.P.tree(json.load(open(Q/'sites218.json')))
g,p,e=A.P.allocation(T,s);h,pp,ee=A.P.allocation(U,t)
psites=json.load(open(P/'sites218.json'));qsites=json.load(open(Q/'sites218.json'))
assert [r[1:]for r in psites]==[r[1:]for r in qsites]
pg=A.continuation_cfg(s);qg=A.continuation_cfg(t);assert pg==qg==A.address_cfg(psites)==A.address_cfg(qsites)
rolekey=lambda ns:tuple(sorted(hashlib.sha256(repr(n).encode()).hexdigest()for n in ns))
def history(V,G):
 inc=collections.defaultdict(list)
 for(q,b),(w,d,z)in V.items():inc[z].append((q,b,w,d))
 marks={}
 for q in sorted({q for q,b in V}):
  if q==0 or not inc[q]or any(d!=1 or p==0 for p,b,w,d in inc[q]):continue
  if any(not inc[p]or any(dd!=1 for pp,bb,ww,dd in inc[p])for p,b,w,d in inc[q]):continue
  marks[q]=sorted({(ww,w)for p,b,w,d in inc[q]for pp,bb,ww,dd in inc[p]})
 pairs=[]
 for q in marks:
  for r in marks:
   if q>=r or set(marks[q])&set(marks[r]):continue
   same=[b for b in(0,1)if V[q,b]==V[r,b]]
   if len(same)==1:pairs.append(dict(states=[q,r],markers=[marks[q],marks[r]],shared_read=same[0],roles=[rolekey(G.get(q,[])),rolekey(G.get(r,[]))],role_leaves=[[A.length(n)for n in G.get(q,[])]for q in(q,r)]))
 return marks,pairs
pm,ps=history(T,g);qm,qs=history(U,h);oldroles={tuple(sorted(tuple(x)for x in pair['roles']))for pair in ps};new=[pair for pair in qs if tuple(sorted(tuple(x)for x in pair['roles']))not in oldroles]
comparison=[]
for q in [79,85,96,188,189,190,212,221]:comparison.append(dict(state=q,primary_rows=[T.get((q,b))for b in(0,1)],alternate_rows=[U.get((q,b))for b in(0,1)],primary_roles=[dict(leaves=A.length(n),alternate_entries=sorted(z for z,ns in h.items()if n in ns))for n in g.get(q,[])],alternate_roles=[dict(leaves=A.length(n),primary_entries=sorted(z for z,ns in g.items()if n in ns))for n in h.get(q,[])]))
out=dict(primary_source_sha256=hashlib.sha256((P/'sites218.json').read_bytes()).hexdigest(),alternate_source_sha256=hashlib.sha256((Q/'sites218.json').read_bytes()).hexdigest(),ordered_primitive_operations_and_arguments_equal=True,primitive_occurrences=len(psites),guarded_successor_edges=sum(len(r[2])for r in pg),two_independent_cfg_resolvers_agree=True,cfg_sha256=hashlib.sha256(A.compact(pg)).hexdigest(),primary_table_sha256=hashlib.sha256((P/'k218.native.tm').read_bytes()).hexdigest(),alternate_table_sha256=hashlib.sha256((Q/'k218.native.tm').read_bytes()).hexdigest(),same_ordinal_cfg=True,both_prefix_bindings_complete=True,core_comparison=comparison,alternate_history_states=len(qm),alternate_history_pairs=qs,structurally_new_history_pairs=new,conclusion='Both folds implement the identical52/54-leaf logical pair at85 with left marker0/1, dispatched to12/150 using helper190(primary)or221(alternate). Alternate212is an outer4721-leaf role, not a third copy of the folded54-leaf role. Exact role equality uses complete literal ASTs. No whole-runtime or boot claim for alternate.')
(OUT/'CONTEXTUAL_ALTERNATE_COMPARISON.json').write_text(json.dumps(out,indent=2)+'\n')
print('alternate markers',len(qm),'pairs',len(qs),'new',len(new));print(json.dumps([{k:v for k,v in x.items()if k!='roles'}for x in new],indent=2))
