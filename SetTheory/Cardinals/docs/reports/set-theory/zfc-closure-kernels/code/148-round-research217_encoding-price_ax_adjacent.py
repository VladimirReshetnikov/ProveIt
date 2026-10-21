"""Owned five-interior-swap source census; no physical allocator invocation."""
from pathlib import Path
from functools import lru_cache
import sys,json,time,hashlib,resource
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
contract=json.load(open(OUT/'AX_ROW_CONTRACT_INVENTORY.json'));raw=(A.NEW/'sites218.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==contract['source_sha256'];oldsites=json.loads(raw);old=A.P.tree(oldsites);oldg=A.continuation_cfg(old);assert oldg==A.address_cfg(oldsites)
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
atoms=[freeze(a['tree'])for a in contract['atoms']];names=list(contract['row_atoms']);order0=list(range(8));values=[];ids={};sizes=[]
def intern(n):
 if n in ids:return ids[n]
 i=len(values);ids[n]=i;values.append(n);sizes.append(1 if isinstance(n[0],str)else sizes[n[0]]+sizes[n[1]]);return i
@lru_cache(None)
def encode(n):return intern(n)if A.P.leaf(n)else intern((encode(n[0]),encode(n[1])))
baseid=encode(old);assert len(values)==205;atomids=[encode(n)for n in atoms]
def compose(t,order):
 if t[0]=='F':return encode(A.at(old,t[1]))
 if t[0]=='A':return atomids[order[t[1]]]
 return intern((compose(t[1],order),compose(t[2],order)))
def live(k):
 seen={k};todo=[k]
 for i in todo:
  n=values[i]
  if isinstance(n[0],str):continue
  for c in n:
   if c not in seen:seen.add(c);todo.append(c)
 return seen
@lru_cache(None)
def decode(k):
 n=values[k];return n if isinstance(n[0],str)else tuple(decode(c)for c in n)
def orderatoms(order):return [k for i in order for k in contract['row_atoms'][names[i]]]
assert compose(contract['template'],orderatoms(order0))==baseid
start=time.monotonic();reports=[];dest=OUT/'ax_adjacent';dest.mkdir(exist_ok=True)
for i in range(1,6):
 assert time.monotonic()-start<2,'bounded source census expired'
 order=order0.copy();order[i],order[i+1]=order[i+1],order[i];ao=orderatoms(order);root=compose(contract['template'],ao);t=decode(root);sites=A.flatten(t);g=A.continuation_cfg(t);assert g==A.address_cfg(sites)
 expected=oldsites[:135]+sum((oldsites[slice(*contract['rows'][j]['interval'])]for j in order),[])+oldsites[2650:]
 assert [x[1:]for x in sites]==[x[1:]for x in expected]and len(sites)==4744
 newstarts={};pos=135
 for k in ao:newstarts[k]=pos;pos+=A.length(atoms[k])
 assert pos==2650
 for k,a in enumerate(contract['atoms']):
  lo,hi=a['interval'];nlo=newstarts[k];delta=nlo-lo
  for oi in range(lo,hi):
   op,arg,edges=oldg[oi];assert all(lo<=e<=hi for e in edges);assert g[oi+delta]==[op,arg,[e+delta for e in edges]]
 for j in list(range(135))+list(range(2650,4744)):
  assert oldg[j]==g[j]
  assert all(not 135<e<2650 for e in oldg[j][2])
 b=A.compact(sites);stem=f'swap_{i}_{names[i]}_{names[i+1]}';(dest/(stem+'.sites.json')).write_bytes(b)
 reports.append(dict(swapped=[names[i],names[i+1]],order=[names[j]for j in order],source_nodes=len(live(root)),leaves=len(sites),depth=max(len(p)for p,o,k in sites),maximum_zero_run=max(len(z)for p,o,k in sites for z in p.split('1')),source_file=str((dest/(stem+'.sites.json')).relative_to(ROOT)),source_sha256=hashlib.sha256(b).hexdigest(),all_closed_atom_internal_edges_and_exits_transported=True,outer_cfg_unchanged=True,dual_full_cfg_agreement=True,axiom_positions_from_top={names[j]:8-rank for rank,j in enumerate(order)},physical_status='NOT_ATTEMPTED'))
report=dict(status='COMPLETE',baseline_nodes=205,source_sha256=contract['source_sha256'],family='Exactly five interior adjacent swaps, rho8 first and rho1 last fixed, current520-indivisible-closed-atom skeleton.',reports=reports,minimum_nodes=min(x['source_nodes']for x in reports),seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,scope='Source costs and transported closed-atom CFG only. Not old ordinal-CFG equality; no physical allocation/runtime/blank-start certificate. Enumerative compiler axiom offsets are remapped explicitly but their completeness proof is not replayed.')
(OUT/'AX_ADJACENT_PRICES.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
