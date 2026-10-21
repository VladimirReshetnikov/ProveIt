"""Owned explicit four-row table for the205-node30-leaf source crossover."""
from pathlib import Path
import sys,json,time,collections,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
from prefix_kernel import Counter,allocate
T=A.R.table(A.NEW/'k218.native.tm');old=A.P.tree(json.load(open(A.NEW/'sites218.json')));og,op,eg=A.P.allocation(T,old)
receipt=next(x for x in json.load(open(OUT/'CROSSOVER_PRICES.json'))['reports']if x['interval']==[4567,4597]and x['recipient']=='primary')
sourcepath=ROOT/receipt['source_file'];raw=sourcepath.read_bytes();assert hashlib.sha256(raw).hexdigest()==receipt['source_sha256'];src=A.P.tree(json.loads(raw));assert A.continuation_cfg(old)==A.continuation_cfg(src)==A.address_cfg(json.loads(raw))
U=T.copy();edits={(193,0):(0,1,196),(193,1):(1,1,195),(195,0):(0,1,197),(195,1):(1,1,196)}
for k,a in edits.items():U[k]=a
assert all(U[k]==T[k]for k in[(188,1),(189,1),(190,0),(190,1),(156,1),(176,1)])
counter=Counter(200000,2);start=time.monotonic();result=dict(source_sha256=receipt['source_sha256'],source_nodes=205,table_states=218,changes=[dict(row=k,old=T[k],new=v)for k,v in edits.items()])
try:
 ng,np,gg=allocate(U,src,counter);oldg=collections.defaultdict(set)
 for ins,b,a,p in eg:oldg[ins,b].add(a)
 bad=[dict(operation=ins,read=b,action=a,path=p)for ins,b,a,p in gg if a not in oldg[ins,b]]
 out=OUT/'crossover30_primary';out.mkdir(exist_ok=True);(out/'sites.json').write_bytes(raw);traw=A.P.M.enc(U);(out/'raw218.native.tm').write_bytes(traw)
 result.update(status='PREFIX_PASS',novel_primitive_entry_count=len(bad),novel_primitive_entries=bad,table_sha256=hashlib.sha256(traw).hexdigest(),decoder_states=len(ng),decoder_roles=sum(map(len,ng.values())),directory=str(out.relative_to(ROOT)),new_role_entries=[dict(state=q,subtree_leaf_counts=[A.length(n)for n in ns-og.get(q,set())])for q,ns in ng.items()if ns-og.get(q,set())])
except Exception as e:result.update(status='NOT_PROVED',reason=repr(e))
result.update(transitions=counter.steps,seconds=time.monotonic()-start,scope='Source CFG and complete exact decoder-prefix binding only. All primitive action forms are inventoried, but shifted-context universal primitive runtime and blank startup still require independent validation.')
(OUT/'CROSSOVER30_ALLOCATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
