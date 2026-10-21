"""Owned three-row 652-leaf crossover prefix and two-marker-selector pilot."""
from pathlib import Path
import sys,json,time,collections,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
from prefix_kernel import Counter,allocate
T=A.R.table(A.NEW/'k218.native.tm');old=A.P.tree(json.load(open(A.NEW/'sites218.json')));og,op,eg=A.P.allocation(T,old)
r=next(x for x in json.load(open(OUT/'CROSSOVER_PRICES.json'))['reports']if x['interval']==[3678,4330]and x['recipient']=='primary')
raw=(ROOT/r['source_file']).read_bytes();assert hashlib.sha256(raw).hexdigest()==r['source_sha256'];source=A.P.tree(json.loads(raw));assert A.continuation_cfg(source)==A.continuation_cfg(old)==A.address_cfg(json.loads(raw))
U=T.copy();edits={(200,1):(1,1,220),(220,0):(0,1,167),(221,1):(1,1,112)}
for row,act in edits.items():U[row]=act
assert all(U[k]==T[k]for k in[(188,1),(189,1),(190,0),(190,1),(156,1),(176,1)])
count=Counter(200000,2);start=time.monotonic();out=dict(source_sha256=r['source_sha256'],states=218,source_nodes=len(A.P.nodes(source))+23,changes=[dict(row=k,old=T[k],new=v)for k,v in edits.items()],scope='Exact source CFG and all known decoder-prefix contracts, followed only by pair200/209 and200/216 unchanged-helper selectors with exact two-cell endpoints. No universal primitive runtime or blank-start claim.')
try:
 ng,np,gg=allocate(U,source,count);oldg=collections.defaultdict(set)
 for ins,b,a,p in eg:oldg[ins,b].add(a)
 bad=[dict(operation=ins,read=b,action=a,path=p)for ins,b,a,p in gg if a not in oldg[ins,b]]
 dest=OUT/'crossover652_primary';dest.mkdir(exist_ok=True);(dest/'sites.json').write_bytes(raw);traw=A.P.M.enc(U);(dest/'raw218.native.tm').write_bytes(traw)
 out.update(prefix_status='PASS',novel_primitive_entry_count=len(bad),novel_primitive_entries=bad,table_sha256=hashlib.sha256(traw).hexdigest())
 inc=collections.defaultdict(list)
 for(q,b),(w,d,z)in U.items():inc[z].append([q,b,w,d])
 marker={}
 for q in(200,209,216):
  assert q!=0 and inc[q] and all(e[3]==1 for e in inc[q]);marker[q]={e[2]for e in inc[q]};assert len(marker[q])==1
 marker={q:next(iter(ms))for q,ms in marker.items()};out['marker_premises']={q:dict(marker=m,incoming=inc[q])for q,m in marker.items()}
 states=sorted({q for q,b in U});catalog={}
 for w in(0,1):
  for H in states:
   for m in(0,1):
    tape={-1:m,0:w};q=H;h=-1;seen=set();points=[];trace=[];stop='STEP_BOUND_UNKNOWN'
    for i in range(32):
     points.append(dict(q=q,h=h,bits=[tape[-1],tape[0]],trace=list(trace)))
     key=q,h,tape[-1],tape[0]
     if key in seen:stop='CYCLE';break
     seen.add(key)
     if q==254:stop='HALT';break
     if h not in tape:stop='OPAQUE_EXIT';break
     if i==31:break
     count.tick();b=tape[h];ww,d,z=U[q,b];trace.append([q,h,b,ww,d,z]);tape[h]=ww;h+=d;q=z
    catalog[w,H,m]=(points,stop)
 reports=[]
 for pair in[(200,209),(200,216)]:
  q,r=pair;assert U[q,0]==U[r,0] and marker[q]!=marker[r];matches=[];near=[];one=0;phi=lambda s:q if s==r else s
  for w in(0,1):
   for H in states:
    if H in pair:continue
    ws=[]
    for role in pair:
     ww,d,z=U[role,1];pts,stop=catalog[w,H,marker[role]]
     good=next((p for p in pts if phi(p['q'])==phi(z) and p['h']==d and p['bits']==[marker[role],ww] and all(t[0]not in pair for t in p['trace'])),None);ws.append(good)
    if all(ws):matches.append(dict(action=[w,-1,H],witnesses=ws))
    elif any(ws):
     one+=1;bad=ws.index(None);role=pair[bad];ww,d,z=U[role,1];pts,stop=catalog[w,H,marker[role]]
     wrong=[p for p in pts if p['h']==d and p['bits']==[marker[role],ww]and all(t[0]not in pair for t in p['trace'])]
     if wrong:near.append(dict(action=[w,-1,H],matching_role=pair[1-bad],missing_role=role,expected=z,wrong=wrong[-1],matched=ws[1-bad]))
  reports.append(dict(pair=pair,matches=matches,one_marker_matches=one,near_matches=near))
 out.update(selector_status='COMPLETE',selectors=reports)
except Exception as e:out.update(status='NOT_PROVED',reason=repr(e))
out.update(transitions=count.steps,seconds=time.monotonic()-start);(OUT/'CROSSOVER652_ALLOCATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
