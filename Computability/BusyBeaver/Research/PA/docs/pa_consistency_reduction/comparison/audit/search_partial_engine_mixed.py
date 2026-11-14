from pathlib import Path
import sys,time,json,collections
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;start=time.monotonic();records=[];hits=[]
for mode in ['original','h_only']:
 m=S.load_machine()if mode=='original'else S.load_machine(out/'h_catalan_node170_3_133_37.tm');sites=S.flatten(S.source_tree()[0])if mode=='original'else[(tuple(p),tuple(op))for p,op in json.loads((out/'h_catalan_node170_3_133_37_sites.json').read_text())];S.all_sites=lambda:sites;cs=S.contracts();first=collections.defaultdict(list)
 for i,b,br,s,t in cs:
  trace=[]
  if S.execute(m,br,s,t,record=trace)is None:raise RuntimeError(('baseline',mode,i,b))
  seen=set()
  for tag,v,row in trace:
   if tag=='step'and v[0]not in seen:first[v[0]].append((br,v,t,i,b));seen.add(v[0])
 protected={q for q,b in S.ENGINE_ROWS}|{m[k][2]for k in S.ENGINE_ROWS}|{0,S.ROOT};trials=0;partial=[]
 for keep,freebit in [(99,0)]:
  for drop in sorted({q for q,b in m}-protected):
   if drop==keep:continue
   nm={k:(w,d,keep if z==drop else z)for k,(w,d,z)in m.items()if k[0]!=drop};w,d,z=m[drop,freebit];nm[keep,freebit]=(w,d,keep if z==drop else z)
   if not S.check_engine(nm):raise RuntimeError('engine mutation')
   trials+=1;examples=first[drop]+first[keep]
   if any(S.execute(nm,br,(keep,)+v[1:],t)is None for br,v,t,i,b in examples):continue
   try:result,_=S.verify(nm)
   except AssertionError as e:partial.append((keep,drop,str(e)));continue
   item={'mode':mode,'keep':keep,'drop':drop,'summary':result};hits.append(item);stem=f'partial_engine_{mode}_{drop}_{keep}';item['stem']=stem
   (out/(stem+'.tm')).write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(nm.items())))
   (out/(stem+'_sites.json')).write_text(json.dumps(sites)+'\n');print('HIT',item,flush=True)
 records.append({'mode':mode,'trials':trials,'partial':partial});print('DONE',mode,trials,partial,flush=True)
(out/'partial_engine_mixed_results.json').write_text(json.dumps({'records':records,'hits':hits,'seconds':time.monotonic()-start},indent=2));print('ALL',len(hits),'seconds',time.monotonic()-start,flush=True)
