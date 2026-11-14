from pathlib import Path
import sys,time,json
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;start=time.monotonic();results=[];hits=[]
for mode in['original','h_only']:
 m=S.load_machine()if mode=='original'else S.load_machine(out/'h_catalan_node170_3_133_37.tm');sites=S.flatten(S.source_tree()[0])if mode=='original'else[(tuple(p),tuple(op))for p,op in json.loads((out/'h_catalan_node170_3_133_37_sites.json').read_text())];S.all_sites=lambda:sites;cs=S.contracts();priority=[c for c in cs if c[0]in(0,25)];rest=[c for c in cs if c[0]not in(0,25)];protected={q for q,b in S.ENGINE_ROWS}|{m[k][2]for k in S.ENGINE_ROWS}|{0,S.ROOT};trials=0
 for drop in sorted({q for q,b in m}-protected):
  for bit in(0,1):
   keep=S.ROOT;nm={k:(w,d,keep if z==drop else z)for k,(w,d,z)in m.items()if k[0]!=drop};w,d,z=m[drop,bit];nm[keep,bit]=(w,d,keep if z==drop else z);trials+=1
   if any(S.execute(nm,br,s,t)is None for i,b,br,s,t in priority):continue
   if any(S.execute(nm,br,s,t)is None for i,b,br,s,t in rest):continue
   summary,_=S.verify(nm);hit={'mode':mode,'drop':drop,'bit':bit,'summary':summary};hits.append(hit);stem=f'root_mixed_{mode}_{drop}_{bit}';hit['stem']=stem
   (out/(stem+'.tm')).write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(nm.items())))
   (out/(stem+'_sites.json')).write_text(json.dumps(sites)+'\n');print('HIT',hit,flush=True)
 results.append({'mode':mode,'trials':trials});print('DONE',mode,trials,flush=True)
(out/'root_mixed_results.json').write_text(json.dumps({'records':results,'hits':hits,'seconds':time.monotonic()-start},indent=2));print('ALL',hits,flush=True)
