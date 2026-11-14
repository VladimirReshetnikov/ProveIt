from pathlib import Path
import sys,time,json
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;start=time.monotonic();hits=[];results=[];oldroot=S.ROOT
for mode in ['original','h_only']:
 m=S.load_machine()if mode=='original'else S.load_machine(out/'h_catalan_node170_3_133_37.tm');sites=S.flatten(S.source_tree()[0])if mode=='original'else[(tuple(p),tuple(op))for p,op in json.loads((out/'h_catalan_node170_3_133_37_sites.json').read_text())];S.all_sites=lambda:sites
 S.ROOT=oldroot;reference=S.contracts();trials=0
 for keep in sorted({q for q,b in m}-{oldroot}):
  nm={k:(w,d,keep if z==oldroot else z)for k,(w,d,z)in m.items()if k[0]!=oldroot}
  if not S.check_engine(nm):continue
  trials+=1;bad=None
  for i,b,br,s,t in reference:
   s=(keep,)+s[1:];t=None if t is None else(keep,)+t[1:]
   if S.execute(nm,br,s,t)is None:bad=(i,b);break
  if bad is None:
   S.ROOT=keep;summary,_=S.verify(nm);hit={'mode':mode,'keep':keep,'summary':summary};hits.append(hit);stem=f'root_fold_{mode}_{keep}';hit['stem']=stem
   (out/(stem+'.tm')).write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(nm.items())))
   (out/(stem+'_sites.json')).write_text(json.dumps(sites)+'\n');print('HIT',hit,flush=True)
  results.append({'mode':mode,'keep':keep,'failure':bad})
 print('DONE',mode,trials,flush=True)
S.ROOT=oldroot;(out/'root_fold_results.json').write_text(json.dumps({'records':results,'hits':hits,'seconds':time.monotonic()-start},indent=2));print('ALL',hits,flush=True)
