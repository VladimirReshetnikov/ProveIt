from pathlib import Path
import sys,json,time
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;m=S.load_machine(out/'h_catalan_node170_3_133_37.tm');sites=[(tuple(p),tuple(op))for p,op in json.loads((out/'h_catalan_node170_3_133_37_sites.json').read_text())];S.all_sites=lambda:sites;cs=S.contracts();start=time.monotonic()
m[101,0]=(0,1,40);m[122,1]=(1,1,60);m={k:v for k,v in m.items()if k[0]!=109};print('remaining109incoming',[k for k,v in m.items()if v[2]==109],flush=True)
bad=[]
for i,b,br,s,t in cs:
 if S.execute(m,br,s,t)is None:bad.append((i,b))
print('baselinebad',bad,flush=True);first=[c for c in cs if (c[0],c[1])in bad[:2]];partial=[];hits=[];trials=0
for q in sorted({q for q,b in m}):
 for w in(0,1):
  for d in(-1,1):
   nm=m|{(77,0):(w,d,q)};trials+=1
   if any(S.execute(nm,br,s,t)is None for i,b,br,s,t in first):continue
   partial.append((w,d,q));fails=[]
   for i,b,br,s,t in cs:
    if S.execute(nm,br,s,t)is None:fails.append((i,b))
   print('partial',w,d,q,'fail',fails[:10],flush=True)
   if not fails:
    hits.append((w,d,q));(out/f'h_plain_{w}_{d}_{q}.tm').write_text(''.join(f'{u} {b} {w} {"R"if d==1 else"L"} {v}\n'for(u,b),(w,d,v)in sorted(nm.items())))
report=dict(trials=trials,partial=partial,hits=hits,seconds=time.monotonic()-start);(out/'h_plain_helper_clearH_results.json').write_text(json.dumps(report,indent=2));print(report,flush=True)
