from pathlib import Path
import sys,json,time
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
m=S.load_machine();tree,nodes=S.source_tree();maps=json.loads((Path(__file__).resolve().parents[2]/'verification/node_map.json').read_text())
old=nodes['node168'];new=(nodes['node145'],nodes['node57'])
def rec(t):
 if t==old:return new
 if t[0]=='leaf':return t
 return rec(t[0]),rec(t[1])
nt=rec(tree);newsites=S.flatten(nt);oldsites=S.all_sites();S.all_sites=lambda:newsites
m[maps['node168'][0],0]=(0,1,maps['node145'][0])
bad=[];passed=0
for i,b,br,s,t in S.contracts():
 if S.execute(m,br,s,t) is None:bad.append((i,b))
 else:passed+=1
out=Path(__file__).parent
(out/'h_only_seed.tm').write_text(''.join(f'{s} {b} {w} {"R" if d==1 else "L"} {t}\n' for (s,b),(w,d,t) in sorted(m.items())))
(out/'h_only_seed_sites.json').write_text(json.dumps(newsites)+'\n')
(out/'h_only_seed_results.json').write_text(json.dumps({'source_sites':len(newsites),'passed':passed,'failed':bad},indent=2)+'\n')
print('sites',len(newsites),'passed',passed,'bad',bad,flush=True)
