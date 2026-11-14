from pathlib import Path
import sys,json,time
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;m=S.load_machine();tree,nodes=S.source_tree();maps=json.loads((Path(__file__).resolve().parents[2]/'verification/node_map.json').read_text())
old=nodes['node169'];new=((nodes['node167'],nodes['node145']),nodes['node57'])
def rec(t):
 if t==old:return new
 if t[0]=='leaf':return t
 return rec(t[0]),rec(t[1])
nt=rec(tree);newsites=S.flatten(nt);hs=json.loads((out/'h_only_seed_sites.json').read_text());hs=[(tuple(p),tuple(op)) for p,op in hs];print('CFG same',S.instructions(hs)==S.instructions(newsites),flush=True)
q169,q168,q167,q145,q57=[maps['node'+str(i)][0] for i in [169,168,167,145,57]]
m[q169,0]=(0,1,q168);m[q169,1]=(1,1,q57);m[q168,0]=(0,1,q167);m[q168,1]=(1,1,q145)
S.all_sites=lambda:newsites
bad=[];passed=0
for i,b,br,s,t in S.contracts():
 if S.execute(m,br,s,t) is None:bad.append((i,b))
 else:passed+=1
(out/'h_reassociate.tm').write_text(''.join(f'{s} {b} {w} {"R" if d==1 else "L"} {t}\n' for (s,b),(w,d,t) in sorted(m.items())))
(out/'h_reassociate_sites.json').write_text(json.dumps(newsites)+'\n')
(out/'h_reassociate_results.json').write_text(json.dumps({'source_sites':len(newsites),'passed':passed,'failed':bad,'changed_states':[q169,q168]},indent=2)+'\n')
print('sites',len(newsites),'states',q169,q168,'passed',passed,'bad',bad,flush=True)
