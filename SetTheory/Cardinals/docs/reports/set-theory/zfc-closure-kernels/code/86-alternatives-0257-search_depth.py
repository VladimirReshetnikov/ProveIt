from pathlib import Path
import sys,json,time
R=Path(__file__).resolve().parents[1];P=R/'context_folds/recovered/67/research'
sys.path.insert(0,str(P/'agent_logic'))
from verify_reassociation import Decoder,read_json
OUT=Path(__file__).parent
paths=[P/'sources/beyond252/beyond252/exploratory/data/original203.json',P/'root_search/rebracket202_minimal.json',P/'agent_state/rebracket/combined246_dag.json']
records=[]
for path in paths:
 n,r,_=read_json(path);old=Decoder(n,r);normal=old.normal(('N',r));graph=old.graph();count=0
 for q,(left,right) in n.items():
  if left[0]!='N':continue
  a,b=n[left[1]];fresh=max(n)+1;nn=n|{q:(a,('N',fresh)),fresh:(b,right)}
  try:d=Decoder(nn,r)
  except AssertionError:continue
  m=d.metrics()
  if m[1]<=6:
   eq=d.normal(('N',r))==normal
   row={'base':path.name,'rotated':q,'nodes':len(d.reached),'metrics':m,'normal_equal':eq}
   if eq:
    row['graph_equal']=d.graph()==graph
    if row['graph_equal']:
     out=OUT/f'depth6_{path.stem}_{q}.json';out.write_text(json.dumps({'root':r,'nodes':{k:v for k,v in nn.items() if k in d.reached}},indent=2)+'\n');row['file']=str(out)
   records.append(row);print(row,flush=True)
  count+=1
 print('done',path.name,count,flush=True)
(OUT/'depth_search.json').write_text(json.dumps(records,indent=2)+'\n')
