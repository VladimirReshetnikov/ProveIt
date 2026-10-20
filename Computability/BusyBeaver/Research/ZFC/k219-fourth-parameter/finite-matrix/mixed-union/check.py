"""Own tiny carrier tests of named mixed fourth-input families, no supplied executable imports."""
from pathlib import Path
from itertools import product
import argparse,json,hashlib
ap=argparse.ArgumentParser()
ap.add_argument('--model',type=Path,default=Path(__file__).resolve().parent.parent/'model.json')
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args();P=args.model
assert hashlib.sha256(P.read_bytes()).hexdigest()=='639477b266ca069ae8298568d447c06a53924e4981e106434db9039b8f85f2d8'
assert not args.output.exists()
old=json.loads(P.read_text())
models={'source147_five':{'I':old['table'],'R':[[2]*5 for _ in range(5)],'Q':old['Q'],'D':old['D'],'T':old['T'],'F':old['F']},'opening_three_candidate':{'I':[[1,2,2],[2,2,2],[1,1,2]],'R':[[1,0,2],[1,0,2],[1,0,0]],'Q':[1,1,2],'D':[2],'T':2,'F':0}}
results={}
for name,m in models.items():
 I=lambda a,b:m['I'][a][b]
 L=lambda a,b,c,u:I(I(I(c,u),a),I(I(a,c),I(b,c)))
 n=len(m['I']);rows={}
 for key,fn in {'RAB':lambda a,b,c:m['R'][a][b],'A':lambda a,b,c:a,'B':lambda a,b,c:b,'C':lambda a,b,c:c,'truth':lambda a,b,c:m['T'],'F':lambda a,b,c:m['F']}.items():
  bad=[list(v)+[fn(*v),L(*v,fn(*v))]for v in product(range(n),repeat=3)if L(*v,fn(*v))not in m['D']]
  rows[key]={'carrier_assignments':n**3,'failures':len(bad),'failure_witnesses':bad}
 results[name]={'model':m,'rows':rows}
r={'status':'EXISTING_MODEL_UNION_SCOPE_CHECK','models':results,'scope':'Only finite assignments for named fourth-input builders. A PASS extends an already sound model; failure refutes only that model, not the calculus. Opening three-value candidate remains pending independent native-row/AST validation.'}
assert {k:v['failures'] for k,v in results['source147_five']['rows'].items()}=={'RAB':0,'A':0,'B':5,'C':0,'truth':0,'F':0}
p=args.output;p.write_text(json.dumps(r,indent=2)+'\n')
for name,v in results.items():print(name,{k:r['failures']for k,r in v['rows'].items()})
