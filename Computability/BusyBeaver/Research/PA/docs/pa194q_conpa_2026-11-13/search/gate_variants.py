import make_variants as m
import json
from pathlib import Path
p=Path(__file__).resolve().parent
data=[x for x in json.load(open(p/'safe_gate_and_encoding_variants.json')) if x['macro_tokens']==190]
vs=[];info=[]
for v in data:
 seq=[tuple(x)if isinstance(x,list)else x for x in v['native_word']]
 for shape,t in enumerate([m.old,m.other]):
  vs.append(m.reword(t,seq));info.append({'id':len(info),'name':v['name'],'shape':shape})
text=m.texts[:135]+[str(len(vs))]
for i,t in enumerate(vs):
 ts,r=m.tarray(t);text+=[f'{i} {len(ts)} {r}']+[' '.join(map(str,x))for x in ts]
 m.save_tree(t,p/f'gate{i}.grammar.json')
(p/'gate_variants.txt').write_text('\n'.join(text)+'\n');(p/'gate_variants.json').write_text(json.dumps(info,indent=2)+'\n')
print(len(vs))
