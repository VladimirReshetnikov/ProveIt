import json,pathlib,collections
p=pathlib.Path(__file__).resolve().parent
src=p.parent/'review/packages/69-cones-pell/positive/equation.json'
x=json.loads(src.read_text()); s=[]
for row in x['source']:
 if row[0]=='q4': continue
 if row[0]=='q5': row=['U','*','q2','Y']
 elif row[0]=='g56': row=['g56','*','q','E']
 else: row=[('U' if v=='q5' else v) for v in row]
 s.append(row)
x.update(name='twelve_positive_adaptive_saturation_degree78',source=s,operations=len(s),system_operations=len(s)-6,operation_breakdown=dict(collections.Counter(r[1] for r in s)),exact_degree=78,residual_degrees=[15,13,50],coefficient_binding='Inherited complete compact44 tuple beta,K0,MC,MF; beta=2^590069-1; MF already shifted')
x['coefficient_binding']='native/ACTIVE_BINDING.json'
(p/'p12_degree78.json').write_text(json.dumps(x,indent=2)+'\n')
print(x['operations'],x['operation_breakdown'])
