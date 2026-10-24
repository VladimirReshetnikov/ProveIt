import json,pathlib,collections
p=pathlib.Path(__file__).resolve().parent;x=json.loads((p.parent/'review/packages/70-residue-orientation/eleven/p11_positive_degree325.json').read_text())
s=[]
for row in x['source']:
 if row[0] in ('g14','g15'):continue
 if row[0]=='I':row=['I','*','c2','i']
 s.append(row)
x.update(name='eleven_positive_denominator_free_degree277',source=s,operations=len(s),system_operations=len(s)-3,operation_breakdown=dict(collections.Counter(r[1] for r in s)),exact_degree=277,residual_degrees=[264,13],coefficient_binding='Complete unchanged compact44 tuple beta,K0,MC,MF; MF already shifted')
x['coefficient_binding']='native/ACTIVE_BINDING.json'
(p/'p11_degree277.json').write_text(json.dumps(x,indent=2)+'\n');print(len(s))
