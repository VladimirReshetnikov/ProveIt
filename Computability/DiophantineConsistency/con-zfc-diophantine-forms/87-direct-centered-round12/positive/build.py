"""Own graph transformations; upstream JSON is data, never executed."""
import json,pathlib,collections
P=pathlib.Path(__file__).resolve().parent
old=P/'interfaces/p11_degree277.json'
x=json.loads(old.read_text()); s=[]
for row in x['source']:
 name=row[0]
 if name in ('g32','g33','Rhat','g53','Vbar','L'): continue
 if name=='cT':
  s += [['Tshift','+','q','alpha'],['Told','+','T','Tshift']]
  row=['cT','*','Told','c']
 if name=='g56':
  s += [['Aparam','+','a',2],['Dcenter','*','Aparam','I'],['gapmajor','*','k','Told'],['L','+','gapmajor','F']]
 if name=='g60':
  s += [['shiftV','+','g59','V'],['shiftD','+','shiftV','Dcenter']]
  row=['g60','*','M','shiftD']
 s.append(row)
x.update(name='eleven_positive_two_center_cofinal_degree211',source=s,operations=len(s),system_operations=len(s)-3,operation_breakdown=dict(collections.Counter(r[1] for r in s)),exact_degree=211,residual_degrees=[198,13],coefficient_binding='native/ACTIVE_BINDING.json')
(P/'p11_degree211.json').write_text(json.dumps(x,indent=2)+'\n')
print(len(s),x['operation_breakdown'])
y=json.loads((P/'interfaces/p12_degree78.json').read_text()); ss=[]
for row in y['source']:
 if row[0]=='den':continue
 row=[('g73' if z=='den' else z) for z in row]
 if row[0] in ('g89','g92'):row=[('Q' if z=='rho' else z) for z in row]
 ss.append(row)
y.update(name='twelve_positive_ordinary_norm_degree70_materialized',source=ss,operations=len(ss),system_operations=len(ss)-6,operation_breakdown=dict(collections.Counter(r[1] for r in ss)),exact_degree=70,residual_degrees=[15,13,42],coefficient_binding='native/ACTIVE_BINDING.json',novelty='Materialization of incoming report/report.tex section12; no new mathematical construction claimed')
(P/'p12_degree70.json').write_text(json.dumps(y,indent=2)+'\n')
print(len(ss),y['operation_breakdown'])
