"""Replay saved examples without reconstructing expanded membrane populations."""
from motif_compiler import Rule,compile_schema
from pathlib import Path
import json
ROOT=Path(__file__).parent
examples=json.loads((ROOT/'examples.json').read_text())
packets={name:p for name,p in examples.items() if isinstance(p,dict) and 'witness' in p}
packets.update({'same_mass_'+name:p for name,p in examples['same_mass_different_successor'].items()})
report=[]
for name,p in packets.items():
    rules=[Rule(kind=r['kind'],label=r['label'],a=r['a'],out=tuple(r['out']),other=tuple(r['other']),elementary=r['elementary']) for r in p['rules']]
    d=p['alphabet_size'];eq,variables=compile_schema(p['schema'],rules,d);w=p['witness']
    assert set(variables)==set(w)
    assert all(type(v) is int and v>=0 for v in w.values())
    assert all(q.evaluate(w)==0 for _,q in eq)
    cs=p['schema']['configs'];ts=p['schema']['transitions'];K=len(cs);J=len(ts)
    A=sum(len(c['children']) for c in cs);E=sum(len(t['children']) for t in ts);B=sum(v.startswith('e:') for v in variables);L=sum(len(t['targets']) for t in ts);Z=sum(n.startswith('maximal:') for n,_ in eq)
    assert len(variables)==d*K+A+E+B+3*d*J+K*J
    assert len(eq)==(3*d+2*K)*J+(d+K)*L+Z
    H=max(2,max((max(r.out,default=0) for r in rules if r.kind=='evolve'),default=0),1+max((len(t['children']) for t in ts),default=0))
    actual_H=max(abs(c) for _,q in eq for c in q.t.values())
    assert actual_H<=H
    report.append({'name':name,'variables':len(variables),'residuals':len(eq),'max_degree':max(q.degree for _,q in eq),'coefficient_height':actual_H,'height_bound':H})
    if name=='dissolution_then_contextual_copy':
        (ROOT/'contextual_copy_polynomials.json').write_text(json.dumps({'convention':'Each residual is a list of [integer coefficient, sorted variable-name monomial]; all variables natural; conjunction is sum of residual squares = 0.','variables':variables,'residuals':{n:q.as_json() for n,q in eq},'witness':w},indent=2)+'\n')
(ROOT/'saved_example_receipt.json').write_text(json.dumps({'status':'passed','examples':report},indent=2)+'\n')
print(json.dumps(report,indent=2))
