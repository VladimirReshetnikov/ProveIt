#!/usr/bin/env python3
"""Owned final-artifact audit; standard library only. Never execute received code."""
import contextlib, io, json, runpy, sys
from pathlib import Path
if sys.flags.optimize:
    raise SystemExit('Do not run with -O or PYTHONOPTIMIZE.')
ROOT=Path(__file__).resolve().parents[1]
E=ROOT/'evidence'
R=E/'diophantine_zfc_round2'
def check(condition, label):
    if not condition: raise ValueError(label)
# This is newly authored local audit code, not one of the pinned received scripts.
with contextlib.redirect_stdout(io.StringIO()):
    owned=runpy.run_path(str(R/'integers/verify_integer_artifacts_independent.py'))
upper=owned['weighted_upper_bound']; ev=owned['evalcirc']; con=owned['const']; var=owned['var']; mul=owned['mul']; deg=owned['degree']
forms=json.loads((ROOT/'final_forms.json').read_text())
results=[]
for item in forms:
    packet=json.loads((ROOT/item['artifact']).read_text())
    if item['kind']=='sum_of_squares':
        check(len(packet['variables'])==item['variables'],item['artifact']+' variables')
        check(len(packet['residual_polynomials'])==item['equations'],item['artifact']+' equations')
        check(packet['sum_of_squares_exact_degree']==item['exact_degree'],item['artifact']+' SOS degree')
        results.append(dict(artifact=item['artifact'],variables=item['variables'],equations=item['equations'],degree=item['exact_degree'],checked_by='independent sparse low-degree and integer audits'))
        continue
    rows=packet['source']; ws=packet['witnesses']; fixed=packet['fixed_numerals']
    check(len(ws)==len(set(ws))==item['variables'],item['artifact']+' witnesses')
    check(len(rows)==item['operations'],item['artifact']+' operations')
    targets=[(packet['output'],0)] if 'output' in packet else packet['comparisons']
    check(len(targets)==item['equations'],item['artifact']+' equations')
    known=set(ws+fixed); by={}
    for out,op,a,b in rows:
        check(op in ('+','-','*') and out not in known,item['artifact']+' gate')
        check(all(type(x)is int or x in known for x in (a,b)),item['artifact']+' closure')
        known.add(out);by[out]=(a,b)
    live=set();todo=[x for pair in targets for x in pair]
    while todo:
        x=todo.pop()
        if type(x)is int or x in live:continue
        live.add(x);todo.extend(by.get(x,()))
    check(known<=live,item['artifact']+' liveness')
    counts={'M':sum(row[1]=='*' for row in rows),'A':sum(row[1]!='*' for row in rows)}
    for key,value in counts.items():
        if key in packet.get('ledger',{}):check(packet['ledger'][key]==value,item['artifact']+' ledger '+key)
    if item['domain']=='integer':
        check(packet['exact_degree']==item['exact_degree'],item['artifact']+' integer degree')
        results.append(dict(artifact=item['artifact'],variables=len(ws),equations=len(targets),operations=len(rows),degree=item['exact_degree'],counts=counts,checked_by='independent exact weighted sparse integer audit'))
        continue
    # Degree proof: exact sparse formal-cut upper bounds, with cancellation before
    # each cut; an exact integer line specialization attains every stated bound.
    weights={x:mul(con(j+2),var('t')) for j,x in enumerate(ws)}
    weights.update({x:con(v) for x,v in zip(fixed,[15,3,2,19])})
    lower=ev(rows,weights,True)
    ds=[]
    for j,(a,b) in enumerate(targets):
        p=dict(packet);p['source']=rows+[[f'audit_residual_{j}','-',a,b]];p['output']=f'audit_residual_{j}'
        bound,_,_=upper(p,[])
        av=con(a) if type(a)is int else lower[a]
        bv=con(b) if type(b)is int else lower[b]
        attained=deg(owned['add'](av,bv,-1))
        check(bound==attained,item['artifact']+' upper/lower degree '+str(j)+': '+str((bound,attained)))
        ds.append(bound)
    check(max(ds)==item['exact_degree'],item['artifact']+' exact degree')
    if 'output' not in packet and 'residual_exact_degrees' in packet:check(ds==packet['residual_exact_degrees'],item['artifact']+' residual degrees')
    results.append(dict(artifact=item['artifact'],variables=len(ws),equations=len(targets),operations=len(rows),degree=max(ds),residual_degrees=ds,counts=counts,checked_by='exact sparse formal-cut upper bounds; attaining integer/coefficient specialization; uniform authentic-tuple degree uses accompanying proof'))
# Recheck the reported exact C -> marked_rhs arithmetic identity.
identity=json.loads((R/'review/blank67_start_only67_identity.json').read_text())
for item in identity:
    a=json.loads((E/item['first']).read_text());b=json.loads((E/item['second']).read_text())
    a=a.get('packet',a);b=b.get('packet',b)
    def rename(x):
        if isinstance(x,str):return item['renaming'].get(x,x)
        if isinstance(x,list):return [rename(v) for v in x]
        return x
    check(rename(a['source'])==b['source'],'package 06/08 literal source identity')
    check(rename(a.get('comparisons',[]))==b.get('comparisons',[]),'package 06/08 comparison identity')
# Exact bounded coefficient binding; giant integers are not expanded.
binding=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text())
spec=json.loads((R/'compiler/raw_coefficients_specification.json').read_text())
check(binding['kappa']==int(spec['definitions']['kappa'])==10762728984864,'kappa')
check(binding['cell_bits_power_five']==spec['layout']['cell_bits_power_five']==43,'d=5^43')
check(spec['ports']=={'Bm1':'B-1','Kconstant':'DC+B*DR','MC':'MC','MF':'MF_native+B-1'},'four ports')
receipt={'status':'PASS','final_forms':results,'package_06_08_arithmetic_identity':'PASS','coefficient_binding':'PASS','scope':'Finite algebra, syntax, liveness, counts, degree certificates and coefficient-recipe checks. Semantic proofs and K215 calibration are separate mathematical dependencies, not consequences of a bounded replay.'}
(ROOT/'FINAL_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
