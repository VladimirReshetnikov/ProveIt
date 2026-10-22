import sys
if sys.flags.optimize:
    raise SystemExit("Do not run these evidence checks with -O or PYTHONOPTIMIZE.")
"""New inert-data circuit transformation; no received script executed."""
import json,random,hashlib
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
p=json.loads((ROOT/'diophantine_zfc_review/start_only_polynomial67.json').read_text())

def ordinary(p):
    p=dict(p); out=[]
    for row in p['source']:
        dst,op,a,b=row
        if dst=='aux_coefficient_root':
            out += [['ordinary_ic2','*','i','c2'],['ordinary_I2','*','ordinary_ic2','ordinary_ic2'],['ordinary_f2m1','-','L16',1],['ordinary_Q','*','A','ordinary_f2m1'],['ordinary_difference','-','ordinary_I2','ordinary_Q'],['norm_strong','+','ordinary_difference',1]]
        elif dst in ['R16','scaled_f_square','norm_strong']:continue
        elif dst=='L17':out.append([dst,op,'ordinary_Q',b])
        elif dst=='polynomial':out.append([dst,op,a,1])
        else:out.append(row)
    p['source']=out;p['description']='Start-only ordinary-strong polynomial. Its full theorem requires the accompanying ordinary-strong transfer audit.'
    return p

def shear(p):
    p=dict(p);out=[]
    for row in p['source']:
        dst,op,a,b=row
        if dst in ['tau_square','aux_y2']:continue
        out.append(row)
        if dst=='first_root_base':out += [['restored_tau','+','first_root_base','tau_gap'],['tau_square','*','restored_tau','restored_tau']]
        if dst=='aux_u_rhs':out += [['restored_y','+','aux_u_rhs','aux_gap'],['aux_y2','*','restored_y','restored_y']]
    p['source']=out;p['witnesses']=[{'tau_root':'tau_gap','y_aux':'aux_gap'}.get(v,v) for v in p['witnesses']]
    p['description'] += ' Two positive gap shears: tau=L+tau_gap, y=V+aux_gap.'
    return p

def ledger(p):
    seen=set(p['witnesses']+p['fixed_numerals']);ctr=Counter();by={}
    for d,o,a,b in p['source']:
        assert d not in seen
        assert all(isinstance(x,int) or x in seen for x in [a,b]),(d,a,b)
        seen.add(d);ctr[o]+=1;by[d]=[a,b]
    live=set(); todo=['polynomial']
    while todo:
        v=todo.pop()
        if isinstance(v,int) or v in live:continue
        live.add(v);todo+=by.get(v,[])
    assert seen<=live
    return {'total':len(p['source']),'M':ctr['*'],'A':ctr['+']+ctr['-'],'all_rows_and_ports_live':True}

def ev(p,env):
    e=dict(env)
    for d,o,a,b in p['source']:
        a=e.get(a,a) if isinstance(a,str) else a;b=e.get(b,b) if isinstance(b,str) else b
        e[d]=a*b if o=='*' else a+b if o=='+' else a-b
    return e

def add(a,b,s,m):
    c=[0]*max(len(a),len(b))
    for n,x in enumerate(a):c[n]=(c[n]+x)%m
    for n,x in enumerate(b):c[n]=(c[n]+s*x)%m
    while len(c)>1 and c[-1]==0:c.pop()
    return c

def mul(a,b,m):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%m
    while len(c)>1 and c[-1]==0:c.pop()
    return c

rng=random.Random(20261022)
variants=[('start_only_ordinary69',ordinary(p),[22,18,28,7,2,22]),('start_only_sheared69',shear(p),[12,18,54,7,2,46]),('start_only_ordinary_sheared71',shear(ordinary(p)),[12,18,22,7,2,22])]
receipts=[]
for name,obj,degs in variants:
    obj['ledger']=ledger(obj);obj['factor_exact_degrees']=degs;obj['exact_total_degree']=sum(degs)
    dense=[]
    for m in [1000000007,1000000009]:
        e={x:[rng.randrange(1,9),rng.randrange(1,9)] for x in obj['witnesses']};e.update({x:[rng.randrange(2,15)] for x in obj['fixed_numerals']})
        for d,o,a,b in obj['source']:
            a=e[a] if isinstance(a,str) else [a%m];b=e[b] if isinstance(b,str) else [b%m]
            e[d]=mul(a,b,m) if o=='*' else add(a,b,1 if o=='+' else -1,m)
        actual=[len(e[x])-1 for x in obj['factor_names']]
        assert actual==degs,(name,actual,degs)
        assert len(e['polynomial'])-1==sum(degs)
        dense.append({'modulus':m,'factor_degrees':actual,'degree':sum(degs),'leading_coefficient':e['polynomial'][-1]})
    if 'sheared' in name:
        parent=ordinary(p) if 'ordinary' in name else p
        for _ in range(100):
            vals={v:rng.randrange(-5,9) for v in obj['witnesses']+obj['fixed_numerals']}
            child=ev(obj,vals)
            vals.update(tau_root=child['restored_tau'],y_aux=child['restored_y'])
            old=ev(parent,vals)
            for fac in obj['factor_names']+['polynomial']:assert old[fac]==child[fac]
    (OUT/(name+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
    receipts.append({'name':name,'ledger':obj['ledger'],'dense_checks':dense,'all_signed_shear_identity_checks':100 if 'sheared' in name else 0})
(OUT/'sheared_tradeoff_audit.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(receipts,indent=2))
# Transparent systems and their exact sum-of-squares outputs.
for basename in ['start_only_ordinary69','start_only_ordinary_sheared71']:
    obj=json.loads((OUT/(basename+'.json')).read_text())
    remove={'norm_pair','norm_four','norm_product','all_units','seven_units','polynomial','ordinary_difference','norm_strong'}
    system=dict(obj);system['source']=[r for r in obj['source'] if r[0] not in remove]
    system.pop('output',None);system.pop('factor_names',None);system.pop('factor_exact_degrees',None);system.pop('exact_total_degree',None)
    system['comparisons']=[['norm_first',1],['norm_main',1],['norm_aux',1],['norm_index',1],['norm_transport',1],['ordinary_I2','ordinary_Q']]
    ctr=Counter(r[1] for r in system['source'])
    system['ledger']={'total':len(system['source']),'M':ctr['*'],'A':ctr['+']+ctr['-']}
    system['residual_exact_degrees']=[12,18,22,7,2,22] if 'sheared' in basename else [22,18,28,7,2,22]
    (OUT/(basename+'_system.json')).write_text(json.dumps(system,indent=2)+'\n')
    sos=dict(system);sos['source']=list(system['source'])
    for n,(a,b) in enumerate(system['comparisons']):
        sos['source'] += [[f'residual{n}','-',a,b],[f'square{n}','*',f'residual{n}',f'residual{n}']]
    prev='square0'
    for n in range(1,6):
        sos['source'].append([f'sum{n}','+',prev,f'square{n}']);prev=f'sum{n}'
    sos['output']=prev;sos.pop('comparisons');sos['exact_total_degree']=2*max(system['residual_exact_degrees'])
    ctr=Counter(r[1] for r in sos['source']);sos['ledger']={'total':len(sos['source']),'M':ctr['*'],'A':ctr['+']+ctr['-']}
    (OUT/(basename+'_sos.json')).write_text(json.dumps(sos,indent=2)+'\n')
    print(basename, system['ledger'],sos['ledger'],sos['exact_total_degree'])
