"""Independent arithmetic audit of JSON data, authored for this deliverable.
Does not execute inherited repository code or the packet-building script.
Modular coefficient checks supplement the symbolic leading-form proof.
"""
import json, hashlib
from pathlib import Path
from collections import Counter
P=Path(__file__).resolve().parent
MOD=1_000_000_007
def trim(a):
    while len(a)>1 and not a[-1]:a.pop()
    return a
def add(a,b,sign=1):
    c=[0]*max(len(a),len(b))
    for i,v in enumerate(a):c[i]=v
    for i,v in enumerate(b):c[i]=(c[i]+sign*v)%MOD
    return trim(c)
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):c[i+j]=(c[i+j]+u*v)%MOD
    return trim(c)
def run(packet,seed):
    env={w:[1+(i+seed)%5,1+(i*3+seed)%11] for i,w in enumerate(packet['witnesses'])}
    env.update({k:[v] for k,v in {'Bm1':15,'Kconstant':19,'MC':2,'MF':19}.items()})
    def value(a):return [a%MOD] if type(a) is int else env[a]
    known=set(packet['witnesses']+packet['fixed_numerals']);counts=Counter()
    deps={}
    for out,op,a,b in packet['source']:
        assert out not in known
        assert all(type(v) is int or v in known for v in (a,b))
        env[out]=mul(value(a),value(b)) if op=='*' else add(value(a),value(b),1 if op=='+' else -1)
        known.add(out);counts[op]+=1;deps[out]=(a,b)
    assert packet['ledger']['total']==len(packet['source'])
    assert packet['ledger']['M']==counts['*']
    assert packet['ledger']['A']==counts['+']+counts['-']
    if 'comparisons' in packet:
        outputs=[x for c in packet['comparisons'] for x in c if isinstance(x,str)]
        degrees=[len(add(value(a),value(b),-1))-1 for a,b in packet['comparisons']]
        assert degrees==packet['residual_exact_degrees'],degrees
        result={'residual_degrees':degrees,'diagnostic_SOS_degree':2*max(degrees)}
    else:
        outputs=[packet['output']]
        degrees=[len(env[x])-1 for x in packet['factor_names']]
        assert degrees==packet['factor_exact_degrees'],degrees
        assert len(env[packet['output']])-1==packet['exact_total_degree']==155
        v={w:env[w][1] for w in packet['witnesses']};Q=15*v['Jrep'];k=v['eta']+v['zeta']
        C=Q-v['F']-v['alpha'];trans=v['w']*C-v['transport_quotient']*Q
        leader=(-8*Q**91*v['h']*v['gamma']*v['i']**4*k**13*v['w']**13*v['s']**26*trans*v['auxiliary_quotient']**2*v['f']**2)%MOD
        assert env['polynomial'][-1]==leader
        result={'factor_degrees':degrees,'diagnostic_degree':155,'leading_form_match':True}
    live=set(outputs);todo=list(outputs)
    while todo:
        for arg in deps.get(todo.pop(),()):
            if isinstance(arg,str) and arg not in live:live.add(arg);todo.append(arg)
    assert live==known
    return result
report={}
for name in ['start_only_system61.json','start_only_polynomial67.json']:
    data=(P/name).read_bytes();packet=json.loads(data)
    report[name]={'sha256':hashlib.sha256(data).hexdigest(),'ledger':packet['ledger'],'witnesses':len(packet['witnesses']),'fixed_ports':packet['fixed_numerals'],'checks':[run(packet,s) for s in [1,2]]}
(P/'start_only_arithmetic_audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
