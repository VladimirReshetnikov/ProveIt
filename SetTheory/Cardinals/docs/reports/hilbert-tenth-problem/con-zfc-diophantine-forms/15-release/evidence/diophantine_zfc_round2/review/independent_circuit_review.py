import sys
if sys.flags.optimize:
    raise SystemExit("Do not run these evidence checks with -O or PYTHONOPTIMIZE.")
"""Owned inert-JSON circuit audit. Never imports or executes downloaded code."""
import json, random
from pathlib import Path

ROOT=Path(__file__).parent
P=1000000007

def trim(a):
    while len(a)>1 and not a[-1]: a.pop()
    return a

def add(a,b,sgn=1):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a): c[i]=x
    for i,x in enumerate(b): c[i]=(c[i]+sgn*x)%P
    return trim(c)

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%P
    return trim(c)

def packets(node,label):
    if isinstance(node,dict):
        if isinstance(node.get('source'),list) and node['source'] and len(node['source'][0])==4:
            yield label,node
        else:
            for k,v in node.items(): yield from packets(v,label+'/'+k)
    elif isinstance(node,list):
        for i,v in enumerate(node): yield from packets(v,label+'/'+str(i))

def audit(name,j):
    src=j['source']; assigned=set(); free=set(); ops={'+':0,'-':0,'*':0}
    for out,op,a,b in src:
        assert op in ops, (name,op)
        assert out not in assigned,(name,out)
        for x in (a,b):
            if isinstance(x,str) and x not in assigned: free.add(x)
        assigned.add(out); ops[op]+=1
    ws=j.get('witnesses',j.get('positive_witnesses',[]))
    cs=j.get('fixed_numerals',[])
    if not cs: cs=sorted(free-set(ws))
    assert set(ws).issubset(free),(name,'dead witnesses')
    assert not free-set(ws)-set(cs),(name,free-set(ws)-set(cs))
    comps=j.get('comparisons')
    if comps is None and isinstance(j.get('equations'),list): comps=j['equations']
    out=j.get('output')
    if not comps and not out: return None
    if comps:
        cs=list(set(cs)|{v for pair in comps for v in pair if isinstance(v,str) and v not in assigned and v not in ws})
    degrees=[]
    for seed in (7143,9721):
        rnd=random.Random(seed)
        env={x:[rnd.randrange(2,100),rnd.randrange(1,100)] for x in ws}
        env.update({x:[rnd.randrange(2,100)] for x in cs})
        def val(x): return env[x] if isinstance(x,str) else [x%P]
        for dest,op,a,b in src:
            av,bv=val(a),val(b)
            env[dest]=mul(av,bv) if op=='*' else add(av,bv,1 if op=='+' else -1)
        degrees.append([len(add(val(a),val(b),-1))-1 for a,b in comps] if comps else [len(val(out))-1])
    return dict(name=name,unknowns=len(ws),coefficient_ports=cs,equations=len(comps) if comps else 1,multiplications=ops['*'],additions_subtractions=ops['+']+ops['-'],operations=len(src),line_substitution_degree_diagnostics=degrees,proof_scope='Counts and two independent modular line-specialization diagnostics only; semantic proofs and uniform exact degrees are separate.')

results=[]
for path in sorted(ROOT.rglob('*.json')):
    if path.name=='independent_circuit_review.json': continue
    try: data=json.loads(path.read_text())
    except (ValueError,UnicodeError): continue
    for name,j in packets(data,str(path.relative_to(ROOT))):
        x=audit(name,j)
        if x: results.append(x)
(ROOT/'independent_circuit_review.json').write_text(json.dumps(results,indent=2)+'\n')
for x in results:
    print(x['name'],x['unknowns'],x['equations'],x['operations'],x['line_substitution_degree_diagnostics'])
