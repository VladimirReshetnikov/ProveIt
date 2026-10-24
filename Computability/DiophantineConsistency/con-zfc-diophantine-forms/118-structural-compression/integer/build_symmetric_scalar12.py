"""Pointwise-identical symmetric norm evaluators for scalar-carrier12."""
import json
from pathlib import Path
from collections import Counter
from build_symmetric_trace13 import evaluate

HERE=Path(__file__).resolve().parent
def build(variant):
    parent=json.loads((HERE/f'scalar12_{variant}_parent.json').read_text())
    out=dict(parent);nodes=[list(n) for n in parent['nodes'][:125]]
    leaves={n[1]:i for i,n in enumerate(nodes) if n[0]=='integer'}
    def c(k):
        if k not in leaves:leaves[k]=len(nodes);nodes.append(['integer',k])
        return leaves[k]
    def op(kind,a,b):nodes.append([kind,a,b]);return len(nodes)-1
    def plus(a,b):return op('add',a,b)
    def minus(a,b):return op('sub',a,b)
    def times(a,b):return op('mul',a,b)
    def sq(a):return times(a,a)
    z=sq(124)
    if variant=='rational':
        z=times(88,z);common=times(88,112);d=times(112,97)
    else:
        common=112;d=times(times(112,88),97)
    a=times(times(common,c(9)),86)
    b=times(times(common,c(81)),102)
    e=times(times(common,c(729)),80)
    p=plus(a,b);q=plus(e,d);ab=times(a,b);ed=times(e,d)
    e1=plus(p,q);e2=plus(plus(ab,ed),times(p,q))
    e3=plus(times(ab,q),times(ed,p));e4=times(ab,ed)
    s=minus(z,e1);t=minus(sq(s),times(c(4),e2))
    C=plus(sq(t),times(c(64),minus(e4,times(z,e3))))
    L=minus(t,times(c(4),times(z,s)))
    final=minus(sq(C),times(c(256),times(e4,sq(L))))
    out['nodes']=nodes;out['output']=final
    out['named_registers']={k:v for k,v in parent['named_registers'].items() if v<125}
    out['named_registers'].update({'output':final,'norm_e1':e1,'norm_e2':e2,'norm_e3':e3,'norm_e4':e4,'norm_s':s,'norm_t':t,'norm_C':C,'norm_L':L})
    counts=Counter(n[0] for n in nodes if n[0] in ('add','sub','mul'))
    out['operation_counts']=dict(sorted(counts.items()));out['operations']=sum(counts.values())
    out['name']=f'integer12_symmetric_scalar_{variant}'
    out['ordinary_proof']='Universal norm identity; identical polynomial to scalar-carrier12 parent.'
    used=set()
    def mark(i):
        if i in used:return
        used.add(i)
        if nodes[i][0] in ('add','sub','mul'):
            for j in nodes[i][1:]:mark(j)
    mark(final)
    if len(used)!=len(nodes):raise AssertionError(('dead nodes',set(range(len(nodes)))-used))
    (HERE/f'symmetric_scalar12_{variant}.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    return parent,out

def main():
    import random
    results=[];rng=random.Random(2601024)
    for variant in ('rational','integral'):
        parent,child=build(variant)
        for mod in (101,1009,1000003):
            for case in range(300):
                values={n[1]:rng.randrange(-mod,mod) for n in parent['nodes'] if n[0]=='variable'}
                ports={n[1]:rng.randrange(mod) for n in parent['nodes'] if n[0]=='coefficient'}
                if evaluate(parent,values,ports,mod)!=evaluate(child,values,ports,mod):raise AssertionError(('mismatch',variant,mod,case))
        results.append({'variant':variant,'parent_operations':parent['operations'],'new_operations':child['operations'],'counts':child['operation_counts'],'exact_degree':parent['exact_degree'],'same_polynomial':True,'random_controls':900})
    print(results)

if __name__=='__main__':main()
