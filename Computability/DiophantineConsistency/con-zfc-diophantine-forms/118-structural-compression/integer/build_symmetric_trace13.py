"""Replace only the four-root norm tail of a pinned trace13 circuit."""
import json
from pathlib import Path
from collections import Counter
from norm_identity import var, add, sub, mul, scale, square, symmetric_norm

HERE=Path(__file__).resolve().parent

def build():
    parent=json.loads((HERE/'trace13_parent.json').read_text())
    out=dict(parent);nodes=[list(n) for n in parent['nodes'][:116]]
    leaves={n[1]:i for i,n in enumerate(nodes) if n[0]=='integer'}
    def c(k):
        if k not in leaves:leaves[k]=len(nodes);nodes.append(['integer',k])
        return leaves[k]
    def op(kind,a,b):nodes.append([kind,a,b]);return len(nodes)-1
    def plus(a,b):return op('add',a,b)
    def minus(a,b):return op('sub',a,b)
    def times(a,b):return op('mul',a,b)
    def sq(a):return times(a,a)
    delta=67;z=times(delta,sq(115));scaled_u2=times(delta,108)
    a=times(scaled_u2,65);b=times(scaled_u2,79)
    e=times(scaled_u2,105);d=times(108,74)
    p=plus(a,b);q=plus(e,d);ab=times(a,b);ed=times(e,d)
    e1=plus(p,q);e2=plus(plus(ab,ed),times(p,q))
    e3=plus(times(ab,q),times(ed,p));e4=times(ab,ed)
    s=minus(z,e1);t=minus(sq(s),times(c(4),e2))
    C=plus(sq(t),times(c(64),minus(e4,times(z,e3))))
    L=minus(t,times(c(4),times(z,s)))
    final=minus(sq(C),times(c(256),times(e4,sq(L))))
    out['nodes']=nodes;out['output']=final
    out['named_registers']={k:v for k,v in parent['named_registers'].items() if v<116}
    out['named_registers'].update({'output':final,'N':final,'norm_e1':e1,'norm_e2':e2,'norm_e3':e3,'norm_e4':e4,'norm_s':s,'norm_t':t,'norm_C':C,'norm_L':L})
    counts=Counter(n[0] for n in nodes if n[0] in ('add','sub','mul'))
    out['operation_counts']=dict(sorted(counts.items()));out['operations']=sum(counts.values())
    out['name']='integer13_symmetric_trace_degree536'
    out['proof']='Universal norm identity; identical polynomial to the frozen quadratic-trace endpoint.'
    used=set()
    def mark(i):
        if i in used:return
        used.add(i)
        if nodes[i][0] in ('add','sub','mul'):
            for j in nodes[i][1:]:mark(j)
    mark(final)
    if len(used)!=len(nodes):raise AssertionError(('dead nodes',set(range(len(nodes)))-used))
    (HERE/'symmetric_trace13.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    return parent,out

def evaluate(packet,values,coefficients,mod):
    result=[]
    for row in packet['nodes']:
        op,*args=row
        if op=='variable':v=values[args[0]]
        elif op=='coefficient':v=coefficients[args[0]]
        elif op=='integer':v=args[0]
        elif op=='mul':v=result[args[0]]*result[args[1]]
        elif op=='add':v=result[args[0]]+result[args[1]]
        elif op=='sub':v=result[args[0]]-result[args[1]]
        else:raise ValueError(op)
        result.append(v%mod)
    return result[packet['output']]

def main():
    import random
    parent,child=build();rng=random.Random(2601024)
    for mod in (101,1009,1000003):
        for case in range(300):
            values={n[1]:rng.randrange(-mod,mod) for n in parent['nodes'] if n[0]=='variable'}
            ports={n[1]:rng.randrange(mod) for n in parent['nodes'] if n[0]=='coefficient'}
            if evaluate(parent,values,ports,mod)!=evaluate(child,values,ports,mod):
                raise AssertionError(('mismatch',mod,case))
    print({'parent_operations':parent['operations'],'new_operations':child['operations'],'counts':child['operation_counts'],'exact_degree':parent['exact_degree'],'same_polynomial':True,'random_controls':900})

if __name__=='__main__':main()
