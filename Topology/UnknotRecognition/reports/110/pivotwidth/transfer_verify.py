"""Independent transfer-table optimality checker; no producer imports.

Uses named vertices and frozensets rather than positional matching bit masks.
Every product entry is checked against every possible intermediate state.
"""
from itertools import permutations


def reference_transfer(program):
    inputs=program.get('inputs',[])
    kinds={}; initial={}
    for spec in inputs:
        name,side,w=spec['name'],spec['side'],spec.get('weight',0)
        if not isinstance(name,str) or not name or name in kinds or side not in ('R','C'):
            raise ValueError('bad input port')
        if type(w) is not int or w<0 or (side=='C' and w):raise ValueError('bad weight')
        kinds[name]=(side,w);initial[name]=(side,w)
    live=set(kinds);seen=set();events=[];fresh_weight=0
    for cmd in program.get('commands',[]):
        op=cmd['op']
        if op=='introduce':
            v,side,w=cmd['name'],cmd['side'],cmd.get('weight',0)
            if not isinstance(v,str) or not v or v in kinds or side not in ('R','C'):
                raise ValueError('bad introduced vertex')
            if type(w) is not int or w<0 or (side=='C' and w):raise ValueError('bad weight')
            kinds[v]=(side,w);live.add(v);fresh_weight+=w
            events.append((op,v))
        elif op=='forget':
            v=cmd['name']
            if v not in live:raise ValueError('bad forget')
            live.remove(v);events.append((op,v))
        elif op=='edge':
            r,c,x=cmd['row'],cmd['column'],cmd['count'];allowed=cmd.get('allowed',x==1)
            if r not in live or c not in live or kinds[r][0]!='R' or kinds[c][0]!='C':
                raise ValueError('bad edge endpoint')
            if type(x) is not int or x<=0 or type(allowed) is not bool or (allowed and x!=1):
                raise ValueError('bad edge coefficient')
            if (r,c) in seen or (r in initial and c in initial):raise ValueError('non-fresh or duplicate edge')
            seen.add((r,c));events.append((op,r,c,allowed,kinds[r][1]))
        else:raise ValueError('unsupported operation')
    output=program.get('outputs',{})
    if set(output)!=live or len(set(output.values()))!=len(live):raise ValueError('bad output map')
    if any(not isinstance(v,str) or not v for v in output.values()):raise ValueError('bad output label')
    final={output[v]:kinds[v] for v in live}
    def space(names):
        return [(tuple(p),frozenset(p[k] for k in range(len(p)) if mask>>k&1))
                for p in permutations(sorted(names)) for mask in range(1<<len(names))]
    ss,tt=space(initial),space(final);ti={s:i for i,s in enumerate(tt)}
    result=[[None]*len(tt) for s in ss]
    for i,state in enumerate(ss):
        tab={state:0}
        for event in events:
            nxt={}
            def put(s,v):
                if s not in nxt or v>nxt[s]:nxt[s]=v
            for (order,flags),score in tab.items():
                op=event[0]
                if op=='introduce':
                    for j in range(len(order)+1):
                        put((order[:j]+(event[1],)+order[j:],flags),score)
                elif op=='forget':
                    v=event[1]
                    put((tuple(x for x in order if x!=v),flags-{v}),score)
                else:
                    _,r,c,allowed,w=event
                    if order.index(r)<order.index(c):put((order,flags),score)
                    elif allowed and r not in flags and c not in flags:
                        put((order,flags|{r,c}),score+w)
            tab=nxt
        for (order,flags),score in tab.items():
            renamed=(tuple(output[v] for v in order),frozenset(output[v] for v in flags))
            result[i][ti[renamed]]=score
    return result,ss,initial,final,fresh_weight


def verify_power(certificate):
    if certificate.get('schema')!='ordered-pivot-power-v1':raise ValueError('bad schema')
    exponent=certificate.get('exponent')
    if type(exponent) is not int or exponent<0:raise ValueError('bad exponent')
    base,states,initial,final,fresh_weight=reference_transfer(certificate['program'])
    if initial!=final:raise ValueError('interface types do not match')
    n=len(base);nodes=certificate['nodes'];root=certificate['root']
    if not isinstance(nodes,list) or type(root) is not int or not 0<=root<len(nodes):
        raise ValueError('bad proof inventory')
    tables=[];lengths=[]
    for k,node in enumerate(nodes):
        a=node['matrix']
        if len(a)!=n or any(len(row)!=n for row in a):raise ValueError('bad table shape')
        if any(x is not None and (type(x) is not int or x<0) for row in a for x in row):
            raise ValueError('bad table value')
        kind=node['kind']
        if kind=='identity':
            if a!=[[0 if i==j else None for j in range(n)] for i in range(n)]:
                raise ValueError('bad identity')
            length=0
        elif kind=='template':
            if a!=base:raise ValueError('template table does not replay')
            length=1
        elif kind=='product':
            left,right=node['left'],node['right']
            if any(type(x) is not int or not 0<=x<k for x in (left,right)):
                raise ValueError('cyclic or out-of-order product reference')
            b,c=tables[left],tables[right];mid=node['middle']
            if len(mid)!=n or any(len(row)!=n for row in mid):raise ValueError('bad witness shape')
            for i in range(n):
                for j in range(n):
                    attained=None
                    for ell in range(n):
                        if b[i][ell] is not None and c[ell][j] is not None:
                            val=b[i][ell]+c[ell][j]
                            if attained is None or val>attained:attained=val
                    if a[i][j]!=attained:raise ValueError('product upper/lower bound failure')
                    ell=mid[i][j]
                    if attained is None:
                        if ell is not None:raise ValueError('spurious finite witness')
                    elif (type(ell) is not int or not 0<=ell<n or b[i][ell] is None
                          or c[ell][j] is None or b[i][ell]+c[ell][j]!=attained):
                        raise ValueError('invalid maximizing witness')
            length=lengths[left]+lengths[right]
        else:raise ValueError('unsupported proof node')
        if type(node['length']) is not int or node['length']!=length:raise ValueError('bad power length')
        tables.append(a);lengths.append(length)
    if lengths[root]!=exponent:raise ValueError('wrong exponent at proof root')
    best=max(x for i,s in enumerate(states) if not s[1] for x in tables[root][i] if x is not None)
    total=sum(t[1] for t in initial.values())+exponent*fresh_weight
    if certificate['retained_weight']!=best or certificate['deferred_weight']!=total-best:
        raise ValueError('incorrect optimal objective')
    return {'valid':True,'retained_weight':best,'deferred_weight':total-best,
            'proof_nodes':len(nodes),'scope':'optimal abstract repeated-template value'}
