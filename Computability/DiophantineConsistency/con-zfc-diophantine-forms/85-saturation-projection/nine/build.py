#!/usr/bin/env python3
"""Saturated Pell certificate; source prefix retained as inert literal data."""
from pathlib import Path
import json, collections, hashlib
ROOT=Path(__file__).resolve().parent
OPS={'add','sub','mul'}

class Circuit:
    def __init__(self): self.nodes=[]; self.memo={}; self.names={}
    def emit(self,node):
        node=dict(node)
        if node['kind'] in ('add','mul') and node['left']>node['right']:
            node['left'],node['right']=node['right'],node['left']
        key=tuple(sorted(node.items()))
        if key not in self.memo:
            self.memo[key]=len(self.nodes); self.nodes.append(node)
        return self.memo[key]
    def c(self,n):return self.emit(dict(kind='literal',value=n))
    def b(self,k,a,b):return self.emit(dict(kind=k,left=a,right=b))
    def a(self,*xs):
        r=xs[0]
        for x in xs[1:]:r=self.b('add',r,x)
        return r
    def m(self,*xs):
        r=xs[0]
        for x in xs[1:]:r=self.b('mul',r,x)
        return r
    def s(self,a,b):return self.b('sub',a,b)
    def sq(self,a):return self.m(a,a)
    def save(self,k,v):self.names[k]=v;return v
    def export(self,output):
        live=set()
        def walk(i):
            if i in live:return
            live.add(i);n=self.nodes[i]
            if n['kind'] in OPS:walk(n['left']);walk(n['right'])
        walk(output)
        ids=sorted(live);remap={old:new for new,old in enumerate(ids)}
        nodes=[]
        for i in ids:
            n=dict(self.nodes[i])
            if n['kind'] in OPS:n.update(left=remap[n['left']],right=remap[n['right']])
            nodes.append(n)
        counts=collections.Counter(n['kind'] for n in nodes if n['kind'] in OPS)
        return dict(nodes=nodes,output=remap[output],named_nodes={k:remap[v] for k,v in self.names.items() if v in remap},total_operations=sum(counts.values()),operation_counts=dict(counts))

def build(domain,majorant='cheap',order=(0,1,2,3)):
    path=ROOT/'upstream'/('gap2082_'+domain+'.json')
    parent=json.loads(path.read_text()); d=Circuit(); old=parent['nodes']; oldnames=parent['named_nodes']; mapping={}
    def copy(i):
        if i in mapping:return mapping[i]
        n=dict(old[i])
        if n['kind'] in OPS:n.update(left=copy(n['left']),right=copy(n['right']))
        mapping[i]=d.emit(n);return mapping[i]
    def v(name):
        val=copy(oldnames[name]); d.names[name]=val;return val
    a,m,s,sq,c,save=d.a,d.m,d.s,d.sq,d.c,d.save
    # Retain the arithmetic source, ratio registers and carrier exactly.
    for name in ['b','B','ell','targets','N0','mask','Tcode','Usource','Gsource','Jcode','Scode','L','N','R','capbase','U','Y','M','P','K','A','B1','W1','C','J','Q','D','margin','Omega','E0','V0','a0']:
        v(name)
    A,C,J,D=v('A'),v('C'),v('J'),v('D')
    def var(name):return copy(next(i for i,n in enumerate(old) if n.get('kind')=='variable' and n.get('name')==name))
    i=var('i');j=var('j')
    if domain=='natural':i=a(i,c(1))
    else:j=s(j,c(1))
    save('i',i);save('j0',j)
    am1=save('am1',s(sq(A),c(1)))
    C2=save('C2',sq(C))
    e0=save('e0',m(i,J,C2))
    de=save('de',m(D,e0))
    F=save('F',a(m(am1,e0,de),c(1)))
    lam=save('Lambda',s(a(m(C,D),c(1)),A))
    G=save('G',a(A,m(F,lam)))
    Z=save('Z',a(v('B1'),m(j,C)))
    H=save('H',a(C,m(F,Z)))
    GH=save('GH',m(G,H))
    I=save('I',a(s(sq(GH),sq(H)),c(1)))
    raw_a1=save('raw_a1',m(D,F,I))
    if majorant=='cheap':
        a1=save('a1',raw_a1)
        T=save('Tmajor',m(A,de))
        V1=save('V1',m(T,GH))
    elif majorant=='radical':
        coords=[A,C,i,Z]
        powers={}
        def powcoord(k,e):
            if e==0:return c(1)
            if e==1:return coords[k]
            if (k,e) not in powers:
                h=powcoord(k,e//2);u=m(h,h)
                if e%2:u=m(u,coords[k])
                powers[k,e]=u
            return powers[k,e]
        def horner(terms,depth=0):
            if depth==4:
                assert len(terms)==1
                return c(terms[0][1])
            coord=order[depth];groups=collections.defaultdict(list)
            for ex,co in terms:groups[ex[coord]].append((ex,co))
            es=sorted(groups,reverse=True);prev=es[0];out=horner(groups[prev],depth+1)
            for e in es[1:]:
                out=a(m(out,powcoord(coord,prev-e)),horner(groups[e],depth+1));prev=e
            if prev:out=m(out,powcoord(coord,prev))
            return out
        records=json.loads((ROOT/'radical_upper_P.json').read_text())
        V1=save('V1',horner([(r['powers'],r['coefficient']) for r in records]))
        sigma=save('sigma',m(c(1024),powcoord(1,5),i))
        a1=save('a1',m(sq(sigma),raw_a1))
    else:raise ValueError(majorant)
    Omega,E0,V0,a0=v('Omega'),v('E0'),v('V0'),v('a0')
    theta=save('Theta',s(E0,m(Omega,a(V0,V1))))
    Om2=sq(Omega)
    inner=save('inner',s(sq(theta),m(Om2,a(a0,a1))))
    output=save('F9',s(sq(inner),m(c(4),sq(Om2),a0,a1)))
    result=d.export(output)
    result.update(variables=parent['variables'],domain=domain,exact_degree=1628768 if majorant=='cheap' else 1103950,
                  coefficient_recipes=parent['coefficient_recipes'],fixed_binding='fixed/BINDING.json',
                  parent_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  construction='one-factor Pell saturation, '+majorant+' majorant',
                  majorant=majorant,horner_order=order if majorant=='radical' else None,
                  source_metadata={k:parent[k] for k in ['W','height','Ecode','base_scale_exponent','threshold_b_power','threshold_B_power','threshold_scale_exponent','block_scale_power_of_two','source_sha256','layout_sha256','coherent_tuple','coefficient_bound_exponent']})
    return result

def main():
    receipts=[]
    for domain in ['positive','natural']:
        obj=build(domain);path=ROOT/('saturated_'+domain+'.json');path.write_text(json.dumps(obj,indent=2)+'\n')
        receipts.append({k:obj[k] for k in ['domain','total_operations','operation_counts','exact_degree']})
    (ROOT/'METRICS.json').write_text(json.dumps(receipts,indent=2)+'\n')
    print(json.dumps(receipts,indent=2))
if __name__=='__main__':main()
