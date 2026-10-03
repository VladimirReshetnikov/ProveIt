#!/usr/bin/env python3
"""Materialize Morita1996 constructions. No macro remains in source.json."""
import json,hashlib
from collections import defaultdict,Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent
DEP=ROOT/'dependency'
PRIMES=(2,3,5,7,11)
SEEN={}
def write(name,data): (ROOT/name).write_text(json.dumps(data,indent=2)+'\n')
def machine(k,entry='START',halt='HALT'): return dict(counters=k,start=entry,halt=halt,controls=[],rows=[])
def add(M,name,s,i,x,t):
    seen=SEEN.setdefault(id(M),set(M['controls'])) if id(M) not in SEEN else SEEN[id(M)]
    for q in (s,t):
        if q not in seen: M['controls'].append(q);seen.add(q)
    M['rows'].append(dict(name=name,source=s,counter=i,symbol=x,target=t))
def group(rows,key):
    d=defaultdict(list)
    for e in rows:d[e[key]].append(e)
    return d
def overlap(a,b):return a['counter']!=b['counter'] or a['symbol']==b['symbol'] or a['symbol'] in '+-0' or b['symbol'] in '+-0'
def main():
    SEEN.clear()
    if hashlib.sha256((DEP/'virtual3.json').read_bytes()).hexdigest()!='24c771db50dc621068e470227802c2710a4531ce2e7ad3703a5cdb6b0543bbcf':raise ValueError('Three-counter dependency hash mismatch')
    V=json.loads((DEP/'virtual3.json').read_text());M=machine(3)
    add(M,'entry','START',0,'0',V['entry'])
    for n,(q,row) in enumerate(V['rows'].items()):
        op,i,*dst=row;a=f'v{n:04}'
        if op=='ADD':add(M,a,q,i,'+',dst[0])
        else:
            add(M,a+'z',q,i,'Z',dst[1]);add(M,a+'p',q,i,'P',a+'d');add(M,a+'d',a+'d',i,'-',dst[0])
    write('primitive3.json',M)
    N=json.loads(json.dumps(M));ins=group(N['rows'],'target');norm=[]
    for j,(t,es) in enumerate(ins.items()):
        if len(es)<=2: continue
        chain=[f'n{j:04}_{h}' for h in range(len(es)-2)]
        N['controls'].extend(chain);SEEN[id(N)]=set(N['controls'])
        for h,e in enumerate(es): e['target']=chain[max(0,h-1)] if h<len(es)-1 else t
        for h,q in enumerate(chain):add(N,f'n{j:04}e{h}',q,0,'0',chain[h+1] if h+1<len(chain) else t)
        norm.append(dict(target=t,incoming=[e['name'] for e in es],chain=chain))
    write('normalized3.json',N)
    R=machine(5);R['controls']=list(N['controls']);hist=[]
    for j,(t,es) in enumerate(group(N['rows'],'target').items()):
        if len(es)<2 or not overlap(*es):
            for e in es:add(R,e['name'],e['source'],e['counter'],e['symbol'],t)
            continue
        prefix=f'h{j:04}';d=[prefix+f'D{h}' for h in range(1,7)];part=[]
        for b,e in enumerate(es):
            a=[prefix+f'B{b}T{h}' for h in range(1,6)];part.append(a)
            graph=[(e['source'],e['counter'],e['symbol'],a[0]),(a[0],4,'Z',a[1]),(a[1],3,'Z',d[0] if b==0 else d[4]),(a[1],3,'P',a[2]),(a[2],3,'-',a[3]),(a[3],4,'+',a[4]),(a[4],4,'P',a[1])]
            for z,(s,i,x,u) in enumerate(graph):add(R,prefix+f'b{b}r{z}',s,i,x,u)
        graph=[(d[0],4,'Z',t),(d[0],4,'P',d[1]),(d[1],4,'-',d[2]),(d[2],3,'+',d[3]),(d[3],3,'P',d[4]),(d[4],3,'+',d[5]),(d[5],3,'P',d[0])]
        for z,(s,i,x,u) in enumerate(graph):add(R,prefix+f'd{z}',s,i,x,u)
        hist.append(dict(target=t,incoming=[e['name'] for e in es],parts=part,doubling=d,prefix=prefix))
    write('reversible5.json',R)
    P=machine(2);P['controls']=list(R['controls']);prime=[];restores={}
    incoming=group(R['rows'],'target')
    for q,es in incoming.items():
        if es[0]['symbol'] in 'ZP':restores[q]=dict(prime=PRIMES[es[0]['counter']],prefix=f'r{R["controls"].index(q):05}')
    for j,(q,es) in enumerate(group(R['rows'],'source').items()):
        pref=f'p{j:05}';x=es[0]['symbol'];p=PRIMES[es[0]['counter']];g=[]
        if x=='0':
            e=es[0];g=[(q,0,'0',e['target'])];prime.append(dict(kind='0',source=q,target=e['target'],prefix=pref,rows=[e['name']]))
        elif x in '+-':
            e=es[0];a=lambda n:pref+f'S{n}'
            g=[(q,1,'Z',a(1)),(a(1),0,'Z',a(5)),(a(1),0,'P',a(2)),(a(2),0,'-',a(3)),(a(3),1,'+',a(4)),(a(4),1,'P',a(1)),(a(5),1,'Z',e['target'])]
            if x=='+':
                g.extend([(a(5),1,'P',a(6)),(a(6),1,'-',pref+'C0')])
                for h in range(p):g.append((pref+f'C{h}',0,'+',pref+f'C{h+1}' if h<p-1 else a(7)))
            else:
                g.append((a(5),1,'P',pref+'C0'))
                for h in range(p):g.append((pref+f'C{h}',1,'-',pref+f'C{h+1}' if h<p-1 else a(6)))
                g.append((a(6),0,'+',a(7)))
            g.append((a(7),0,'P',a(5)))
            prime.append(dict(kind=x,source=q,target=e['target'],prime=p,prefix=pref,rows=[e['name']]))
        else:
            targets={e['symbol']:e['target'] for e in es};a=lambda h,v:pref+f'R{h}T{v}'
            g.append((q,1,'Z',a(0,1)))
            for h in range(p):
                symbol='P' if h==0 else 'Z'
                if symbol in targets:g.append((a(h,1),0,'Z',restores[targets[symbol]]['prefix']+f'R{h}T1'))
                g.extend([(a(h,1),0,'P',a(h,2)),(a(h,2),0,'-',a(h+1,1))])
            g.extend([(a(p,1),1,'+',a(p,2)),(a(p,2),1,'P',a(0,1))])
            prime.append(dict(kind='test',source=q,targets=targets,prime=p,prefix=pref,rows=[e['name'] for e in es]))
        for h,(s,i,x,t) in enumerate(g):add(P,pref+f'e{h}',s,i,x,t)
    for q,c in restores.items():
        p=c['prime'];pref=c['prefix'];a=lambda h,v:pref+f'R{h}T{v}'
        g=[(a(0,1),1,'Z',q),(a(0,1),1,'P',a(0,2)),(a(0,2),1,'-',a(p,1))]
        for h in range(p,0,-1):g.extend([(a(h,1),0,'+',a(h,2)),(a(h,2),0,'P',a(h-1,1))])
        for h,(s,i,x,t) in enumerate(g):add(P,pref+f'e{h}',s,i,x,t)
    write('reversible2-primitives.json',P)
    S=dict(schema='reversible-two-counter-v1',controls=P['controls'],start=P['start'],halt=P['halt'],class_cut=0,branches=[])
    for e in P['rows']:
        x=e['symbol'];i=e['counter'];guard={'op':'true'}
        if x in 'ZP-':guard=dict(op='eq' if x=='Z' else 'gt',counter=i,value=0)
        S['branches'].append(dict(name=e['name'],source=e['source'],target=e['target'],side=-1 if i==0 else 1,delta={'+':1,'-':-1}.get(x,0),guard=guard))
    write('source.json',S)
    write('certificates.json',dict(normalization=norm,history=hist,prime=prime,restoration=restores))
    stats={k:dict(controls=len(m['controls']),rows=len(m['rows']),symbols=dict(Counter(e['symbol'] for e in m['rows']))) for k,m in [('primitive3',M),('normalized3',N),('reversible5',R),('reversible2',P)]}
    stats['collision_pairs']=len(hist);stats['normalization_targets']=len(norm)
    write('build-stats.json',stats);print(json.dumps(stats,indent=2))
if __name__=='__main__':main()
