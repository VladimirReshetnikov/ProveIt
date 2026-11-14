#!/usr/bin/env python3
"""Exhaust six independent permutations of PA196's six logical heads.

The objective is primitive-program DAG size with the inherited tree association.
This is a search score, not a compiled TM state count.
"""
import ast, itertools, json, re, time
from functools import lru_cache
from pathlib import Path

BASE=Path(__file__).resolve().parents[2]
UP=BASE/'sources/BusyBeaver'
OUT=BASE/'work/logic/role_search'
OUT.mkdir(exist_ok=True)

class Dag:
    def __init__(self): self.nodes=[]; self.ids={}; self.sizes=[]
    def add(self,k):
        if k not in self.ids:
            self.ids[k]=len(self.nodes);self.nodes.append(k)
            self.sizes.append(1 if isinstance(k[0],str) else self.sizes[k[0]]+self.sizes[k[1]])
        return self.ids[k]
    @lru_cache(None)
    def node_set(self,i):
        k=self.nodes[i]
        return frozenset({i}) if isinstance(k[0],str) else frozenset({i})|self.node_set(k[0])|self.node_set(k[1])
    @lru_cache(None)
    def expand(self,i):
        k=self.nodes[i]
        return k if isinstance(k[0],str) else (self.expand(k[0]),self.expand(k[1]))

dag=Dag();env={}
def parse(ts):
    t=ts.pop(0)
    if t=='(':
        x=parse(ts);assert ts.pop(0)==')';return x
    if t=='.node': return dag.add((parse(ts),parse(ts)))
    if t=='.leaf': return parse(ts)
    if t in ['.dec','.inc','.breakTo','.continueTo']:
        return dag.add(({'.dec':'CD','.inc':'CI','.breakTo':'CB','.continueTo':'CC'}[t],int(ts.pop(0))))
    if t=='.halt': return dag.add(('CH',None))
    return env[t]
for ln in (UP/'PA196/Program.lean').read_text().splitlines():
    m=re.fullmatch(r'def (\w+) : Tree := (.*)',ln)
    if m:
        ts=re.findall(r'\(|\)|\.\w+|\w+',m[2]);env[m[1]]=parse(ts);assert not ts
root=env['trie'];assert dag.sizes[root]==3812
regions=[(503,786),(786,1085),(1085,1381),(1381,1677),(1677,1908),(1908,2258)]

spans={}
def locate(i,lo=0,path=''):
    hi=lo+dag.sizes[i];spans[lo,hi]=(i,path)
    k=dag.nodes[i]
    if not isinstance(k[0],str):
        locate(k[0],lo,path+'0');locate(k[1],lo+dag.sizes[k[0]],path+'1')
locate(root)
blocks=[(a,int(b),int(c)) for a,b,c in re.findall(r'\(\.(\w+), (\d+), (\d+)\)',(UP/'PA196/Source/AXProgram.lean').read_text().split('def program')[0])]
macros={}
for t,lo,hi in blocks:
    if t in ('copyD','copyH','copyA'):
        i,p=spans[lo,hi]
        if t in macros: assert macros[t]==i
        macros[t]=i
roles={macros['copy'+r]:r for r in 'DHA'}
perms=list(itertools.permutations('DHA'))
edits={}
for t,lo,hi in blocks:
    if t not in macros:continue
    owner=next((i for i,(a,b) in enumerate(regions) if a<=lo<hi<=b),None)
    if owner is not None:
        inode,path=spans[lo,hi]
        edits[path]=(owner,tuple(macros['copy'+p['DHA'.index(roles[inode])]] for p in perms))

fixed=set();unchanged=set();selector_nodes=set()
templates=[];template_ids={};sizes=[];dependencies=[]
prefixes={p[:j] for p in edits for j in range(len(p))}
def templ(i,p=''):
    if p in edits:
        owner,vs=edits[p];k=('choice',owner,vs)
        for v in vs:selector_nodes.update(dag.node_set(v));fixed.update(dag.node_set(v))
    elif p not in prefixes:
        k=('fixed',i);fixed.update(dag.node_set(i));unchanged.update(dag.node_set(i))
    else:
        left,right=dag.nodes[i];k=('pair',templ(left,p+'0'),templ(right,p+'1'))
    if k not in template_ids:
        template_ids[k]=len(templates);templates.append(k);sizes.append(dag.sizes[i])
        dependencies.append(frozenset() if k[0]=='fixed' else frozenset({k[1]}) if k[0]=='choice' else dependencies[k[1]]|dependencies[k[2]])
    return template_ids[k]
rt=templ(root);assert selector_nodes<=unchanged
by_size={}
for i,k in enumerate(templates):
    if k[0]=='pair':by_size.setdefault(sizes[i],[]).append(i)
fixed_sizes={dag.sizes[i] for i in fixed}
constant=0;amb=[]
for size,family in by_size.items():
    if len(family)==1 and size not in fixed_sizes:constant+=1
    else:amb.extend(family)

@lru_cache(None)
def instantiate(i,combo):
    k=templates[i]
    if k[0]=='fixed':return k[1]
    if k[0]=='choice':return k[2][combo[k[1]]]
    return dag.add((instantiate(k[1],combo),instantiate(k[2],combo)))

lookups=[]
for i in amb:
    coords=tuple(sorted(dependencies[i]));vals=[]
    for sub in itertools.product(range(6),repeat=len(coords)):
        combo=[0]*6
        for c,v in zip(coords,sub):combo[c]=v
        vals.append(instantiate(i,tuple(combo)))
    lookups.append((coords,vals))
allids=fixed|{v for _,vals in lookups for v in vals}
pos={v:i for i,v in enumerate(sorted(allids))};base=sum(1<<pos[i] for i in fixed)
bitlook=[(c,[1<<pos[v] for v in vals]) for c,vals in lookups]
leaf_count=sum(isinstance(dag.nodes[i][0],str) for i in fixed)
def score(combo):
    bits=base
    for coords,vals in bitlook:
        i=0
        for c in coords:i=i*6+combo[c]
        bits|=vals[i]
    return constant+bits.bit_count()-leaf_count

print('baseline',score((0,)*6),'regions',regions,'templates',len(templates),'ambiguous',len(amb),flush=True)
best=999;choices=[];hist={};start=time.monotonic()
for combo in itertools.product(range(6),repeat=6):
    s=score(combo);hist[s]=hist.get(s,0)+1
    if s<best:best=s;choices=[];print('newbest',best,combo,'at',time.monotonic()-start,flush=True)
    if s==best:choices.append(combo)

def sites(i,path=''):
    k=dag.nodes[i]
    if isinstance(k[0],str):return [(path,*k)]
    return sites(k[0],path+'0')+sites(k[1],path+'1')

report={'baseline_internal':score((0,)*6),'best_internal':best,'count':len(choices),'permutations':perms,'regions':regions,'histogram':hist,'choices':choices}
(OUT/'results.json').write_text(json.dumps(report,indent=2))
for j,c in enumerate(choices[:30]):
    i=instantiate(rt,tuple(c));assert len(dag.node_set(i))-leaf_count==best
    (OUT/f'candidate{j:03}.sites.json').write_text(json.dumps(sites(i)))
print('done',best,len(choices),time.monotonic()-start,flush=True)
