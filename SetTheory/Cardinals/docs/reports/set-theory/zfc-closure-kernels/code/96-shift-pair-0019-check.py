import sys as _assertion_sys
if not __debug__ or _assertion_sys.flags.optimize:
    raise RuntimeError("Assertions must be enabled; do not use -O or PYTHONOPTIMIZE.")
"""Independent data-only audit. No imported project or companion-checker code."""
import json, hashlib, collections, functools, re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'generated'
OUT=BASE/'independent-review'
OUT.mkdir(parents=True,exist_ok=True)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def decode(data):
    active=set()
    @functools.lru_cache(None)
    def node(i):
        assert i not in active
        active.add(i)
        a,b=data['nodes'][i];ans=('N',edge(a),edge(b));active.remove(i);return ans
    def edge(e):return node(e[1]) if e[0]=='ref' else tuple(e)
    return edge(data['root'])

def cfg(tree, helpers=None, wrap=False):
    leaves=[];entry={};interval={};unique=set()
    def index(t,path):
        entry[path]=len(leaves)
        if t[0]=='N':
            unique.add(t);index(t[1],path+(0,));index(t[2],path+(1,))
        else:leaves.append(t)
        if helpers:
            for name,h in helpers.items():
                if t==h:interval.setdefault(entry[path],[]).append((name,len(leaves)))
    index(tree,())
    edges=[None]*len(leaves)
    def target(stack,k):return stack[k-1] if k<=len(stack) else (0 if wrap else -2)
    def build(t,path,after,breaks,continues):
        if t[0]=='N':
            build(t[1],path+(0,),entry[path+(1,)],(after,)+breaks,continues)
            build(t[2],path+(1,),after,breaks,(entry[path],)+continues)
        else:
            k=t[0];n=entry[path]
            if k=='D':edges[n]=(after,target(breaks,1))
            elif k=='B':edges[n]=(target(breaks,t[1]),)
            elif k=='C':edges[n]=(target(continues,t[1]),)
            elif k=='I':edges[n]=(after,)
            elif k=='H':edges[n]=(-3,)
            else:raise ValueError(t)
    build(tree,(),0 if wrap else -1,(),())
    return leaves,edges,interval,len(unique)

def execute(graph,reg,limit=400000):
    leaves,edges,_,_=graph;pc=0;steps=0
    while pc>=0:
        assert steps<limit;steps+=1;t=leaves[pc];k=t[0]
        if k=='I':reg[t[1]]+=1;pc=edges[pc][0]
        elif k=='D':
            if reg[t[1]]:reg[t[1]]-=1;pc=edges[pc][0]
            else:pc=edges[pc][1]
        else:pc=edges[pc][0]
    assert pc==-1,pc
    return steps

def E(a,b):return (1<<a)*(2*b+1)-1
def U(n):
    v=n+1;a=(v&-v).bit_length()-1
    return a,((v>>a)-1)//2

def helper_tests(data):
    result={};maxsteps=0
    for name,d in data.items():
        graph=cfg(decode(d));count=0
        if name=='pair':
            for a in range(9):
              for b in range(15):
                r=[11, b, 13, 17, 19, 23, a, 0, 29];want=r[:]
                want[1]=want[6]=0;want[7]=E(a,b)
                maxsteps=max(maxsteps,execute(graph,r));assert r==want;count+=1
        else:
            s=8 if name=='unpairL' else 2
            for n in range(4097):
                r=[11,13,17,19,23,29,0,0,31];r[s]=n;want=r[:]
                want[s]=0;want[6],want[7]=U(n)
                maxsteps=max(maxsteps,execute(graph,r));assert r==want;count+=1
        result[name]={'cases':count,'leaves':len(graph[0]),'dag_nodes':graph[3]}
    result['max_primitive_steps']=maxsteps
    return result

def clean_closure(source,helpers):
    graph=cfg(decode(source),{k:decode(v) for k,v in helpers.items()},True)
    leaves,edges,markers,nodes=graph
    seen=[set() for _ in leaves];queue=collections.deque([(0,(1<<0)|(1<<4))]);seen[0].add((1<<0)|(1<<4))
    observed=collections.defaultdict(set);count=0
    def offer(q,m,prev):
        if q<0:
            assert q==-3
            return
        for name,end in markers.get(q,[]):
            if not q<=prev<end:observed[name].add(m)
        if m not in seen[q]:seen[q].add(m);queue.append((q,m))
    while queue:
        pc,m=queue.popleft();count+=1;t=leaves[pc];k=t[0]
        if k=='I':offer(edges[pc][0],m|1<<t[1],pc)
        elif k=='D':
            bit=1<<t[1]
            if m&bit:
                offer(edges[pc][0],m,pc);offer(edges[pc][0],m&~bit,pc)
            else:offer(edges[pc][1],m,pc)
        else:offer(edges[pc][0],m,pc)
    assert set(observed)==set(helpers)
    assert all(not m&((1<<6)|(1<<7)) for name in ('unpairL','unpairW') for m in observed[name])
    assert all(not m&(1<<7) for m in observed['pair'])
    return {'leaves':len(leaves),'dag_nodes':nodes,'abstract_states':count,
            'helper_occurrences':sum(map(len,markers.values())),
            'external_entry_masks':{k:sorted(v) for k,v in observed.items()},
            'all_external_helper_entries_clean':True,
            'method':'Independent continuation-stack CFG; sound zero/positive fixed point, exact logical seed support N,D'}

source_path=ROOT/'inputs/Dag254.v'
assert sha(source_path)=='538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3', 'Pinned Dag254.v hash mismatch'
source_text=source_path.read_text()
raw={}
for match in re.finditer(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',source_text):
    def parse(word):
        fields=word.split();kind={'ENode':'ref','EInc':'I','EDecnz':'D','EBreak':'B','EContinue':'C','EHalt':'H'}[fields[0]]
        return (kind,int(fields[1])) if len(fields)>1 else (kind,)
    raw[int(match[1])]=(parse(match[2]),parse(match[3]))
assert len(raw)==219

def lower_original(replacements):
    @functools.lru_cache(None)
    def visit(i):
        if i in replacements:return replacements[i]
        a,b=raw[i]
        return ('N',edge(a),edge(b))
    def edge(t):return visit(t[1]) if t[0]=='ref' else t
    return visit(0)
original_graph=cfg(lower_original({}),wrap=True)
assert len(original_graph[0])==6460 and original_graph[3]==219
result={'status':'PASS','scope':'Finite pairing/helper tests and inductive clean-entry certificate; no literal TM or formal-kernel claim','input_sha256':{}}
for n in range(1<<16):
    a,b=U(n);assert E(a,b)==n and a<=n and b<=n
    assert b<=n//2 and (a<n or n in (0,1))
for a in range(33):
    for b in range(257):
        n=E(a,b);assert U(n)==(a,b) and n>=a+b
        assert (n==a+b)==((a,b) in ((0,0),(1,0)))
result['original_source']={'leaves':len(original_graph[0]),'dag_nodes':original_graph[3],'sha256':sha(source_path)}
result['pairing_checks']={'inverse_inputs':65536,'forward_pairs':33*257}
for suffix,prefix in [('', 'shifted'),('best-','best-shifted')]:
    helperpath=BASE/(suffix+'helpers.json');sourcepath=BASE/(prefix+'-source.json')
    h=json.loads(helperpath.read_text());s=json.loads(sourcepath.read_text())
    reconstructed=lower_original({115:decode(h['unpairL']),116:decode(h['unpairW']),162:decode(h['pair'])})
    assert reconstructed==decode(s), 'Replacement source mismatch'
    result[prefix]={'exact_source_replacement_only':True,'helper_tests':helper_tests(h),'source_closure':clean_closure(s,h)}
    for p in (helperpath,sourcepath):result['input_sha256'][p.name]=sha(p)
graphs={}
for suffix in ('','best-'):
    h=json.loads((BASE/(suffix+'helpers.json')).read_text())
    graphs[suffix or 'initial']={}
    for name, data in h.items():
        g=cfg(decode(data));graphs[suffix or 'initial'][name]=[{'pc':i,'op':t,'edges':g[1][i]} for i,t in enumerate(g[0])]
def semantic_graph(rows):
    return [(r['op'][0] if r['op'][0] in ('I','D') else 'J',r['op'][1] if r['op'][0] in ('I','D') else None,tuple(r['edges'])) for r in rows]
expected_pair=[('D',1,(1,4)),('I',7,(2,)),('I',7,(3,)),('J',None,(0,)),('D',6,(5,-1)),('D',7,(6,9)),('I',1,(7,)),('I',1,(8,)),('J',None,(5,)),('D',1,(10,12)),('I',7,(11,)),('J',None,(9,)),('I',7,(13,)),('J',None,(4,))]
def expected_inverse(s):
    return [('D',s,(1,2)),('J',None,(3,)),('J',None,(-1,)),('D',s,(4,6)),('I',7,(5,)),('J',None,(0,)),('I',6,(7,)),('D',7,(8,10)),('I',s,(9,)),('J',None,(7,)),('J',None,(0,))]
for version,hs in graphs.items():
    assert semantic_graph(hs['pair'])==expected_pair
    assert semantic_graph(hs['unpairL'])==expected_inverse(8)
    assert semantic_graph(hs['unpairW'])==expected_inverse(2)
result['helper_unbounded_lemma_binding']='PASS: all six helper CFGs exactly match the explicit loop normal forms proved in REVIEW.md'
(OUT/'helper_cfgs.json').write_text(json.dumps(graphs,indent=2)+'\n')
result['input_sha256']['proof/REPORT.md']=sha(ROOT/'proof/REPORT.md')
(OUT/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
