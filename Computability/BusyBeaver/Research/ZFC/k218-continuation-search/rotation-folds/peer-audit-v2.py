"""Own static output/family audit. No root script imports or candidate replay."""
from pathlib import Path
from collections import Counter, defaultdict
from functools import lru_cache
import gzip
import hashlib
import itertools
import json

ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
P=Path('/tmp/k218-rotationfold');OUT=Path(__file__).resolve().parent
pins={};checks=0
def pin(p):
    pins[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest();return p
def require(test):
    global checks
    assert test;checks+=1
def readj(p):return json.loads(pin(p).read_text())
def table(p):
    rows={};start=[]
    for line in pin(p).read_text().splitlines():
        if line.startswith('#! start '):start.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();key=(int(q),int(b));require(key not in rows)
            rows[key]=(int(w),{'L':-1,'R':1}[d],int(z))
    require(start==[0]);require(len(rows)==436)
    states={q for q,b in rows};require(len(states)==218)
    require(set(rows)=={(q,b)for q in states for b in (0,1)})
    require(all(z in states|{254}for w,d,z in rows.values()))
    return rows
def tree(rows):
    leaves={p:(op,arg)for p,op,arg in rows};require(len(leaves)==len(rows))
    def descend(path):
        if path in leaves:return leaves[path]
        return descend(path+'0'),descend(path+'1')
    return descend('')
def leaf(t):return isinstance(t[0],str)
def sites(t,path=''):
    return [[path,*t]] if leaf(t) else sites(t[0],path+'0')+sites(t[1],path+'1')
@lru_cache(None)
def boundary(t):
    if leaf(t):
        op,n=t
        return (1,0,False)if op=='CD'else(n,0,False)if op=='CB'else(0,n,False)if op=='CC'else(0,0,op=='CH')
    a,b=map(boundary,t)
    return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0),a[2]or b[2]
def replacement(t,old,new):
    return new if t==old else t if leaf(t)else tuple(replacement(x,old,new)for x in t)
def graph(rows):
    intervals={}
    for i,(path,op,n)in enumerate(rows):
        for length in range(len(path)+1):
            p=path[:length]
            if p not in intervals:intervals[p]=[i,i+1]
            else:intervals[p][1]=i+1
    result=[]
    for i,(path,op,n)in enumerate(rows):
        def jump(bit,count):
            p=path
            while p:
                edge,p=p[-1],p[:-1]
                if edge==bit:
                    count-=1
                    if count==0:return intervals[p][1]%len(rows)if bit=='0'else intervals[p][0]
            return 0
        after=(i+1)%len(rows)
        targets=[after]if op=='CI'else[jump('0',1),after]if op=='CD'else[jump('0',n)]if op=='CB'else[jump('1',n)]if op=='CC'else[]
        result.append((op,n,targets))
    return result

# Prefix binding is a source construction check, not a primitive runtime proof.
def internal_binding(t,rows):
    bindings=defaultdict(set);paths=defaultdict(list)
    def visit(node,path,state):
        if leaf(node):return
        bindings[state].add(node);paths[state].append(path)
        for bit in (0,1):
            if leaf(node[bit]):continue
            tape={i:int(b)for i,b in enumerate(path+str(bit))};tape[-1]=1
            original=dict(tape);head=len(path);q=state
            for _ in range(100):
                if head==len(path)+1:break
                require(head in tape)
                w,d,q=rows[q,tape[head]];tape[head]=w;head+=d
            require(head==len(path)+1 and tape==original)
            visit(node[bit],path+str(bit),q)
    visit(t,'',84)
    return dict(bindings),paths

layouts={};construction=[]
for seed in ('primary','contextual'):
    census=readj(P/seed/'census.json');base=Path(census['seed'])
    original_rows=readj(base/'sites218.json');original_tree=tree(original_rows)
    original_table=table(base/'k218.native.tm');binding,paths=internal_binding(original_tree,original_table)
    baseline_graph=graph(original_rows)
    require(len(census['rotations'])==(12 if seed=='primary' else 13))
    for rotation in census['rotations']:
        q,r,edge=map(rotation.get,('q','r','edge'));name=rotation['name'];folder=P/seed/name
        require(len(binding[q])==len(binding[r])==1)
        node=next(iter(binding[q]));require(binding[r]=={node[edge]})
        require({key for key,act in original_table.items()if act[2]==r}=={(q,edge)})
        require(all(original_table[z,b][:2]==(b,1)for z in (q,r)for b in(0,1)))
        if edge==0:
            (a,b),c=node;newnode=a,(b,c)
            changes={(q,0):(0,1,original_table[r,0][2]),(q,1):(1,1,r),
                     (r,0):(0,1,original_table[r,1][2]),(r,1):(1,1,original_table[q,1][2])}
        else:
            a,(b,c)=node;newnode=(a,b),c
            changes={(q,0):(0,1,r),(q,1):(1,1,original_table[r,1][2]),
                     (r,0):(0,1,original_table[q,0][2]),(r,1):(1,1,original_table[r,0][2])}
        require(all(boundary(x)==(0,0,False)for x in(a,b,c)))
        expected_tree=replacement(original_tree,node,newnode)
        newrows=readj(folder/'sites.json');require(newrows==sites(expected_tree))
        require(newrows[:37]==original_rows[:37])
        require([x[1:]for x in newrows]==[x[1:]for x in original_rows])
        require(graph(newrows)==baseline_graph)
        newtable=table(folder/'native.tm');require(newtable==dict(original_table,**{})|changes)
        actual,_=internal_binding(expected_tree,newtable)
        expected={z:{replacement(t,node,newnode)for t in ts}for z,ts in binding.items()}
        expected[r]={newnode[1-edge]};require(actual==expected)
        require(rotation['occurrences']==len(paths[q]))
        require(rotation['changed_rows']==[list(k)+list(newtable[k])for k in sorted(newtable)if newtable[k]!=original_table[k]])
        # Reconstruct the finite specification family only; never run its filter.
        states={q for q,b in newtable};changed={q,r};specs={}
        for keep,drop in itertools.permutations(sorted(states),2):
            phi=lambda z:keep if z==drop else z
            actions=[{(newtable[z,b][0],newtable[z,b][1],phi(newtable[z,b][2]))for z in(keep,drop)}for b in(0,1)]
            shared=[b for b in(0,1)if len(actions[b])==1]
            affected=bool({keep,drop}&changed)
            if affected:
                for x,y in itertools.product(*actions):specs[(keep,drop,x,y)]='inherited'
            if len(shared)==1:
                fixed=shared[0];fixedact=next(iter(actions[fixed]))
                targets=(states|{254})-{drop}if affected else changed-{drop}
                for act in itertools.product((0,1),(-1,1),targets):
                    pair=(fixedact,act)if fixed==0 else(act,fixedact)
                    specs.setdefault((keep,drop,*pair),'changed_pair'if affected else'changed_helper')
        layouts[seed,name]=specs
        construction.append({'seed':seed,'rotation':name,'source_leaves':len(newrows),
                             'specifications':len(specs),'families':dict(Counter(specs.values()))})

result=readj(P/'search1/result.json');require(result['status']=='BOUNDED_FAMILY_COMPLETE'and result['hits']==[])
require(len(result['rotations'])==len(layouts)==25)
resultmap={(r['seed'],r['rotation']):r for r in result['rotations']}
observed=Counter();id_=0
stream=pin(P/'search1/rejects.jsonl.gz')
with gzip.open(stream,'rt')as inp:
    for line in inp:
        row=json.loads(line);id_+=1;require(row['id']==id_)
        layout=row['seed'],row['rotation'];spec=(row['keep'],row['drop'],*map(tuple,row['rows']))
        require(layout in layouts and spec in layouts[layout])
        family=layouts[layout].pop(spec);require(row['family']==family)
        require(row['witness']['radius']==7 and row['witness']['fuel']==97)
        require(row['witness']['old_row'][0]in(row['keep'],row['drop']))
        observed[layout,family]+=1
for item in construction:
    layout=item['seed'],item['rotation'];require(not layouts[layout])
    stats=resultmap[layout]['stats'];require(stats['attempts']==stats['filter_rejected']==item['specifications'])
    for family,n in item['families'].items():require(stats[family]==n==observed[layout,family])
require(id_==result['total']==sum(x['specifications']for x in construction)==282416)
for p in [P/'census.py',P/'census-attempt1.py',P/'search.py',
          ROOT/'Computability/BusyBeaver/Research/ZFC/k218-continuation-search/filter_source.py',
          ROOT/'Computability/BusyBeaver/Research/ZFC/k218-continuation-search/check_joint_fold.py',
          ROOT/'Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/pricing/source_language.py',
          ROOT/'Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/pricing/build221.py',Path(__file__)]:pin(p)
receipt={'status':'STATIC_CONSTRUCTION_AND_FULL_STREAM_AUDIT_PASS','checks':checks,'inputs':pins,
         'layouts':construction,'specifications':id_,'scope':'Own literal construction/internal-prefix, source CFG and family-stream metadata checks. No root code imports, window-domain replay, candidate filter replay, primitive runtime or startup claim.'}
(OUT/'audit-result.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':receipt['status'],'checks':checks,'layouts':len(construction),'specifications':id_}))
