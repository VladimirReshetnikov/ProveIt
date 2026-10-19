#!/usr/bin/env python3
"""Map scanner failures to annotated source contexts through segment bisimulation.

Reparses Dag254.v and relates it directly to the routed source. No bare
leaf-order identification is used: the compilations reorder some increments.
Between tests, every register's increment count is compared. Every guard
successor is explored, so the resulting relation is closed. This establishes
source context only; it makes no additional claim about the smaller TM.
"""
from pathlib import Path
from collections import Counter,defaultdict
import hashlib,json,os,re
HERE=Path(__file__).resolve().parent
BASE=Path(os.environ.get('ZFC245_REFERENCE',str(HERE.parent/'packages/zfc245-proof-20261018'))).resolve()
dag_path=BASE/'reference/source/Dag254.v';raw=dag_path.read_bytes()
term=r'(?:ENode \d+|EInc \d+|EDecnz \d+|EBreak \d+|EContinue \d+|EHalt)'
rows={int(q):(a,b,label)for q,a,b,label in re.findall(r'\| (\d+) => \(('+term+r'), ('+term+r')\)\s+\(\* (.*?) \*\)',raw.decode())}
assert sorted(rows)==list(range(219))
rename={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}
dag={};labels={}
def visit(edge,path,ancestors):
    tokens=edge.split();op=tokens[0];arg=int(tokens[1])if len(tokens)>1 else None
    if op=='ENode':
        a,b,label=rows[arg]
        visit(a,path+'0',ancestors+[label]);visit(b,path+'1',ancestors+[label])
    else:dag[path]=(rename[op],arg);labels[path]=ancestors
visit('ENode 0','',[]);assert len(dag)==6460
sites=json.loads((BASE/'certificate/sites_logical.json').read_text());source={p:(op,r)for p,op,r in sites}
bad={row['index']for row in json.loads((HERE/'shorter58-full-failures.json').read_text())['failures']}
assert len(bad)==50
bad_paths={sites[i][0]for i in bad}

def decode(program,word):
    path=''
    for i in range(128):
        path+=word[i]if i<len(word)else'0'
        if path in program:
            assert '1'not in word[len(path):]
            return path,program[path]
    raise AssertionError('Decoder depth')
def inc(word):
    if not word:return ''
    return format((int(word,2)+1)%(1<<len(word)),f'0{len(word)}b')
def strip(word,bit,count):
    while word and count:
        count-=word[-1]==bit;word=word[:-1]
    return word
def segment(program,word):
    counts=Counter();increments=[]
    for _ in range(1000):
        path,(op,r)=decode(program,word)
        if op in('CD','CH'):return word,path,(op,r),counts,increments
        if op=='CI':counts[r]+=1;increments.append(path);word=inc(path)
        elif op=='CB':word=inc(strip(path,'0',r))
        elif op=='CC':word=strip(path,'1',r)
        else:raise AssertionError(op)
    raise AssertionError('Segment fuel')
def context(path):
    ancestors=labels[path]
    if any(x.startswith('axioms()')for x in ancestors):return 'AX'
    if any(x.startswith('mp()')for x in ancestors):return 'MP'
    return 'OTHER'

index={};work=[];entries=[];mapped=defaultdict(set);inc_evidence=defaultdict(set);segments=0
def pair(a,b):
    global segments
    sa,sb=segment(source,a),segment(dag,b)
    assert sa[3]==sb[3]and sa[2]==sb[2]
    segments+=1
    # A bad increment is localized to a whole paired straight-line segment.
    # Require every counterpart increment to belong to the same named context.
    for path in sa[4]:
        if path in bad_paths:
            contexts={context(p)for p in sb[4]};assert len(contexts)==1
            inc_evidence[path].update(sb[4])
            mapped[path].update(contexts)
    if sa[1]in bad_paths:mapped[sa[1]].add(context(sb[1]))
    key=sa[0],sb[0]
    if key not in index:
        index[key]=len(entries);entries.append((sa,sb));work.append(index[key])
    return index[key]
pair('','');test_correspondence=defaultdict(set)
while work:
    sa,sb=entries[work.pop()];assert sa[2]==sb[2]
    if sa[2][0]=='CH':continue
    if sa[1]in bad_paths:test_correspondence[sa[1]].add(sb[1])
    pair(inc(sa[1]),inc(sb[1]));pair(inc(strip(sa[1],'0',1)),inc(strip(sb[1],'0',1)))
assert set(mapped)==bad_paths and all(len(v)==1 for v in mapped.values())
details=[]
for i in sorted(bad):
    path,op,r=sites[i];targets=sorted(test_correspondence[path]if op=='CD'else inc_evidence[path])
    details.append({'source_index':i,'routed_path':path,'opcode':op,'logical_register':r,
        'context':next(iter(mapped[path])),'dag_paths':targets,
        'dag_ancestor_labels':[labels[p]for p in targets],
        'mapping_scope':'matching register-test leaves'if op=='CD'else'paired straight-line increment segment'})
counts=dict(Counter(x['context']for x in details));assert counts=={'AX':49,'MP':1}
assert next(x for x in details if x['context']=='MP')['source_index']==6367
result={'status':'PASS_CLOSED_SEGMENT_BISIMULATION_CONTEXT_MAP','dag_source_sha256':hashlib.sha256(raw).hexdigest(),
    'routed_source_leaves':len(source),'annotated_dag_nodes':len(rows),'annotated_dag_unfolded_leaves':len(dag),
    'related_pointer_pairs':len(entries),'checked_straight_line_segments':segments,
    'bad_leaf_context_counts':counts,'failed_guard_context_counts':{'AX':97,'MP':2},
    'scope':'Source semantic localization through a closed segment relation. Annotation names come from Dag254.v comments. No reachability claim follows from this map alone.',
    'details':details}
(HERE/'scanner-semantic-contexts.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='details'},indent=2))
