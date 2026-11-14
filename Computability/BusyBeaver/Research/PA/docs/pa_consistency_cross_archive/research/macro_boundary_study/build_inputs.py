"""Reconstruct the exact source tree and its finite positivity overapproximation."""
import hashlib,json,re,sys
from collections import deque
from pathlib import Path
HERE=Path(__file__).parent
sys.path.insert(0,str(HERE/'tooling'))
import source_language as s
raw=(HERE/'upstream/data/pa196.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
program_raw=(HERE/'upstream/PA196/Program.lean').read_bytes()
assert hashlib.sha256(program_raw).hexdigest()=='8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872'
text=program_raw.decode()
nodes={}
for name,body in re.findall(r'def (\w+) : Tree := (.+)',text):
    if body.startswith('.node'):
        toks=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',body)
        children=[]
        for op,arg,ref in toks:
            if ref:children.append(nodes[ref])
            else:children.append(({'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}[op],int(arg) if arg else None))
        assert len(children)==2,(name,body,toks)
        nodes[name]=tuple(children)
    else:nodes[name]=nodes[body]
rows=s.sites(nodes['trie']);assert len(rows)==3812
graph,_=s.graph_arithmetic(rows);assert graph==s.graph_intervals(rows)
(HERE/'sites.json').write_text(json.dumps(rows))
def successors(state):
    pc,mask=divmod(state,512);effect,targets=graph[pc]
    if effect[0]=='halt':return []
    if effect[0]=='identity':return [targets[0]*512+mask]
    bit=1<<effect[1]
    if effect[0]=='increment':return [targets[0]*512+(mask|bit)]
    if mask&bit:return [targets[1]*512+(mask&~bit),targets[1]*512+mask]
    return [targets[0]*512+mask]
seen=bytearray(512*len(rows));seed=25*512+1;seen[seed]=1;work=deque([seed]);count=0
while work:
    state=work.popleft();count+=1
    for t in successors(state):
        if not seen[t]:seen[t]=1;work.append(t)
assert seen[seed] and all(all(seen[t] for t in successors(st)) for st,a in enumerate(seen) if a)
masks=[[m for m in range(512) if seen[pc*512+m]] for pc in range(len(rows))]
assert count==274880 and [i for i,m in enumerate(masks) if not m]==[3774,3775]
(HERE/'masks.json').write_text(json.dumps(masks))
print(json.dumps({'source_sites':len(rows),'joint_site_mask_pairs':count,'unreachable_sites':[3774,3775],
 'source_resolvers_agree':True,'fixed_point_closure_audited':True,'input_tm_sha256':hashlib.sha256(raw).hexdigest()},indent=2))
