#!/usr/bin/env python3
"""Independent data/coverage audit. Imports no generator or proof producer.
The Lean theorem, not this script, proves universal tape correctness.
"""
from pathlib import Path
import argparse, collections, hashlib, json, re
p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=Path('verification/context-audit.json'));a=p.parse_args()
root=Path(__file__).resolve().parent;text=(root/'K215Decoder.lean').read_text()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def section(name):
    return re.search(r'^def '+name+r' : [^\n]+ := #\[\n(.*?)\n\]',text,re.M|re.S).group(1)
def bools(s): return [x=='true'for x in re.findall(r'true|false',s)]
nodes=[]
for line in section('sourceNodes').splitlines():
    m=re.fullmatch(r'  \.(leaf|fork) (\d+) (\d+),?',line);assert m,line
    nodes.append((m[1],int(m[2]),int(m[3])))
blocks=[]
for line in section('blocks').splitlines():
    m=re.fullmatch(r'  ⟨(\d+), (\d+), \[([^\]]*)\], (\d+)⟩,?',line);assert m,line
    blocks.append((int(m[1]),int(m[2]),bools(m[3]),int(m[4])))
def edge(s):
    if s.startswith('.internal '):
        x,y=map(int,s.removeprefix('.internal ').split());return('internal',x,y)
    m=re.fullmatch(r'\.primitive (\d+) ⟨(true|false), (\(-1\)|1), (\d+)⟩',s);assert m,s
    return('primitive',int(m[1]),(m[2]=='true',-1 if m[3]=='(-1)'else 1,int(m[4])))
roles=[]
for line in section('roles').splitlines():
    m=re.fullmatch(r'  ⟨(\d+), (\d+), \[([^\]]*)\], \((.+)\), \((.+)\)⟩,?',line);assert m,line
    roles.append((int(m[1]),int(m[2]),bools(m[3]),[edge(m[4]),edge(m[5])]))
assert len(nodes)==202 and len(blocks)==281 and len(roles)==234
assert roles[0][:3]==(201,84,[True])

def before(w):return{i-len(w):b for i,b in enumerate(w)}
def cells(w):return{i-len(w)+1:b for i,b in enumerate(w)}
def covered(known,want):return all(known.get(i) is b for i,b in want.items())
def check_edge(r,bit,rs=roles):
    typ,k,j=r[3][bit]
    if typ=='primitive':return True
    if k>=len(rs)or j>=len(blocks):return False
    s=rs[k];e,x,w,n=blocks[j]
    known={**before(r[2]),0:bool(bit)}
    return e==r[1]and x==s[1]and covered(known,cells(w))and covered(known,{i+1:b for i,b in before(s[2]).items()})
internal=primitive=0
for r in roles:
    assert nodes[r[0]][0]=='fork'
    for bit,e in enumerate(r[3]):
        assert check_edge(r,bit)
        child=nodes[r[0]][bit+1]
        if e[0]=='internal':
            internal+=1;assert nodes[child][0]=='fork'and roles[e[1]][0]==child
        else:
            primitive+=1;assert nodes[child][0]=='leaf'and e[1]==child
assert(internal,primitive)==(371,97)
controls={}
for key,suffix in [('missing_predecessor',[]),('wrong_predecessor',[False])]:
    r=list(roles[0]);r[2]=suffix;controls[key]=not check_edge(r,0)
rs=list(roles);r=list(rs[1]);r[2]=[False,False];rs[1]=r
controls['wrong_next_suffix']=not check_edge(roles[0],0,rs)
controls['missing_target_role']=not check_edge(roles[0],0,[])
assert all(controls.values())

# Bind the concrete Lean data to the inherited JSON independently.
product=json.loads((root/'inputs/decoder_context_certificate.json').read_text())
ops=['CI','CD','CB','CC','CH']
converted=[[ops[x],None if x==4 else y]if k=='leaf'else[x,y]for k,x,y in nodes]
assert converted==product['nodes']
for r,jr in zip(roles,product['roles'],strict=True):
    assert (r[0],r[1],''.join('1'if b else'0'for b in r[2]))==(jr['node'],jr['state'],jr['suffix'])
    for e,je in zip(r[3],jr['edges'],strict=True):
        assert e[0]==je['kind']
        if e[0]=='internal':assert e[1]==je['role']and blocks[e[2]][3]==je['steps']
        else:assert e[1]==je['node']and list(map(int,e[2]))==je['action']

# Traverse every occurrence, rather than treating a DAG node as an occurrence.
leaves={};contexts={};used=set();durations={}
def walk(n,k,path,duration):
    r=roles[k];assert r[0]==n
    assert r[2]==[b=='1'for b in('1'+path)[-2:]]
    contexts[path]=k;durations[path]=duration;used.add(k)
    for bit,e in enumerate(r[3]):
        child=nodes[n][bit+1];p=path+str(bit)
        if nodes[child][0]=='leaf':
            assert e[0]=='primitive';leaves[p]=converted[child]
        else:
            assert e[0]=='internal';walk(child,e[1],p,duration+blocks[e[2]][3])
walk(201,0,'',0)
actual={r[0]:r[1:]for r in json.loads((root/'inputs/sites215.json').read_text())}
assert leaves==actual and len(leaves)==4751 and len(contexts)==4750 and len(used)==234
result={'status':'PASS_FINITE_INDEPENDENT_AUDIT','scope':'Binds inherited Lean product data and source-site expansion, checks all semantic context inclusions and malformed controls. Universal tape theorem is supplied separately by Lean. No primitive runtime or ZFC endpoint rebuild.',
'inputs':{p.name:sha(p)for p in[root/'K215Decoder.lean',root/'inputs/decoder_context_certificate.json',root/'inputs/sites215.json']},
'new_sources':{p.name:sha(p)for p in[root/'DecoderContext.lean',root/'K215Context.lean',root/'Audit.lean']},
'counts':{'source_nodes':len(nodes),'roles':len(roles),'blocks':len(blocks),'role_edges':internal+primitive,'internal_role_edges':internal,'context_inclusions':2*internal,'primitive_role_edges':primitive,'internal_source_occurrences':len(contexts),'internal_occurrence_edges':len(contexts)-1,'primitive_occurrences':len(leaves),'max_internal_path_bits':max(map(len,contexts)),'max_internal_path_steps':max(durations.values())},'malformed_controls_rejected':controls}
a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
