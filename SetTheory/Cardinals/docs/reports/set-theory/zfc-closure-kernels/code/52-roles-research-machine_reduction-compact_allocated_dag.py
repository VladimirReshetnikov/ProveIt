"""Remove no-op leaves while checking/rebasing every finite control successor.

Physical increment/decrement operands are preserved. Break/continue parameters
are synthesized only when their exact decoded successor agrees after epsilon
closure of role-only transfer nodes. This is a finite source-CFG certificate.
"""
from pathlib import Path
from collections import Counter
import json,sys
import dynamic_renaming as d
ROOT=Path(__file__).parent
input_path=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/'allocated-dag.json'
data=json.loads(input_path.read_text());nodes={int(n):tuple(tuple(e) for e in p) for n,p in data['nodes'].items()}
root=tuple(data['root']);leaves={};branches={}
def expand(edge,path=''):
    if edge[0]!='N':leaves[path]=edge;return
    branches[path]=True
    for bit,e in enumerate(nodes[edge[1]]):expand(e,path+str(bit))
expand(root)
nops={p for p,e in leaves.items() if e==('B',0)}

def successor(p,e,zero=None):
    op,*arg=e;r=arg[0] if arg else None
    return d.p.successor(p,'C'+op,r,zero)

def decode(pc,tree_leaves):
    if pc is None:return None
    path=''
    for _ in range(200):
        if path in tree_leaves:return path
        path+=pc[len(path)] if len(path)<len(pc) else '0'
    raise AssertionError('no decode')

def epsilon(pc,tree_leaves,tagged_nops):
    seen=set()
    while (leaf:=decode(pc,tree_leaves)) in tagged_nops:
        assert leaf not in seen,('epsilon cycle',leaf)
        seen.add(leaf);pc=d.p.inc_path(leaf)
    return leaf

reference={}
for path,e in leaves.items():
    if path in nops:continue
    for zero in ((True,False) if e[0]=='D' else (None,)):
        reference[path,zero]=epsilon(successor(path,e,zero),leaves,nops)

def construct(remove):
    newleaves={};mapping={};cause={};collapsed=[]
    def tree(path=''):
        if path in leaves:return None if path in remove else ('leaf',path)
        a=tree(path+'0');b=tree(path+'1')
        if a is None and b is None:return None
        if a is None:collapsed.append((path,path+'0'));return ('unary',path+'0',b)
        if b is None:collapsed.append((path,path+'1'));return ('unary',path+'1',a)
        return ('node',a,b)
    def render(t,path='',lost=()):
        if t[0]=='unary':return render(t[2],path,lost+(t[1],))
        if t[0]=='leaf':
            old=t[1];newleaves[path]=leaves[old];mapping[old]=path;cause[old]=lost;return
        render(t[1],path+'0',lost);render(t[2],path+'1',lost)
    t=tree();assert t is not None;render(t)
    return newleaves,mapping,cause,collapsed

remove=set(nops);history=[]
while True:
    fresh,mapping,cause,collapsed=construct(remove)
    newnops={mapping[p] for p in nops if p in mapping};rebased={};bad=[]
    for old,e in leaves.items():
        if old in nops:continue
        new=mapping[old]
        wanted={z:None if reference[old,z] is None else mapping[reference[old,z]] for z in ((True,False) if e[0]=='D' else (None,))}
        if e[0] in 'BC':
            found=None
            options=[e]+[(op,k) for k in range(len(new)+1) for op in ('C','B')]
            for candidate in options:
                target=epsilon(successor(new,candidate),fresh,newnops)
                if target==wanted[None]:found=candidate;break
            if found is None:bad.append((old,reference[old,None],'control'))
            else:rebased[new]=found
        else:
            for z,target in wanted.items():
                got=epsilon(successor(new,e,z),fresh,newnops)
                if got!=target:bad.append((old,reference[old,z],(e,z)))
    history.append(dict(removed=len(remove),retained=len(nops)-len(remove),bad=len(bad)))
    print(history[-1],flush=True)
    if not bad:break
    restore=set()
    for source,target,_ in bad:
        for prefix in cause[source]+(cause.get(target,()) if target else ()):
            restore.update(p for p in remove if p.startswith(prefix))
    if not restore:
        restore=set(remove)
    assert restore and restore<=remove
    remove-=restore

fresh.update(rebased)
intern={};out={}
def intern_node(a,b):
    pair=a,b
    if pair not in intern:n=len(out);intern[pair]=n;out[n]=pair
    return 'N',intern[pair]
def collapse(path=''):
    if path in fresh:return fresh[path]
    return intern_node(collapse(path+'0'),collapse(path+'1'))
newroot=collapse()
result=dict(summary=dict(input_nodes=len(nodes),output_nodes=len(out),original_nops=len(nops),removed_nops=len(remove),retained_nops=len(nops)-len(remove),control_checks=len(reference),rebased=sum(fresh[mapping[p]]!=leaves[p] for p in mapping if p not in nops),history=history),root=newroot,nodes=out,original_to_new=mapping)
dest=input_path.with_name(input_path.stem+'-compacted.json');dest.write_text(json.dumps(result))
print(result['summary'],flush=True)
