from pathlib import Path
from functools import cache
from collections import defaultdict,Counter
import sys,json,hashlib
HERE=Path(__file__).resolve().parent
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--inputs',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
sys.path.insert(0,str(HERE/'helpers'))
import seed_tools as b
s=b.s
base=args.inputs
source=s.tree(json.loads((base/'parent_sites.json').read_text()))
old=b.read_table((base/'parent.k.tm').read_bytes())
groups,paths=b.decoder_map(old,source)
q=lambda k:b.sole(groups,k)
@cache
def size(n):return 1 if s.leaf(n) else size(n[0])+size(n[1])
def flatten(n):return tuple((o,a) for p,o,a in s.sites(n))
pc,rel,eq,all_,imp,neg=(q(i) for i in [166,155,182,86,90,184])
all_imp=q(153);pair_inc=q(99);tail=q(193)
gate_copy=q(116)[1][1][1]
final_and=(neg,(imp,(neg,gate_copy)))
lower_block=((pc,(rel,all_imp)),(final_and,tail))
origins={}
def lower(n):
    if n==q(224):origins[lower_block]=n;return lower_block
    if s.leaf(n):return n
    r=tuple(map(lower,n))
    if r!=n:origins[r]=n
    return r
stage1=lower(source)
assert flatten(source)[648:732]==flatten((pair_inc,eq))
replacement=((pair_inc,(rel,eq)),all_)
def replace_interval(n,pos):
    end=pos+size(n)
    if 732<=pos or end<=648:return n
    if 648<=pos and end<=732:return replacement if pos==648 else None
    a=replace_interval(n[0],pos);d=replace_interval(n[1],pos+size(n[0]))
    if a is None:return d
    if d is None:return a
    r=(a,d)
    if r!=n:origins[r]=origins.get(n,n)
    return r
stage2=replace_interval(stage1,0)
rotation_path='1110100100111000'
on=s.subtree(stage2,rotation_path)
a,d=on[0];e=on[1]
assert all(s.boundary(v)==(0,0,False) for v in (a,d,e))
nn=(a,(d,e))
def rotate(n):
    if n==on:origins[nn]=origins.get(n,n);return nn
    if s.leaf(n):return n
    r=tuple(map(rotate,n))
    if r!=n:origins[r]=origins.get(n,n)
    return r
tree=rotate(stage2)
assert flatten(stage2)==flatten(tree)
assert s.graph_arithmetic(s.sites(tree))[0]==s.graph_intervals(s.sites(tree))==s.graph_arithmetic(s.sites(stage2))[0]
nodes=set()
def collect(n):
    if n in nodes or s.leaf(n):return
    nodes.add(n);collect(n[0]);collect(n[1])
collect(tree)
oldmap={n:k for k,vs in groups.items() for n in vs}
protected=set(k for k,bit in old)-set(groups)
for state,prs in paths.items():
    for p in prs:
        n=s.subtree(source,p)
        for bit,ch in enumerate(n):
            if s.leaf(ch):continue
            tape={i:int(v) for i,v in enumerate(p+str(bit))};tape[-1]=1
            head=len(p);k=state
            for tick in range(100):
                if head==len(p)+1:break
                if tick:protected.add(k)
                w,d,k=old[k,tape[head]];tape[head]=w;head+=d
intended={n:oldmap[n] for n in nodes if n in oldmap}
occupied=set(intended.values())
intended[tree]=84;occupied.add(84)
for n in nodes:
    origin=origins.get(n)
    if n not in intended and origin in oldmap and oldmap[origin] not in occupied and oldmap[origin] not in protected and len(groups[oldmap[origin]])==1:
        intended[n]=oldmap[origin];occupied.add(oldmap[origin])
free=sorted(set(groups)-occupied-protected,key=lambda k:(any(d!=1 or w!=bit for bit,(w,d,t) in enumerate((old[k,0],old[k,1]))),k))
fresh=300
def assign(n):
    global fresh
    if s.leaf(n):return
    if n not in intended:
        if free:intended[n]=free.pop(0)
        else:intended[n]=fresh;fresh+=1
    assign(n[0]);assign(n[1])
assign(tree)
table=dict(old)
def leaf_row(n,bit):
    op,arg=n
    if op=='CI' and arg==1:return bit,1,61
    if op=='CB' and arg==1 and bit==1:return 0,-1,40
    if op=='CH' and bit==1:return 1,1,254
    if op=='CD' and bit==0:return 0,1,{0:14,1:41,2:56,3:17,4:144,5:45,6:21,7:62,8:39}[arg]
    if op=='CI':return bit,1,{0:14,1:61,2:56,3:161,4:71,5:63,6:13,7:82,8:39}[arg]
    if op=='CC' and bit==1:return 0,-1,{1:1,2:16,3:42}[arg]
    raise ValueError(('unsupported',n,bit))
for n,k in intended.items():
    if n in oldmap:continue
    for bit,ch in enumerate(n):
        alternatives=groups.get(k,set())
        if len(alternatives)==1 and next(iter(alternatives))[bit]==ch:continue
        table[k,bit]=leaf_row(ch,bit) if s.leaf(ch) else (bit,1,intended[ch])
reach={0};todo=[0]
for k in todo:
    for bit in (0,1):
        nxt=table[k,bit][2]
        if nxt!=254 and nxt not in reach:reach.add(nxt);todo.append(nxt)
table={k:r for k,r in table.items() if k[0] in reach}
def check_decoder(tab,tr):
    actual=defaultdict(set);paths=defaultdict(list)
    def visit(n,p,k):
        if s.leaf(n):return
        actual[k].add(n);paths[k].append(p)
        for bit,ch in enumerate(n):
            if s.leaf(ch):continue
            tape={i:int(v) for i,v in enumerate(p+str(bit))};tape[-1]=1
            before=tape.copy();h=len(p);state=k;trace=[]
            for tick in range(100):
                if h==len(p)+1:break
                assert h in tape,(p,k,bit,'outside',trace)
                w,d,z=tab[state,tape[h]];trace.append((state,h,tape[h],w,d,z))
                tape[h]=w;h+=d;state=z
            assert tape==before and h==len(p)+1,(p,k,bit,'badframe',trace)
            assert state==intended[ch],(p,k,bit,'badtarget',state,intended[ch],trace)
            visit(ch,p+str(bit),state)
    visit(tr,'',84)
    return actual,paths
actual,pp=check_decoder(table,tree)
expected=defaultdict(set)
for n,k in intended.items():expected[k].add(n)
assert actual==expected
out=args.output;out.mkdir(parents=True,exist_ok=True)
(out/'sites.json').write_bytes(s.compact(s.sites(tree)))
(out/'candidate.k.tm').write_bytes(b.table_bytes(table))
print(json.dumps({'metrics':s.metrics(tree),'states':len(table)//2,'aliases':sum(len(v)-1 for v in actual.values()),'fresh':fresh-300,'removed':sorted(set(k for k,bit in old)-reach),'sha':hashlib.sha256(b.table_bytes(table)).hexdigest()},indent=2))
