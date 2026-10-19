#!/usr/bin/env python3
"""Verify source rebasing using literal path walking, without dyadic indexing."""
from pathlib import Path
import json,time
import composed_rotations as D
E=D.E
HERE=Path(__file__).resolve().parent

def leaves(nodes,root):
    out=[]
    def visit(e,p):
        if e[0]=='N':
            a,b=nodes[e[1]];visit(a,p+'0');visit(b,p+'1')
        else:out.append((p,e))
    visit(('N',root),'');return out

def inc(word):
    if not word:return ''
    return format((int(word,2)+1)%(1<<len(word)),f'0{len(word)}b')

def strip(word,bit,k):
    pos=len(word)
    while k and pos:
        pos-=1
        if word[pos]==bit:k-=1
    return word[:pos]

def graph(nodes,root):
    ss=leaves(nodes,root);indices={p:i for i,(p,e) in enumerate(ss)}
    def normalize(word):
        e=('N',root);at=0;path=''
        while e[0]=='N':
            bit=word[at] if at<len(word) else '0'
            e=nodes[e[1]][int(bit)];path+=bit;at+=1
        return indices[path]
    out=[]
    for p,e in ss:
        if e[0]=='I':out.append((normalize(inc(p)),))
        elif e[0]=='D':out.append((normalize(inc(p)),normalize(inc(strip(p,'0',1)))))
        elif e[0]=='B':out.append((normalize(inc(strip(p,'0',e[1]))),))
        elif e[0]=='C':out.append((normalize(strip(p,'1',e[1])),))
        else:assert e==('H',);out.append(())
    return ss,out

def main():
    assert __debug__;start=time.monotonic();old,old_graph=graph(E.NODES,E.ROOT)
    data=json.loads((HERE/'source_rebase_examples.json').read_text());reports=[]
    for item in data['examples']:
        nodes={int(n):tuple(map(tuple,p)) for n,p in item['nodes'].items()}
        ss,edges=graph(nodes,item['root']);assert len(nodes)==203 and len(ss)==6460
        for i,((_,a),(_,b)) in enumerate(zip(old,ss)):
            assert a==b or (a[0] in 'BC' and b[0] in 'BC'),(item['recipe'],i,a,b)
        assert edges==old_graph,item['recipe']
        changed=sum(a!=b for (_,a),(_,b) in zip(old,ss))
        assert changed==item['changed_leaf_count']
        reports.append(dict(recipe=item['recipe'],source_nodes=len(nodes),source_leaves=len(ss),
                            checked_successor_edges=sum(map(len,edges)),changed_control_leaves=changed))
    out=dict(status='PASS_INDEPENDENT_LITERAL_PATH_WALK',examples=reports,
             total_checked_successor_edges=sum(r['checked_successor_edges'] for r in reports),
             elapsed=time.monotonic()-start,
             scope='Exact one-instruction source CFG bisimulation for arbitrary register vectors. No TM table or blank initializer is established by this check.')
    (HERE/'source-rebase-independent.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
