#!/usr/bin/env python3
"""Experimental source compiler preserving observed non-decoder row uses.

Rows exercised after initial source decoding by unchanged guarded leaves are
kept, as are unchanged subtree entry rows and all Box support. New or changed
subtrees reuse their former entry only if its changed actions are free; else
a fresh entry is emitted. This is a cost heuristic, not a proof of compilation:
every output is independently subjected to the full strict affine checker.
"""
from functools import lru_cache
from collections import Counter
import json,hashlib,itertools
import rotation_search252 as r
import check_rotation252 as c
from fold_changed252 import read_table

DATA=json.loads((r.HERE/'mp-cache-decoder-entries.json').read_text())
NODES={int(k):tuple(map(tuple,v)) for k,v in DATA['nodes'].items()}
ROOT=DATA['root']
BASE=read_table(r.HERE/'rotation-candidates/mp-cache-permuted252.tm')
ENTRIES={int(k):max(v,key=v.get) for k,v in DATA['state_entries'].items()}

def fingerprints(nodes):
    @lru_cache(None)
    def fp(e):
        return ('N',tuple(fp(x) for x in nodes[e[1]])) if e[0]=='N' else e
    return fp

OLD_FP=fingerprints(NODES)
OLD_LOOKUP={OLD_FP(('N',n)):q for n,q in ENTRIES.items()}

def lookup(nodes,root,path):
    e=('N',root)
    for bit in path:
        if e[0]!='N':return None
        e=nodes[e[1]][int(bit)]
    return e if e[0]!='N' else None

def compile(nodes,root=ROOT):
    r.NEWPHYS=(4,5,0,8,6,2,1,7,3)
    fp=fingerprints(nodes)
    frozen={(str(q),b) for q,b in c.audit.BOX_PAIRS}
    class RuntimeUses(dict):
        def __init__(self,length):super().__init__(BASE);self.i=0;self.length=length;self.runtime=False
        def __getitem__(self,key):
            action=super().__getitem__(key)
            self.runtime|=self.i>=self.length-1 or action[0]!=key[1] or action[1]!='R'
            if self.runtime:frozen.add(key)
            self.i+=1
            return action
    kept=0
    for p,op,arg,z,branch,target in c.cases(NODES,ROOT):
        expected=(op[1:],) if op=='CH' else (op[1:],arg)
        if lookup(nodes,root,p)!=expected:continue
        rr,literal=c.strict.run(RuntimeUses(len(p)),p,branch,target,halt=op=='CH',fuel=1000)
        assert literal>0;kept+=1
    reached=set()
    def reach(e):
        if e[0]!='N' or e[1] in reached:return
        n=e[1];reached.add(n)
        if fp(e) in OLD_LOOKUP:
            q=OLD_LOOKUP[fp(e)];frozen.update((q,b) for b in (0,1))
        for x in nodes[n]:reach(x)
    reach(('N',root))
    table=BASE.copy();allocated=[];assigned={};node_entries={};nextstate=255
    @lru_cache(None)
    def emit(e):
        nonlocal nextstate
        assert e[0]=='N';n=e[1]
        if fp(e) in OLD_LOOKUP and n!=root:
            node_entries[n]=OLD_LOOKUP[fp(e)]
            return node_entries[n]
        oldq=ENTRIES.get(n)
        desired=[]
        for bit,child in enumerate(nodes[n]):
            oldchild=NODES.get(n,(None,None))[bit]
            if oldchild is not None and fp(child)==OLD_FP(oldchild):
                action=BASE[oldq,bit]
            elif child[0]=='N':action=(bit,'R',emit(child))
            elif child[0] in 'IDH':
                label=':'.join(map(str,child));q=max(DATA['leaf_entries'][label],key=DATA['leaf_entries'][label].get)
                action=(bit,'R',q)
            elif child[0]=='B' and child[1]==1:action=(0,'L','7' if bit==0 else '33')
            else:action=r.CONTROL_OPTIONS[child,bit].most_common(1)[0][0]
            desired.append(action)
        can_reuse=oldq is not None and all((oldq,b) not in frozen or BASE[oldq,b]==desired[b] for b in (0,1))
        can_reuse&=oldq not in assigned or assigned[oldq]==desired
        if n==root:
            assert oldq=='96'
            # The fixed dispatcher cannot be cloned. Its possible uses after
            # decoder return are checked by the final complete guard pass.
            can_reuse=True
        if can_reuse:q=oldq
        else:
            q=str(nextstate);nextstate+=1;allocated.append({'node':n,'new':q,'old':oldq})
        assigned[q]=desired
        node_entries[n]=q
        for b in (0,1):table[q,b]=desired[b]
        return q
    assert emit(('N',root))=='96'
    for n in reached:
        if n not in node_entries:node_entries[n]=OLD_LOOKUP[fp(('N',n))]
    return table,{'unchanged_guards_frozen':kept,'frozen_rows':len(frozen),'clones':allocated,'decoder_entries':{str(n):{node_entries[n]:1} for n in sorted(reached)}}

def main():
    nodes=NODES.copy();nodes[189]=(('N',188),('N',187));nodes[188]=(('D',5),('N',186));nodes[186]=(('N',168),('H',))
    table,meta=compile(nodes);result=c.run(table,nodes,ROOT)
    result.update(meta);result['graph_states']=len(r.gc(table))//2
    (r.HERE/'role-aware-special-nip-check.json').write_text(json.dumps(result,indent=2)+'\n')
    r.save(r.HERE/'rotation-candidates/role-aware-special-nip.tm',table)
    (r.HERE/'rotation-candidates/role-aware-special-nip.json').write_text(json.dumps({'nodes':nodes,'root':ROOT,'physical':r.NEWPHYS},indent=2)+'\n')
    print({k:v for k,v in result.items() if k not in ('used_rows','rule_counts','failures')},'failures',len(result['failures']),result['failures'][:3])

if __name__=='__main__':main()
