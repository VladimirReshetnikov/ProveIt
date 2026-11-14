#!/usr/bin/env python3
"""Candidate: MP success leaves stack unchanged rather than pushing zero."""
from grammar_search import *
sys.path.insert(0,str(OUT.parent/'incoming208'))
import compile_ax as ca

def main():
    ns=parse_program();old=ns['trie']
    assert ns['node163']==(ns['node6'],ns['node55'])
    def subst_tree(t,a,b):
        if t==a:return b
        return t if isleaf(t) else (subst_tree(t[0],a,b),subst_tree(t[1],a,b))
    new=subst_tree(old,ns['node163'],(ns['node6'],ns['node54']))
    print('source leaf count',size(old),size(new),flush=True)
    oc=resolve(old);nc=resolve(new)
    def target(x):
        if x is None:return None
        if x==3773:return 3773
        if 3773<x<3792:raise ValueError(x)
        return x-(19 if x>=3792 else 0)
    def instr(v):
        k,*xs=v
        if k=='inc':return(k,xs[0],target(xs[1]))
        if k=='dec':return(k,xs[0],target(xs[1]),target(xs[2]))
        if k=='jump':return(k,target(xs[0]))
        return v
    expected=[instr(v) for i,v in enumerate(oc) if not 3773<=i<3792]
    dif=[(i,a,b) for i,(a,b) in enumerate(zip(expected,nc)) if a!=b]
    print('CFG differences after deleting push',dif[:40],'total',len(dif),flush=True)
    assert not dif
    T=ca.native();assert T[164,1]==(1,'R',98)
    T[164,1]=(1,'R',114)
    out={'description':'MP success omits zero push; table decoder change native164/1->114',
         'tree':new,'table':[[q,b,*a] for(q,b),a in sorted(T.items())],
         'source_removed':[3773,3791],'source_states':len(nc),
         'original_source_states':len(oc),'cfg_difference_count':len(dif)}
    (OUT/'mp_no_zero_candidate.json').write_text(json.dumps(out))
    (OUT/'mp_no_zero_native.tm').write_text(''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t) in sorted(T.items())))
    print('native table',len(ca.states(T)),'states; saved',flush=True)

if __name__=='__main__':main()
