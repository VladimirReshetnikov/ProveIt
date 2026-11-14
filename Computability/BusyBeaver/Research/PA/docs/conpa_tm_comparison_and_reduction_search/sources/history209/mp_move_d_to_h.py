#!/usr/bin/env python3
"""MP success variant: destructively move D to H and retain the stack."""
from grammar_search import *
sys.path.insert(0,str(OUT.parent/'incoming208'))
import compile_ax as ca

def subst_tree(t,a,b):
    if t==a:return b
    return t if isleaf(t) else (subst_tree(t[0],a,b),subst_tree(t[1],a,b))

def main():
    ns=parse_program();old=ns['trie']
    new=subst_tree(old,ns['node163'],(ns['node6'],ns['node147']))
    flat=flatten(new);nc=resolve(new)
    T=ca.native();assert T[164,1]==(1,'R',98)
    T[164,1]=(1,'R',130)
    out={'description':'MP success=(0,w,0,D); native164/1->130',
         'tree':new,'table':[[q,b,*a] for(q,b),a in sorted(T.items())],
         'source_states':len(nc),'original_source_states':3812,
         'replacement_old_sites':[3773,3798],
         'new_sites':[3773,3775]}
    (OUT/'mp_move_h_candidate.json').write_text(json.dumps(out))
    (OUT/'mp_move_h_native.tm').write_text(''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t) in sorted(T.items())))
    print('newsites',len(nc),'entryrows',nc[3770:3785],flush=True)

if __name__=='__main__':main()
