#!/usr/bin/env python3
"""Check that all newly delivered tables are pairwise graph-distinct.

The four transformations are state/root canonicalization, optionally with
reflection, global bit exchange, or both. This is separate from correctness.
"""
from pathlib import Path
import argparse,itertools,json
from compare_candidate import parse,root_free,sha
HERE=Path(__file__).resolve().parent;PACKAGE=HERE.parent

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--machines',type=Path,default=PACKAGE/'machines')
    ap.add_argument('--families',nargs='+',default=['PA194R','PA194F','PA194A','PA194X'])
    ap.add_argument('--output',type=Path,default=HERE/'new_family_graphs.json')
    a=ap.parse_args();assert len(a.families)==len(set(a.families))
    signatures={};tables=[]
    for family in a.families:
        path=a.machines/family/'machine.tm';data=path.read_bytes();table=parse(data)
        assert len(table[1])==194
        ss={f'mirror={m},bitflip={f}':sha(root_free(table,m,f)) for m in (False,True) for f in (0,1)}
        signatures[family]=set(ss.values())
        tables.append({'family':family,'sha256':sha(data),'working_states':194,'graph_signatures':ss})
    pairs=[]
    for x,y in itertools.combinations(a.families,2):
        overlap=signatures[x]&signatures[y]
        assert not overlap,('Cosmetic equivalence',x,y,sorted(overlap))
        pairs.append({'first':x,'second':y,'distinct_even_with_reflection_and_global_bit_exchange':True})
    result={'status':'PASS','tables':tables,'pairs':pairs,
            'scope':'Pairwise graph distinction under arbitrary state renaming/root choice and the four listed cosmetic transformations. No semantic inequivalence is claimed.'}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','families':a.families,'checked_pairs':len(pairs)},indent=2))
if __name__=='__main__':
    if not __debug__:raise SystemExit('Assertions are required; do not use Python -O.')
    main()
