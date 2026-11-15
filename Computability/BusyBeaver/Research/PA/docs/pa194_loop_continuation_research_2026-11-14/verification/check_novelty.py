#!/usr/bin/env python3
"""One-pass exact broad comparison of all five new tables and the pinned corpus."""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'comparison'))
from verify_novelty import canonical

def main():
    assert __debug__
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=ROOT/'verification/novelty.json')
    args=ap.parse_args()
    corpus=json.loads((ROOT/'comparison/full_census.json').read_text())
    references=[]
    for row in corpus['classes']:
        if row['states']==194:
            n,form=canonical(ROOT/'comparison/representatives'/(row['graph_hash']+'.tm'))
            assert n==194 and form is not None
            references.append((row['table_class'],form))
    assert len(references)==94 and len({f for _,f in references})==94
    results=[]
    forms=[]
    candidates=[(name,ROOT/'machines'/name/'machine.tm') for name in
                ['PA194LC','PA194LC_A','PA194LC_B','PA194LC_C']]
    candidates.append(('PA194GAX11',ROOT/'additional/PA194GAX11/machine.tm'))
    for name,path in candidates:
        n,form=canonical(path)
        assert n==194 and form is not None
        matches=[name for name,f in references if f==form]
        assert not matches and all(form!=f for f in forms)
        forms.append(form)
        results.append(dict(name=name,working_states=n,
            dense_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            canonical_sha256=hashlib.sha256(repr(form).encode()).hexdigest(),
            prior_matches=matches))
    result=dict(status='PASS', snapshot=corpus['summary']['snapshot'],
        prior_graphs=94, new_graphs=len(candidates), new_graphs_pairwise_distinct=True,
        compared='Full canonical tuples, not hash equality',
        transformations=['all state renamings','any spanning initial root',
            'global L/R reflection','global symbol exchange','terminal write/move ignored'],
        scope='Structural novelty; symbol exchange is not claimed to preserve a fixed zero blank.',
        results=results)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
