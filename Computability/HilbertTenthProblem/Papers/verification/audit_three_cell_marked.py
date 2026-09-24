#!/usr/bin/env python3
"""Independent scalar audit of all binary ternary relations for marked67."""
from itertools import product
from pathlib import Path
import hashlib
import json
import sys

import explore_three_cell_marked as candidate

ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).with_suffix('.json')


def verify():
    paths=[ROOT/'Papers'/'1980'/'EXPLORATION_THREE_CELL_MARKED_67.md',
           Path(candidate.__file__),candidate.OUT]
    hashes=lambda:{path.relative_to(ROOT).as_posix():hashlib.sha256(path.read_bytes()).hexdigest()
                   for path in paths}
    before=hashes()
    triples=tuple(product((0,1),repeat=3));bitrows=tuple(product((0,1),repeat=2))
    cases=accepted=0
    for table in range(256):
        allowed=frozenset(row for i,row in enumerate(triples) if table>>i&1)
        cc=candidate.compile_rule(2,allowed)
        for rows in product(bitrows,repeat=3):
            occupancy=tuple(sum(row) for row in rows)
            expected=(occupancy==(0,0,0) or
                      (occupancy==(1,1,1) and tuple(row.index(1) for row in rows) in allowed))
            for fill in (0,1):
                encoded=[2*sum(bit*cc.R**j for j,bit in enumerate(row+(fill,)*(cc.m-2))) for row in rows]
                field=sum(coef*value for coef,value in zip(cc.Ds,encoded))
                assert (field&cc.MF==0)==expected,(table,rows,fill)
                assert 0<=field<=cc.B-2
                cases+=1;accepted+=expected
    after=hashes();assert before==after and cases==32768
    return dict(status='PASS_INDEPENDENT_THREE_CELL67',all_binary_ternary_relations=256,
                scalar_and_dummy_cases=cases,accepted=accepted,unchanged_sha256=after,
                scope='Independent direct one-hot truth evaluation using compiled coefficients; full source and positive cyclic proof reviewed separately')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['all_binary_ternary_relations'],'relations;',result['scalar_and_dummy_cases'],'cases')
