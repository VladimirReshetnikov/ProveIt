"""Check cyclic signatures against literal covering-isomorphism orbits.

This uses the finite permutation graph oracle from audit.py.  Expected
equivalence classes are obtained by enumerating actual equivariant maps and
their actions on peripheral cycles; no gcd, CRT, or canonical-phase formula
is used in the expected answers.
"""

from itertools import product
import argparse
import json
from pathlib import Path
import time

from bootstrap import enable_fast
enable_fast()
from fastunknot.boundary_transport import BoundaryTransportIndex
from audit import example,literal_model,literal_maps,literal_orbit


def audit_canonical(max_sheets=9):
    start = time.perf_counter()
    result = {'presentations':0,'signature_queries':0,'marking_classes':0,
              'witness_checks':0,'max_sheets':max_sheets}
    for n in range(1,max_sheets+1):
        for a,b in product(range(n),repeat=2):
            raw = example(n,[(1,a),(1,b)])
            index = BoundaryTransportIndex(raw)
            generators,peripheral,components = literal_model(raw)
            orbits = [[literal_orbit(p,x) for x in range(n)] for p in peripheral]
            result['presentations'] += 1
            for has_point in (False,True):
                signature_to_literal,literal_to_signature = {},{}
                reported_count = None
                for source in components:
                    maps = literal_maps(generators,source,components[0])
                    circle0 = sorted({min(orbits[0][x]) for x in source})
                    circle1 = sorted({min(orbits[1][x]) for x in source})
                    point_choices = source if has_point else (None,)
                    for point,x,y in product(point_choices,circle0,circle1):
                        marks = [point] if has_point else []
                        answer = index.cyclic_marked_signature(source[-1],
                                  point_marks=marks,boundary_marks=[(0,x),(1,y)])
                        signature = answer['signature']
                        candidates = []
                        for mapping in maps:
                            candidate = ((mapping[point],) if has_point else ())
                            candidate += (min(orbits[0][mapping[x]]),min(orbits[1][mapping[y]]))
                            candidates.append(candidate)
                        literal = min(candidates)
                        if signature in signature_to_literal:
                            assert signature_to_literal[signature] == literal,(raw,answer,literal)
                        if literal in literal_to_signature:
                            assert literal_to_signature[literal] == signature,(raw,answer,literal)
                        signature_to_literal[signature] = literal
                        literal_to_signature[literal] = signature
                        if reported_count is not None:
                            assert reported_count == answer['marking_type_count']
                        reported_count = answer['marking_type_count']
                        root = answer['source_root']
                        anchor = answer['canonical_root_image']
                        witnesses = [mapping for mapping in maps if mapping[root] == anchor]
                        assert len(witnesses) == 1,(raw,answer)
                        mapping = witnesses[0]
                        for sheet in source:
                            assert index.transport_sheet(root,anchor,sheet) == mapping[sheet]
                            result['witness_checks'] += 1
                        result['signature_queries'] += 1
                assert len(signature_to_literal) == reported_count,(raw,has_point,reported_count)
                result['marking_classes'] += reported_count
    result['elapsed_seconds'] = time.perf_counter()-start
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-sheets',type=int,default=9)
    parser.add_argument('--output',default=str(Path(__file__).with_name('canonical-audit-results.json')))
    args = parser.parse_args()
    result = audit_canonical(args.max_sheets)
    text = json.dumps(result,indent=2,sort_keys=True)+'\n'
    Path(args.output).write_text(text)
    print(text,end='')
