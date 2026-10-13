"""Small shared-port dimension does not bound rejected source rays."""
from itertools import product
import sys

from .common import Block, source_hashes, verify_vector
from .test_filtered import compiled
from .filtered import FilteredAtlas
from .filtered_native import save


def main():
    output = dict(passed=False, source_sha256=source_hashes(), records=[],
        scope='abstract scalar-port orthant blocks, not native triangulations')
    for m in range(1, 8):
        co = compiled((Block(2, (), ((1, 1),)),)*m)
        p = FilteredAtlas(co)
        result = p.search((1,)*(2*m), lambda x:dict(accepted=False),
                          max_rejected=None, max_transitions=None)
        expected = {tuple(v for bit in bits for v in (1-bit, bit)) for bits in product((0,1), repeat=m)}
        actual = {tuple(a['coordinates']) for a in result['trace']}
        assert actual == expected and len(result['trace']) == 2**m
        for x in actual:
            assert verify_vector(co.source.n, co.source.equations, (), (1,)*(2*m), x, extreme=True)
        assert result['status']=='NO_ACCEPTED_EXTREME' and result['queries']==2**m+1
        capped = p.search((1,)*(2*m), lambda x:dict(accepted=False), max_rejected=4)
        assert capped['status'] == ('NO_ACCEPTED_EXTREME' if m<=2 else 'INCONCLUSIVE')
        output['records'].append(dict(blocks=m, result=result, capped=capped,
            prepared_stats=p.intrinsic.prepared.stats, intrinsic_dimension=p.intrinsic.reduction.dimension))
        save(sys.argv[1], output)
        print(m, result['queries'], result['transitions'], flush=True)
    output['passed'] = True
    save(sys.argv[1], output)


if __name__ == '__main__':
    main()
