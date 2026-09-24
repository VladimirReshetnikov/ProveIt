#!/usr/bin/env python3
"""Complete82 integration: fixed helical semantics plus fixed-base bridge."""
from pathlib import Path
import hashlib
import json
import sys
import sympy as sp

import explore_fixed_base_exponent_bridge as arithmetic
import explore_helical_unary_tableau as tableau

OUT = Path(__file__).with_suffix('.json')
ROOT = Path(__file__).resolve().parents[2]
NAMES = arithmetic.NAMES
CONSTANTS = arithmetic.CONSTANTS
SCHEDULE = arithmetic.SCHEDULE
EQUALITIES = arithmetic.EQUALITIES
source_residuals = arithmetic.source_residuals


def verify():
    source = arithmetic.verify_source()
    assert (source['operations'],source['multiplications'],source['additions_subtractions']) == (82,44,38)
    assert source['positive_existential_unknown_count'] == 33 and source['equations'] == 21
    source.pop('external_unpriced_interface')
    source['complete_raw_input_universal_certificate'] = True
    env = arithmetic.fixed_environment(arithmetic.SYM)
    aliases = {name:value for name,value in env.items() if name not in arithmetic.SYM}
    fixed = {arithmetic.SYM[name] for name in CONSTANTS}
    assert all(sp.sympify(value).free_symbols <= fixed for value in aliases.values())
    source['fixed_aliases'] = {name:sp.sstr(value) for name,value in aliases.items()}
    semantic = tableau.verify()
    assert semantic['noncanonical_N_not_divisible_by_h'] > 0
    composition = arithmetic.verify_helical_compositions()
    assert composition['cases'] > 0 and composition['positive_aliases_without_raw_bound'] > 0
    paths = ['Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md',
             'Papers/verification/explore_helical_unary_tableau.py',
             'Papers/verification/explore_helical_unary_tableau.json',
             'Papers/1980/EXPLORATION_FIXED_BASE_EXPONENT_BRIDGE.md',
             'Papers/verification/explore_fixed_base_exponent_bridge.py',
             'Papers/verification/explore_fixed_base_exponent_bridge.json']
    return dict(status='PASS_FIXED_RAW_UNIVERSAL82',source=source,
                helical_tableau=semantic,base_two_congruences=arithmetic.verify_congruences(),
                helical_compositions=composition,
                component_sha256={path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in paths},
                proof='../1980/FIXED_RAW_UNIVERSAL_82_PROOF.md',
                complete_fixed_index_raw_input_universal_certificate=True,
                proof_assistant_verified=False,full_packed_kernel_tuples_materialized=False,
                scope='Complete positive fixed-index raw-input82 theorem; full source checks, fixed helical semantics and positive arithmetic interfaces')


if __name__ == '__main__':
    result = verify()
    if sys.argv[1:] == ['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result == json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',
          result['helical_tableau']['local_triples_checked'],'helical triples;',
          result['helical_compositions']['cases'],'arithmetic interfaces')
