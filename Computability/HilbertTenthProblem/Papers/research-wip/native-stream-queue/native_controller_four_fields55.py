"""Complete55/57 native four-field relation, using proved implicit parity."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sympy as sp
import native_controller_four_fields56 as prior

selector=prior.selector


def source_check(repunit=False):
    parameters=['q','F0','F1','F2','F3']
    auxiliaries=selector.CORE_NAMES+[f'alpha{i}' for i in range(4)]+(['Hrep'] if repunit else [])
    z={n:sp.Symbol(n) for n in parameters+auxiliaries}
    outer=[row for row in prior.OUTER if row[0]!='even_r']
    assert len(outer)==12
    schedule=outer+(prior.EXPOSE_H if repunit else [])+selector.CORE
    env=selector.execute(schedule,z)
    equalities=[(f'bound{i}','q') for i in range(4)]+[('r','packed')]
    if repunit:equalities += [('q','q_calc')]
    equalities+=selector.kernel.EQUALITIES[1:]
    source_with_parity=prior.independent_sources(dict(z,nu=sp.Symbol('unused_nu')),repunit)
    assert source_with_parity[5]==z['r']-2*sp.Symbol('unused_nu')
    sources=source_with_parity[:5]+source_with_parity[6:]
    u=2*z['r']+1+z['j']*z['c'];norm_index=len(sources)-3
    correction=sources[norm_index]*(u*u-z['y_aux']**2);records=[]
    for ix,((left,right),source) in enumerate(zip(equalities,sources)):
        adjust=correction if ix==norm_index+1 else 0
        assert sp.expand(env[left]-env[right]-source-adjust)==0,(repunit,ix)
        records.append(dict(equality=[left,right],source=str(sp.expand(source)),correction=str(sp.expand(adjust))))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==55+2*repunit and counts['*']==30 and counts['+']+counts['-']==25+2*repunit
    assert len(equalities)==len(sources)==15+repunit and len(auxiliaries)==21+repunit
    assert set().union(*(p.free_symbols for p in sources))==set(z.values())
    return dict(operations=len(schedule),multiplications=30,additions_subtractions=25+2*repunit,equations=len(sources),
                positive_parameters=parameters,positive_auxiliaries=auxiliaries,
                instructions=[list(row) for row in schedule],sources=records)


def verify():
    preliminary=prior.prepower()
    preliminary['scope']='Pre-power inequalities are independent of parity and include oddr'
    fields=prior.exhaustive_fields()
    for row in fields:
        row['native_words_excluded_by_index_parity']=row.pop('native_words_rejected_by_explicit_parity')
    return dict(status='PASS_COMPLETE_INDEPENDENT_NATIVE_FIELDS_55_57',
                sources={'55':source_check(),'57':source_check(True)},
                prepower=preliminary,field_scan=fields,canonical=prior.canonical_fields(),
                exact_projection='Identical to frozen56/58: signed parity forces evenr, so nu=r/2 extends every solution',
                parity_reference='EXPLORATION_FIXED_MINUS_INDEX_PARITY.md Section4, plus branch',
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
                scope='Complete native typing component; no universal controller, input bridge or acceptance',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k!='sources'},indent=2))
