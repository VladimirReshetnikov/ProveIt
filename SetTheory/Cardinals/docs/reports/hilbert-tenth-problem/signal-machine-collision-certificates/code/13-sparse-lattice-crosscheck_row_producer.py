"""Cross-check producer residual coefficients against the independent compiler.
Usage: python crosscheck_producer.py /path/to/sparse_mass.py
"""
from collections import Counter,defaultdict
from itertools import product
from pathlib import Path
import argparse, hashlib, importlib.util, json, random, re, sys, tempfile
from independent_dynamics import conservative_permutation, dense_step, to_records
from independent_row_polynomial_audit import Compiler, strengthen_and_verify


def load_producer(path):
    spec=importlib.util.spec_from_file_location('audited_producer',path)
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    return module


def classify(name):
    if name.endswith('.b'):return 'compare_bit'
    if name.endswith('.d'):return 'compare_gap'
    if '.ch.' in name:return 'channel_selector'
    if '.stream.' in name:return 'stream_position'
    if '.mass.' in name:return 'input_mass'
    if re.search(r'\.g\.\d+\.[RCL]\.\d+$',name):return 'lookup_selector'
    if '.row.' in name:return 'row_selector'
    if '.pair.' in name:return 'pair_product'
    if '.triple.' in name:return 'triple_product'
    if '.out.' in name:return 'output_mass'
    if name.endswith(('.xmin','.xmax')):return 'sort_position'
    if name.endswith(('.zmin','.zmax')):return 'sort_channel'
    raise AssertionError(name)


def check_instance(mod,K,g,records,T,orthant,allowed_inputs=None):
    a=Compiler(K,g,records,T,allowed_inputs=allowed_inputs)
    if orthant:strengthen_and_verify(a)
    conf=defaultdict(lambda:[0,0,0])
    for x,c in records:conf[x][c]+=1
    b,meta=mod.compile_history(mod.LocalTable.from_mapping(K,g),dict(conf),T,orthant_exact=orthant,lookup_backend="rows",allowed_inputs=allowed_inputs)
    assert b.validate_witness()
    ai=defaultdict(list);bi=defaultdict(list)
    for j,name in enumerate(a.names):ai[name].append(j)
    for j,name in enumerate(b.names):bi[classify(name)].append(j)
    assert set(ai)==set(bi)
    mapping={}
    for kind in ai:
        assert len(ai[kind])==len(bi[kind]),kind
        mapping.update(zip(ai[kind],bi[kind]))
    assert all(a.values[j]==b.values[k] for j,k in mapping.items())
    def canon(d):return tuple(sorted((tuple(sorted(m)),c) for m,c in d.items() if c))
    A=Counter(canon({tuple(sorted(mapping[j] for j in mon)):c for mon,c in r.d.items()}) for r in a.residuals)
    B=Counter(tuple(p.terms) for p in b.residuals)
    assert A==B,{'only_independent':list((A-B).items())[:2],'only_producer':list((B-A).items())[:2]}
    assert b.decode(meta['physical_shift'])==[{x:tuple(v) for x,v in d.items()} for d in b.decode(meta['physical_shift'])]
    with tempfile.TemporaryDirectory() as temp:
        path=Path(temp)/'certificate.json'
        payload=b.export(path,meta)
        assert mod.verify_bound_export(path)['valid']
        if b.values:
            payload['witness_values'][0]+=1
            path.write_text(json.dumps(payload))
            assert not mod.verify_bound_export(path)['valid']
        # A changed polynomial must fail descriptor binding, even if made zero.
        payload=b.export(path,meta)
        if payload['residuals']:
            payload['residuals'][0]=[];path.write_text(json.dumps(payload))
            try:mod.verify_bound_export(path)
            except ValueError:pass
            else:raise AssertionError('altered residual passed descriptor binding')
    return len(b.values),len(b.residuals)


def loader_checks(mod):
    m=2;K=m+18
    g=mod.LocalTable.from_mapping(K,{abc:abc for abc in product(range(K+1),repeat=3)})
    cases=0
    for gamma,inc in [(0,None),(2,0),(4,None),(6,1),(7,None)]:
        coefficients=None
        for n0,n1 in [(0,0),(0,9),(8,0),(7,13)]:
            b,meta=mod.compile_morita_inputs(g,m,gamma,inc,n0,n1,0)
            assert b.validate_witness()
            M=m+19
            assert len(b.values)==len(b.residuals)==4+3*M*(M-1)
            assert max(b.values)<=meta['witness_height_bound']
            assert all(r.degree<=2 for r in b.residuals)
            current=[r.terms for r in b.residuals]
            if coefficients is None:coefficients=current
            else:assert coefficients==current,'loader polynomial changes with evaluated counter input'
            dense=defaultdict(lambda:[0,0,0])
            dense[0]=[10,m+6-gamma,gamma]
            for j,n in enumerate([n0,n1]):dense[n][2 if n==0 and inc==j else 1]+=2**j
            assert b.decode(0)==[{x:tuple(v) for x,v in sorted(dense.items())}]
            cases+=1
    return cases


def partial_checks(mod):
    K=2
    g={abc:abc for abc in product(range(K+1),repeat=3)}
    allowed=[(0,0,0),(1,0,0),(0,0,1)]
    count=0
    for T,orthant in product((1,2,3),(False,True)):
        check_instance(mod,K,g,[(0,2)],T,orthant,allowed_inputs=allowed)
        count+=1
    table=mod.LocalTable.from_mapping(K,g)
    try:mod.compile_history(table,{0:(0,1,0)},1,allowed_inputs=allowed)
    except ValueError:pass
    else:raise AssertionError('trajectory outside partial domain accepted')
    try:mod.compile_history(table,{0:(0,0,1)},1,allowed_inputs=[(1,0,0)])
    except ValueError:pass
    else:raise AssertionError('partial domain without vacuum accepted')
    return count


def loader_observer_checks(mod):
    # A diagnostic conservative permutation, not a Morita simulation claim.
    m=2;K=m+18;M=m+19
    mapping={abc:abc for abc in product(range(K+1),repeat=3)}
    mapping[(0,0,10)],mapping[(1,9,0)]=(1,9,0),(0,0,10)
    table=mod.LocalTable.from_mapping(K,mapping)
    lane_table={abc:mapping[abc[::-1]] for abc in mapping}
    cases=0;accepted=rejected=0
    for (gamma,inc),(n0,n1),T,orthant in product([(0,None),(2,0),(6,1)],[(0,0),(3,5)],(1,2),(False,True)):
        initial=defaultdict(lambda:[0,0,0]);initial[0]=[10,m+6-gamma,gamma]
        for j,n in enumerate([n0,n1]):initial[n][2 if n==0 and inc==j else 1]+=2**j
        dense={x:tuple(v) for x,v in initial.items()}
        physical=[dense];allowed={(0,0,0)}
        for t in range(T):
            dest=defaultdict(lambda:[0,0,0])
            for x,lanes in dense.items():
                for c,n in enumerate(lanes):dest[x+c-1][c]+=n
            allowed.update(tuple(lanes[::-1]) for lanes in dest.values())
            dense=dense_step(dense,lane_table);physical.append(dense)
        b,meta=mod.compile_morita_inputs(table,m,gamma,inc,n0,n1,T,first_pulse=True,orthant_exact=orthant,lookup_backend='rows',allowed_inputs=allowed)
        S=len(allowed);core_v=T*(M*(S+14)+5*M*(M-1));core_r=T*(17*M+5*M*(M-1)+2*M*int(orthant))
        load=4+3*M*(M-1)
        assert len(b.values)==core_v+load+4*M*T+3*M
        assert len(b.residuals)==core_r+load+4*M*T+2*M+T+M*int(orthant)
        assert b.decode(T)==physical
        assert max(b.values)<=meta['witness_height_bound']
        expected=sum((physical[t].get(-1,(0,0,0))[0]-int(t==T))**2 for t in range(1,T+1))
        assert b.score()==expected
        assert b.validate_witness()==(expected==0)
        if expected==0:accepted+=1
        else:rejected+=1
        cases+=1
    assert accepted>0 and rejected>0
    return {'cases':cases,'valid_first_pulse_instances':accepted,'earlier_pulse_instances_rejected':rejected}


def accounting_checks(mod):
    K=1;g={abc:abc for abc in product(range(2),repeat=3)}
    b,meta=mod.compile_history(mod.LocalTable.from_mapping(K,g),{0:(0,0,1)},1)
    checked=0
    with tempfile.TemporaryDirectory() as temp:
        path=Path(temp)/'certificate.json'
        original=b.export(path,meta)
        for field in original['counts']:
            payload=json.loads(json.dumps(original))
            value=payload['counts'][field]
            payload['counts'][field]=value+1 if isinstance(value,int) else value+' tampered'
            path.write_text(json.dumps(payload))
            try:mod.verify_bound_export(path)
            except ValueError:pass
            else:raise AssertionError(('altered accounting accepted',field))
            checked+=1
        payload=json.loads(json.dumps(original));payload['polynomial']='zero'
        path.write_text(json.dumps(payload))
        try:mod.verify_bound_export(path)
        except ValueError:pass
        else:raise AssertionError('altered polynomial declaration accepted')
        checked+=1
    return checked


def main():
    p=argparse.ArgumentParser();p.add_argument('producer');args=p.parse_args()
    source_hash=hashlib.sha256(Path(args.producer).read_bytes()).hexdigest()
    mod=load_producer(args.producer)
    cases=vars_=resids=0
    for K in (1,2,3):
        for seed in range(3):
            rng=random.Random(500*K+seed);g=conservative_permutation(K,rng)
            vals=[rng.randrange(K+1) for _ in range(9)]
            while sum(vals)>6:vals[rng.choice([j for j,v in enumerate(vals) if v])]-=1
            records=sorted((2*x,c) for x in range(3) for c in range(3) for _ in range(vals[3*x+c]))
            if not records:records=[(0,1)]
            low=min(x for x,c in records);records=[(x-low,c) for x,c in records]
            for T,orthant in product((0,1,2),(False,True)):
                v,r=check_instance(mod,K,g,records,T,orthant)
                cases+=1;vars_+=v;resids+=r
    loader_count=loader_checks(mod);partial_count=partial_checks(mod);accounting_count=accounting_checks(mod);observer_receipt=loader_observer_checks(mod)
    assert source_hash==hashlib.sha256(Path(args.producer).read_bytes()).hexdigest(),'producer changed during checks'
    print(json.dumps({'backend':'rows','producer_sha256':source_hash,'crosschecked_compilers':cases,'witnesses_compared_under_renaming':vars_,'residuals_compared_coefficientwise':resids,'exact_polynomial_multisets_match':True,'valid_exports_pass':True,'mutated_witnesses_fail':True,'altered_polynomials_fail_binding':True,'uniform_loader_cases':loader_count,'paid_loader_plus_observer':observer_receipt,'partial_row_coefficient_crosschecks':partial_count,'tampered_accounting_or_declaration_cases_rejected':accounting_count,'partial_domain_exit_rejected':True,'partial_domain_without_vacuum_rejected':True},indent=2))

if __name__=='__main__':main()
