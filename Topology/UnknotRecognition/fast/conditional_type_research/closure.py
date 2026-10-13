"""Independent original STANDARD replay; no kernel or solver imports."""
from copy import deepcopy
from fractions import Fraction
from math import gcd
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_surface_geometry import _prepare
from .common import digest


def integer(x):
    assert type(x) is int
    return x


def pair(x,n):
    assert type(x) is list and len(x)==2
    assert 0<=integer(x[0])<n and 0<=integer(x[1])<3
    return tuple(x)


def mask(x,n):
    assert type(x) is list
    result=[pair(p,n) for p in x]
    assert result==sorted(result) and len(result)==len(set(result))
    return result


def local_forcing(prepared,conditional,proof,source_digest):
    """A source row combination vanishes on matching vectors; sign forces zero."""
    if proof is None:return set()
    assert type(proof) is dict and set(proof)=={'schema','source_sha256','allowed_types','steps'}
    # Raw legacy producer data is independently interpreted only by this scratch
    # general-mask algebra replay. Existing compatible-only native semantics stay intact.
    assert proof['schema']=='normal-sector-matching-support-v1'
    assert proof['source_sha256']==source_digest
    assert mask(proof['allowed_types'],len(prepared['tetrahedra']))==conditional
    assert type(proof['steps']) is list and proof['steps']
    forced=set();equations=prepared['matching']
    for step in proof['steps']:
        assert type(step) is dict and set(step)=={'row_combination','forced_indices'}
        terms=step['row_combination'];assert type(terms) is list and terms
        row={};previous=-1
        for term in terms:
            assert type(term) is list and len(term)==3
            index,num,den=map(integer,term)
            assert previous<index<len(equations) and num!=0 and den>0 and gcd(abs(num),den)==1
            previous=index;weight=Fraction(num,den)
            for column,value in equations[index].items():row[column]=row.get(column,0)+weight*value
        assert not any(value for column,value in row.items() if column%7<4)
        added=[]
        for i,(t,q) in enumerate(conditional):
            if i in forced:continue
            coefficient=row.get(7*t+4+q,0)
            assert coefficient>=0
            if coefficient>0:added.append(i)
        claimed=step['forced_indices']
        assert type(claimed) is list and all(type(i) is int for i in claimed) and claimed==added and added
        forced.update(added)
    return forced


def replay_record(record,old,cap):
    source=old['preprocessing']['u1']['result']['partial_chain']['triangulation']
    assert digest(record['source'])==digest(source) and record['source_sha256']==digest(source)
    assert record['id']==old['id'] and digest(record['input_pd'])==digest(old['input_pd'])
    assert verify_crushing_chain(Diagram.from_pd(old['input_pd']),old['preprocessing']['u1']['result']['partial_chain'])
    prepared=_prepare(source,lambda:None);n=len(source['tetrahedra'])
    allowed=[(t,q) for t in range(n) for q in range(3)]
    assert mask(record['initial_types'],n)==allowed
    assert 0<=integer(record['checks_used'])<=cap
    assert type(record['queries']) is list
    prep=record['preparation'];assert type(prep) is dict
    used=integer(prep['checks_used']);assert 0<=used<=record['checks_used']
    cursor=0;deleted=[];proofs=0;other_forced=[];capped=False
    if prep['status']=='CAPPED':
        assert used==cap and not record['queries'] and record['status']=='CAPPED'
        capped=True
    else:
        assert prep['status']=='RETURNED' and integer(prep['vertices'])==prepared['vertices']==1
    for index,query in enumerate(record['queries']):
        assert not capped and cursor<len(allowed)
        assert integer(query['index'])==index and mask(query['retained_before'],n)==allowed
        tested=pair(query['tested_type'],n);assert tested==allowed[cursor]
        conditional=[a for a in allowed if a[0]!=tested[0] or a==tested]
        assert mask(query['conditional_mask'],n)==conditional
        assert integer(query['start_checks'])==used
        used=integer(query['end_checks']);assert query['start_checks']<=used<=cap
        if 'kernel_statistics' in query:
            stats=query['kernel_statistics']
            assert type(stats) is dict and set(stats)=={'tetrahedra','allowed_types','active_equations',
                'triangle_classes','kernel_variables','kernel_equations','matching_nullity',
                'matching_rank','removed_link_factors'}
            assert all(type(value) is int and value>=0 for value in stats.values())
            assert stats['tetrahedra']==n and stats['allowed_types']==len(conditional)
            assert stats['kernel_variables']==stats['triangle_classes']+len(conditional)
            assert stats['matching_nullity']+stats['matching_rank']==len(conditional)
            assert stats['active_equations']<=4*len(conditional)
            assert stats['triangle_classes']<=8*len(conditional)
            assert stats['kernel_equations']<=stats['active_equations']
        if query['status']=='CAPPED':
            assert used==cap and index==len(record['queries'])-1
            assert 'removed_type' not in query and 'raw_matching_provenance' not in query
            capped=True;continue
        assert query['status']=='RETURNED' and 'kernel_statistics' in query
        forced=local_forcing(prepared,conditional,query['raw_matching_provenance'],digest(source))
        proofs+=query['raw_matching_provenance'] is not None
        keep=[i for i in range(len(conditional)) if i not in forced]
        assert type(query['retained_indices']) is list and all(type(i) is int for i in query['retained_indices'])
        assert query['retained_indices']==keep
        assert mask(query['conditional_forced_types'],n)==[conditional[i] for i in sorted(forced)]
        target=conditional.index(tested)
        if target in forced:
            assert pair(query['removed_type'],n)==tested
            # Compatibility implies a vector with q_tested>0 is in this
            # conditional mask. Local zero therefore licenses THIS deletion.
            allowed.remove(tested);deleted.append(tested);cursor=0
            others=[conditional[i] for i in forced if conditional[i]!=tested]
            if others:other_forced.append((index,others[0]))
        else:
            assert query['removed_type'] is None;cursor+=1
    assert record['checks_used']==used
    assert mask(record['retained_types'],n)==allowed
    assert [pair(a,n) for a in record['deletions']]==deleted
    if capped:assert record['status']=='CAPPED'
    else:assert record['status']=='SUFFICIENT_CLOSURE_FIXED_POINT' and cursor==len(allowed)
    return dict(id=record['id'],tetrahedra=n,queries=len(record['queries']),
        conditional_provenance_packets=proofs,deletions=len(deleted),remaining_types=len(allowed),
        status=record['status'],checks_used=used,accepted_deletions_verified=True,
        no_effect_scope='Sufficient-closure observation, not a proof that each surviving type is feasible.'),other_forced


