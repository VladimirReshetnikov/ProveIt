#!/usr/bin/env python3
"""Independent structural-map audit. Standard library; no producer imports.
Run: python structural.py SOURCE [--output RECEIPT]
Imports only the independent polynomial/catalog checker in this directory.
"""
from pathlib import Path
from itertools import combinations, permutations, product
from collections import Counter, defaultdict
from functools import lru_cache
import argparse
import hashlib
import json
import time
import check

R = Path(__file__).resolve().parent
DEPENDENCY_MANIFEST_SHA256 = '2ce3f5bc844f695633643c9de77a816a2d5603dba55f19c011f9deef07c273ce'
POSITIVE_SHA256 = 'a3c7a6eaebe02ef50998710282542be2751b218a6713853cdd2eecadbe1f1f86'
POSITIVE_MD5 = 'c73d80267112a960df5485f159ab56e0'
require = check.require


def mask(indices):
    return sum(1 << i for i in indices)


def bits(value):
    return tuple(i for i in range(value.bit_length()) if value >> i & 1)


def dual(bases, n):
    return frozenset(((1 << n)-1) ^ b for b in bases)


# Explicit exceptional nonbases from the approved primary-source check,
# COSW Examples 11.1--11.4 and 11.7. Labels below are one-based in print.
def line(values):
    return mask(i-1 for i in values)

FANO = frozenset(line(t) for t in [(1,2,3),(3,4,5),(1,5,6),(1,4,7),
                                  (2,5,7),(3,6,7),(2,4,6)])
EXCEPTIONS = {
    'F7': FANO,
    'F7-': FANO-{line((2,4,6))},
    'F7--': FANO-{line((2,4,6)),line((1,4,7))},
    'M(K4)+e': FANO-{line((2,4,6)),line((1,4,7)),line((3,4,5))},
    'F7-3': FANO-{line((2,4,6)),line((2,5,7)),line((3,6,7))},
}
ALL_TRIPLES_7 = frozenset(mask(s) for s in combinations(range(7),3))


def same_nonbase_system(left, right):
    """Exact isomorphism via degree-constrained bijections, never invariants only."""
    if len(left) != len(right):
        return False
    left_groups = defaultdict(list)
    right_groups = defaultdict(list)
    for i in range(7):
        left_groups[sum(bool(b >> i & 1) for b in left)].append(i)
        right_groups[sum(bool(b >> i & 1) for b in right)].append(i)
    if {d:len(v) for d,v in left_groups.items()} != {d:len(v) for d,v in right_groups.items()}:
        return False
    degrees = sorted(left_groups)
    for choices in product(*(permutations(right_groups[d]) for d in degrees)):
        permutation = [None]*7
        for d, targets in zip(degrees, choices):
            for source, target in zip(left_groups[d], targets):
                permutation[source] = target
        mapped = {mask(permutation[i] for i in bits(b)) for b in left}
        if mapped == right:
            return True
    return False


def drop_bit(value, index):
    return (value & ((1 << index)-1)) | ((value >> (index+1)) << index)


def minor_bases(bases, n, element, contract):
    containing = tuple(b for b in bases if b >> element & 1)
    avoiding = tuple(b for b in bases if not b >> element & 1)
    # Contract a loop / delete a coloop using the nonempty other branch.
    selected = (containing or avoiding) if contract else (avoiding or containing)
    return frozenset(drop_bit(b, element) for b in selected)


def rank_of(bases, subset):
    return max((b & subset).bit_count() for b in bases)


def paving(bases, n):
    rank = next(iter(bases)).bit_count()
    if rank == 0:
        return True
    return all(any(s & ~b == 0 for b in bases)
               for s in (mask(t) for t in combinations(range(n),rank-1)))


@lru_cache(None)
def classify_small(bases, n):
    require(bool(bases), 'Empty matroid basis system')
    ranks = {b.bit_count() for b in bases}
    require(len(ranks) == 1 and all(0 <= b < (1 << n) for b in bases), 'Invalid matroid bases')
    rank = next(iter(ranks))
    if n <= 6:
        return 'HPP_at_most_six'
    if n == 7:
        if rank not in (3,4):
            return 'HPP_seven_nonexceptional_rank'
        rank_three = dual(bases,n) if rank == 4 else bases
        nonbases = ALL_TRIPLES_7-rank_three
        for name, exceptional in EXCEPTIONS.items():
            if same_nonbase_system(nonbases,exceptional):
                return 'NON_HPP_'+name+('*' if rank == 4 else '')
        return 'HPP_seven_complete_exception_test'
    require(n == 8, 'Small classification only supports at most eight elements')
    minor_statuses = [classify_small(minor_bases(bases,n,e,c),7)
                      for e in range(n) for c in (False,True)]
    if any(s.startswith('NON_HPP') for s in minor_statuses):
        return 'NON_HPP_seven_element_minor'
    if rank != 4:
        return 'HPP_eight_all_minors_and_nonmiddle_rank'
    if not (paving(bases,n) and paving(dual(bases,n),n)):
        return 'HPP_eight_all_minors_and_not_sparse_paving'
    return 'UNKNOWN_eight_rank_four_sparse_paving'


def hall_basis(masks, selected):
    # Hall over ground-element subsets, independent of the producer's
    # injection-DP basis reconstruction.
    neighbors = tuple(masks[i] for i in selected)
    unions = [0]*(1 << len(neighbors))
    for subset in range(1,len(unions)):
        low = subset & -subset
        unions[subset] = unions[subset ^ low] | neighbors[low.bit_length()-1]
        if unions[subset].bit_count() < subset.bit_count():
            return False
    return True


def recount_bases(masks, rank):
    return frozenset(mask(selected) for selected in combinations(range(len(masks)),rank)
                     if hall_basis(masks,selected))


def transpose(rows):
    return tuple(mask(i for i in range(len(rows)) if rows[i] >> j & 1)
                 for j in range(len(rows)))


def index_set(value, n, name):
    require(isinstance(value,list) and all(type(x) is int and 0 <= x < n for x in value)
            and value == sorted(set(value)), 'Invalid '+name)
    return tuple(value)


def full_rows(core_rows):
    return tuple(row | (1 << 5) | (1 << 6) for row in core_rows)+(0,0)


def preorder(rows):
    reflexive = tuple(row | (1 << i) for i,row in enumerate(rows))
    return all(reflexive[j] & ~reflexive[i] == 0
               for i in range(len(rows)) for j in bits(reflexive[i]))


def load_dependencies():
    directory=R/'dependencies'
    manifest_raw=(directory/'source-pins.json').read_bytes()
    require(hashlib.sha256(manifest_raw).hexdigest() == DEPENDENCY_MANIFEST_SHA256,
            'Dependency manifest changed')
    pins=json.loads(manifest_raw)
    for filename,pin in pins.items():
        require(hashlib.sha256((directory/filename).read_bytes()).hexdigest() == pin['sha256'],
                'Dependency changed: '+filename)
    one=json.loads((directory/'one-tail-approval.json').read_text())
    require(one['verdict']=='approved' and one['source_theorem_sha256']==pins['one-tail-theorem.md']['sha256'],
            'One-tail approval linkage failed')
    role=json.loads((directory/'role-cover-approval.json').read_text())
    require(role['verdict']=='approved' and role['proof_sha256']==pins['role-cover-theorem.md']['sha256'],
            'Role-cover approval linkage failed')
    physical=json.loads((directory/'physical-cover-three-approval.json').read_text())
    require(physical['verdict']=='APPROVED' and physical['source_hashes']['three-core-internal-extension/PHYSICAL_COVER_THREE_ULC.md']==pins['physical-cover-three-theorem.md']['sha256'],
            'Physical-cover approval linkage failed')
    weighted=json.loads((directory/'preorder-degree-three-approval.json').read_text())
    require(weighted['verdict']=='approved' and weighted['source_theorem_sha256']==pins['preorder-degree-three-theorem.md']['sha256'],
            'Weighted-preorder approval linkage failed')
    raw=(directory/'n9r4Hpp.txt').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==POSITIVE_SHA256 and hashlib.md5(raw).hexdigest()==POSITIVE_MD5,
            'Published-positive file checksum mismatch')
    lines=raw.decode().splitlines()
    require(len(lines)==4125 and all(len(s)==126 and set(s)<=set('*0') for s in lines),
            'Invalid published-positive file')
    return pins,lines


def check_small_controls():
    tested=0
    for nonbases in EXCEPTIONS.values():
        bases=ALL_TRIPLES_7-nonbases
        for bb in (bases,dual(bases,7)):
            require(classify_small(bb,7).startswith('NON_HPP'), 'Seven-element exception falsely accepted')
            require(classify_small(bb,8).startswith('NON_HPP'), 'Loop extension falsely accepted')
            tested+=2
    uniform=frozenset(mask(s) for s in combinations(range(8),4))
    require(classify_small(uniform,8)=='UNKNOWN_eight_rank_four_sparse_paving',
            'Conservative eight-element boundary was lost')
    return {'exception_and_loop_extension_negative_controls':tested,
            'conservative_unknown_control':1}


def verify_structural(source, cores):
    started=time.time()
    pins,published=load_dependencies()
    controls=check_small_controls()
    path=Path(source)/'structural-9608.json'
    raw=path.read_bytes()
    proposals=json.loads(raw)['records']
    seen=set(); counts=Counter(); classifications=Counter(); details=[]
    colex=sorted(mask(s) for s in combinations(range(9),4))
    for proposal in proposals:
        ident=proposal['id']
        require(type(ident) is int and 0 <= ident < len(cores) and ident not in seen,
                f'Duplicate/invalid structural ID: {ident}')
        seen.add(ident)
        code,core_rows=cores[ident]
        require(proposal['core_code']==code and proposal['core_rows']==list(core_rows),
                f'Structural catalog mismatch: {ident}')
        rows=full_rows(core_rows)
        arcs=tuple((i,j) for i,row in enumerate(rows) for j in bits(row))
        method=proposal['method']; counts[method]+=1
        result={'id':ident,'method':method}
        if method=='two_tail_two_head':
            p=index_set(proposal['tail_cover'],7,'tail cover')
            q=index_set(proposal['head_cover'],7,'head cover')
            require(len(p)<=2 and len(q)<=2 and all(i in p or j in q for i,j in arcs),
                    f'Invalid two-tail/two-head cover: {ident}')
            result.update(tail_cover=list(p),head_cover=list(q))
        elif method=='physical_vertex_cover_three':
            cover=index_set(proposal['cover'],7,'physical cover')
            require(len(cover)<=3 and all(i in cover or j in cover for i,j in arcs),
                    f'Invalid physical cover: {ident}')
            result['cover']=list(cover)
        elif method=='one_tail_HPP_side':
            require(type(proposal['dual_relation']) is bool, 'Invalid reversal flag')
            working=transpose(rows) if proposal['dual_relation'] else rows
            require(proposal['working_rows']==list(working),f'Wrong reversal: {ident}')
            p=proposal['tail'];require(type(p) is int and 0<=p<7,'Invalid distinguished tail')
            q=index_set(proposal['heads'],7,'covered heads')
            require(q and all(i==p or j in q for i,row in enumerate(working) for j in bits(row)),
                    f'Invalid one-tail cover: {ident}')
            # Minimality is checked because the supplied maps claim this exact
            # presentation, though the abstract theorem does not need it.
            expected_q=sorted({j for i,row in enumerate(working) if i!=p for j in bits(row)})
            require(list(q)==expected_q,f'Wrong indicated covered-head set: {ident}')
            tails=tuple(mask(k for k,j in enumerate(q) if working[i] >> j & 1) for i in range(7))
            rank=len(q)
            simple=tuple(1 << j for j in range(rank))+tuple(n for n in tails if n.bit_count()>=2)
            require(proposal['tail_masks']==list(tails) and proposal['simple_masks']==list(simple)
                    and proposal['simple_rank']==rank,f'Wrong side presentation: {ident}')
            classes=tuple(tuple([7+j]+[i for i,n in enumerate(tails) if n==1<<j])
                          for j in range(rank))+tuple((i,) for i,n in enumerate(tails) if n.bit_count()>=2)
            require(len(classes)==len(simple), 'Parallel-class count mismatch')
            require(all(hall_basis(simple,pair) for pair in combinations(range(len(simple)),2)),
                    'Claimed simplification has a parallel pair')
            bases=recount_bases(simple,rank)
            require(proposal['bases']==sorted(bases) and mask(range(rank)) in bases,
                    f'Wrong complete side basis set: {ident}')
            classification=proposal['classification'];classifications[classification]+=1
            result.update(dual_relation=proposal['dual_relation'],tail=p,heads=list(q),
                          simple_rank=rank,simple_size=len(simple),basis_count=len(bases),
                          parallel_classes=[list(c) for c in classes],
                          loops=[i for i,n in enumerate(tails) if n==0],classification=classification)
            counts['side_basis_recounts']+=1
            if classification=='HPP_published_nine_positive':
                require(len(simple)==9 and rank in (4,5), f'Bad nine-element side: {ident}')
                require(type(proposal['dual_matroid']) is bool and proposal['dual_matroid']==(rank==5),
                        f'Wrong side-duality flag: {ident}')
                target=dual(bases,9) if rank==5 else bases
                published_line=proposal['published_line']
                require(type(published_line) is int and 1<=published_line<=len(published),'Invalid positive-list line')
                fingerprint=published[published_line-1]
                require(proposal['fingerprint']==fingerprint,f'Published fingerprint mismatch: {ident}')
                perm=proposal['side_to_published']
                require(isinstance(perm,list) and all(type(x) is int for x in perm) and sorted(perm)==list(range(9)),
                        f'Invalid explicit basis permutation: {ident}')
                listed={b for b,symbol in zip(colex,fingerprint) if symbol=='*'}
                for b in colex:
                    mapped=mask(perm[i] for i in bits(b))
                    require((b in target)==(mapped in listed),f'Nine-element basis bijection fails: {ident}')
                    counts['published_basis_indicator_comparisons']+=1
                result.update(published_line=published_line,side_to_published=perm,dual_matroid=rank==5)
            elif classification in ('HPP_eight_nonmiddle_rank','HPP_le7_rank'):
                n=len(simple)
                if classification=='HPP_eight_nonmiddle_rank':
                    require(n==8 and rank!=4,f'Wrong eight-element classification domain: {ident}')
                else:
                    require(n<=7 and (n<=6 or rank not in (3,4)),f'Wrong <=7 rank classification domain: {ident}')
                verdict=classify_small(bases,n)
                require(verdict.startswith('HPP'),f'Side classification failed: {ident}, {verdict}')
                result['independent_classification']=verdict
                if n==8:
                    ranks=tuple(rank_of(bases,s) for s in range(1<<n))
                    minor_results=[]
                    for e in range(n):
                        for contract in (False,True):
                            minor=minor_bases(bases,n,e,contract)
                            status=classify_small(minor,7)
                            require(status.startswith('HPP'),f'Unproved proper minor: {ident}, {e}, {contract}')
                            # Verify every computed minor rank by its independent
                            # defining deletion/contraction rank identity.
                            for s in range(1<<7):
                                lifted=(s&((1<<e)-1))|((s>>e)<<(e+1))
                                expected=ranks[lifted|(1<<e)]-ranks[1<<e] if contract else ranks[lifted]
                                require(rank_of(minor,s)==expected,'Minor rank identity failed')
                                counts['minor_rank_function_identities']+=1
                            minor_results.append({'element':e,'contract':contract,
                                                  'rank':next(iter(minor)).bit_count(),
                                                  'basis_count':len(minor),'classification':status})
                            counts['one_element_minor_checks']+=1
                    result['proper_minor_checks']=minor_results
            else:
                raise ValueError(f'Unsupported HPP classification: {classification}')
        else:
            raise ValueError(f'Unsupported structural method: {method}')
        details.append(result)
    require(path.read_bytes()==raw,'Structural source changed during audit')
    return seen,{
        'status':'PASS','record_count':len(seen),'method_counts':dict(counts),
        'classification_counts':dict(classifications),'controls':controls,
        'structural_source_sha256':hashlib.sha256(raw).hexdigest(),
        'dependency_manifest_sha256':DEPENDENCY_MANIFEST_SHA256,
        'dependency_files':{k:v['sha256'] for k,v in pins.items()},
        'published_positive_data_sha256':POSITIVE_SHA256,
        'all_recorded_covers_reversals_sides_and_bases_verified':True,
        'all_required_small_side_minors_verified':True,
        'all_nine_element_explicit_basis_bijections_verified':True,
        'source_records_unchanged':True,'producer_code_imported_or_executed':False,
        'seconds':round(time.time()-started,3),
    },details


def verify_preorders(source, cores):
    path=Path(source)/'preorder-coverage.json'
    if not path.exists():
        return set(),{'present':False},[]
    raw=path.read_bytes();proposals=json.loads(raw)['records']
    expected={i for i,(_,rows) in enumerate(cores) if preorder(rows)}
    seen=set();records=[]
    for record in proposals:
        ident=record['id']
        require(type(ident) is int and 0<=ident<len(cores) and ident not in seen,'Invalid preorder ID')
        code,rows=cores[ident]
        require(record['core_code']==code and record['rows']==list(rows),'Wrong preorder core')
        require(record['method']=='previous_weighted_preorder_degree_three_theorem','Wrong preorder method')
        require(preorder(rows) and preorder(full_rows(rows)),'Nontransitive proposed preorder/extension')
        seen.add(ident);records.append({'id':ident,'core_transitive_with_diagonal':True,
                                      'seven_vertex_extension_transitive_with_diagonal':True,
                                      'physical_degree_bound':3})
    require(seen==expected,'Preorder coverage does not match the full transitive catalog subset')
    require(path.read_bytes()==raw,'Preorder source changed during audit')
    return seen,{'present':True,'status':'PASS','record_count':len(seen),
                 'all_core_and_sink_extension_transitivity_checks_passed':True,
                 'actual_degree_at_most_three_by_seven_physical_vertices':True,
                 'source_sha256':hashlib.sha256(raw).hexdigest()},records


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path)
    parser.add_argument('--output',type=Path,default=R/'structural-receipt.json')
    args=parser.parse_args()
    cores,catalog_hash=check.read_catalog(args.source/'cores.txt')
    structural,receipt,records=verify_structural(args.source,cores)
    preorders,preorder_receipt,preorder_records=verify_preorders(args.source,cores)
    receipt.update(catalog_sha256=catalog_hash,coverage=check.check_coverage(cores),
                   preorder_branch=preorder_receipt,preorder_new_beyond_structural=len(preorders-structural),
                   combined_structural_preorder_count=len(structural|preorders),
                   checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    args.output.with_name(args.output.stem+'-records.json').write_text(
        json.dumps({'structural':records,'preorder':preorder_records},indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':
    main()
