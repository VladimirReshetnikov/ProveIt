"""Audit geometric chain compatibility and short-row nullity invariance.

Run with --output JSON. Optional --subdivision-source JSON reuses subdivision
fixtures saved by forest_audit.py; otherwise the same 1-4 sources are generated.
All normal-cut source geometries are independently authenticated. Occurrence
parities come from UNCAPPPED cycle flags, never from the capped raw scheduler.
Every distinct sampled dual tree is replayed by the source top-handle verifier.
"""

import argparse
from collections import Counter, deque
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import random
import sys
import time


FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from fastunknot.core_handlebody import _forest
from fastunknot.core_top_reduction import source_core_top_incidence
from fastunknot.core_top_reduction_verify import replay_core_top_reduction
from fastunknot.integer_codec import json_safe
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity


class DisjointSets:
    def __init__(self, size):
        self.parent = list(range(size))

    def root(self, v):
        while self.parent[v] != v:
            self.parent[v] = self.parent[self.parent[v]]
            v = self.parent[v]
        return v

    def join(self, a, b):
        a, b = self.root(a), self.root(b)
        if a == b:
            return False
        self.parent[max(a, b)] = min(a, b)
        return True


def digest(value):
    return hashlib.sha256(json.dumps(json_safe(value), sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


def binary_rank(rows):
    """Bit-vector elimination over F2, using highest set-bit pivots."""
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length()-1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def dense_binary_rank(rows, columns):
    """Independent low-column elimination on explicit zero/one arrays."""
    matrix = [[int(bool(row & (1 << c))) for c in range(columns)] for row in rows]
    rank = 0
    for column in range(columns):
        pivot = next((r for r in range(rank, len(matrix)) if matrix[r][column]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        for r in range(rank+1, len(matrix)):
            if matrix[r][column]:
                matrix[r] = [(a+b) % 2 for a, b in zip(matrix[r], matrix[rank])]
        rank += 1
    return rank


def chain_product(a_rows, b_rows, three_count):
    """Columns of A-transpose B, encoded as bit vectors on one-handles."""
    products = [0]*three_count
    for a, b in zip(a_rows, b_rows):
        while b:
            bit = b & -b
            products[bit.bit_length()-1] ^= a
            b ^= bit
    return products


def path_edges(adjacency, start, target):
    previous = {start: None}
    todo = deque([start])
    while target not in previous:
        v = todo.popleft()
        for w, edge in adjacency[v]:
            if w not in previous:
                previous[w] = v, edge
                todo.append(w)
    result = []
    while target != start:
        target, edge = previous[target]
        result.append(edge)
    return result


def forced_forest(two_ends, mandatory, vertices):
    sets = DisjointSets(vertices)
    adjacency = [[] for _ in range(vertices)]
    cycle = None
    for edge in mandatory:
        a, b = two_ends[edge]
        if sets.join(a, b):
            adjacency[a].append((b, edge))
            adjacency[b].append((a, edge))
        elif cycle is None:
            cycle = path_edges(adjacency, a, b) + [edge]
    return sets, cycle


def extend_dual_tree(two_ends, mandatory, order, q):
    sets = DisjointSets(q+1)
    tree = []
    for edge in mandatory:
        if not sets.join(*two_ends[edge]):
            raise ArithmeticError('a claimed mandatory forest has a cycle')
        tree.append(edge)
    for edge in order:
        if sets.join(*two_ends[edge]):
            tree.append(edge)
    if len(tree) != q:
        raise ArithmeticError('a source dual forest could not reach every cap')
    return sorted(tree)


def tree_cancellation_order(two_ends, tree, q):
    adjacency = [[] for _ in range(q+1)]
    for edge in tree:
        a, b = two_ends[edge]
        adjacency[a].append((b, edge))
        adjacency[b].append((a, edge))
    todo = deque([q])
    reached = {q}
    moves = []
    while todo:
        v = todo.popleft()
        for w, edge in sorted(adjacency[v]):
            if w not in reached:
                reached.add(w)
                todo.append(w)
                moves.append([edge, w])
    if len(reached) != q+1:
        raise ArithmeticError('the sampled dual tree is not boundary-rooted')
    return moves


def short_graph_rank(rows, selected, columns):
    position = {c: i for i, c in enumerate(columns)}
    ground = len(columns)
    sets = DisjointSets(ground+1)
    rank = 0
    for edge in selected:
        row = rows[edge]
        if len(row) not in (1, 2) or any(value != 1 for value in row.values()):
            raise ArithmeticError('a short-H edge is not an honest incidence row')
        ends = [position[c] for c in row]
        if len(ends) == 1:
            ends.append(ground)
        rank += sets.join(*ends)
    return rank


def audit_case(case, family, args, randomizer):
    started = time.perf_counter()
    raw, coordinates = case['triangulation'], case['coordinates']
    parallelity = normal_cut_parallelity(raw, coordinates, record_certificate=True)
    if parallelity['status'] != 'COMPLETE':
        raise ArithmeticError('unbounded source geometry unexpectedly incomplete: '+case['id'])
    if not verify_normal_cut_parallelity(raw, coordinates, parallelity['certificate']):
        raise ArithmeticError('source geometry failed independent authentication: '+case['id'])
    geometry = parallelity['geometry']
    incidence = source_core_top_incidence(raw, coordinates, geometry)
    core = geometry['core']
    primal, components = _forest(core, lambda: None)
    forest = set(primal)
    columns = [h['id'] for h in core['handles1'] if h['id'] not in forest]
    position = {c: i for i, c in enumerate(columns)}
    rows = []
    for handle in core['handles2']:
        # Opposite orientations have the same parity, but repeated crossings
        # must be counted before parity reduction. Saturation loses odd >=3.
        row = Counter(flag['handle'] for flag in handle['cycle']
                      if flag['dimension'] == 1 and flag['handle'] not in forest)
        rows.append(dict(sorted(row.items())))
    m, q, n = len(rows), len(core['handles3']), len(columns)
    a_rows = [sum((value % 2) << position[c] for c, value in row.items()) for row in rows]
    capped_a = [sum((min(2, value) % 2) << position[c] for c, value in row.items())
                for row in rows]
    two_ends = [[q if v is None else v for v in h['ends']] for h in incidence['two_handles']]
    b_rows = []
    for ends in two_ends:
        parity = 0
        for v in ends:
            if v != q:
                parity ^= 1 << v
        b_rows.append(parity)
    product = chain_product(a_rows, b_rows, q)
    if any(product):
        raise ArithmeticError('uncapped A-transpose B is nonzero: '+case['id'])
    rank_a, rank_b = binary_rank(a_rows), binary_rank(b_rows)
    if rank_a != dense_binary_rank(a_rows, n) or rank_b != dense_binary_rank(b_rows, q):
        raise ArithmeticError('independent binary rank algorithms disagree')
    if rank_b != q:
        raise ArithmeticError('source cap incidence lacks full column rank')
    beta2 = m-q-rank_a
    if beta2 < 0:
        raise ArithmeticError('the verified chain complex has negative beta2')
    mandatory = [r for r, row in enumerate(rows)
                 if sum(min(2, value) for value in row.values()) > 2 or
                 not row or len(row) == 1 and next(iter(row.values())) >= 2]
    mandatory_set = set(mandatory)
    short = [r for r in range(m) if r not in mandatory_set]
    sets, cycle = forced_forest(two_ends, mandatory, q+1)
    rank_d = binary_rank([b_rows[r] for r in mandatory])
    rank_short = binary_rank([a_rows[r] for r in short])
    rank_h = short_graph_rank(rows, short, columns)
    if rank_short != rank_h:
        raise ArithmeticError('the honest short-row matrix is not the H incidence matrix')
    record = dict(id=case['id'], family=family, tetrahedra=len(raw['tetrahedra']),
        source_sha256=digest(raw), coordinates_sha256=digest(coordinates),
        geometry_sha256=digest(geometry), source_geometry_authenticated=True,
        core_handle_counts=[len(core[f'handles{i}']) for i in range(4)],
        primal_forest=primal, nonforest_one_handles=columns,
        raw_occurrence_rows=[[[c, value] for c, value in row.items()] for row in rows],
        cap_endpoints=[h['ends'] for h in incidence['two_handles']],
        a_mod2_rows=list(map(hex, a_rows)), b_mod2_rows=list(map(hex, b_rows)),
        chain_identity=True, nonvacuous_chain=q > 0,
        ranks=dict(full_uncapped_a=rank_a, cap_b=rank_b, mandatory_b_rows=rank_d,
                   short_a=rank_short, short_graph_h=rank_h),
        core_betti_mod2=[len(set(components)), n-rank_a, beta2, 0],
        mandatory_rows=mandatory, honest_short_rows=short,
        mandatory_dual_forest=cycle is None,
        capped_parity_diagnostic=dict(is_homology_computation=False,
            chain_identity=not any(chain_product(capped_a, b_rows, q)),
            rank=binary_rank(capped_a),
            odd_entries_at_least_three=sum(value >= 3 and value % 2
                                            for row in rows for value in row.values())),
        sampled_dual_trees=[])
    if family == 'subdivision':
        record['source'] = case
    if cycle is not None:
        parity = 0
        for edge in cycle:
            parity ^= b_rows[edge]
        if parity or len(cycle) != len(set(cycle)) or rank_d >= len(mandatory):
            raise ArithmeticError('the mandatory dual cycle witness is invalid')
        record['mandatory_cycle_witness'] = cycle
    else:
        k = len(mandatory)
        if rank_d != k or rank_short != rank_a:
            raise ArithmeticError('mandatory forest row-rank preservation failed')
        ground = sets.root(q)
        quotient_vertices = sorted({sets.root(v) for v in range(q+1)} - {ground})
        quotient_index = {v: i for i, v in enumerate(quotient_vertices)}
        quotient_b = []
        for edge in short:
            parity = 0
            for v in two_ends[edge]:
                owner = sets.root(v)
                if owner != ground:
                    parity ^= 1 << quotient_index[owner]
            quotient_b.append(parity)
        quotient_rank = binary_rank(quotient_b)
        if quotient_rank != q-k or any(chain_product([a_rows[r] for r in short], quotient_b, q-k)):
            raise ArithmeticError('contracted short-row chain identity failed')
        graph_nullity = len(short)-quotient_rank-rank_h
        if graph_nullity != beta2:
            raise ArithmeticError('short graph formula does not equal full core beta2')
        record['contracted_graph'] = dict(vertices=len(quotient_vertices)+1,
            rank=quotient_rank, short_edges=len(short), short_h_rank=rank_h,
            short_chain_identity=True, predicted_residual_nullity=graph_nullity)
        orders = [('ascending', short), ('descending', short[::-1])]
        for index in range(args.random_trees):
            order = short.copy()
            randomizer.shuffle(order)
            orders.append(('random_'+str(index), order))
        seen = set()
        for label, order in orders:
            tree = extend_dual_tree(two_ends, mandatory, order, q)
            key = tuple(tree)
            if key in seen:
                continue
            seen.add(key)
            selected = set(tree)
            remaining = [r for r in range(m) if r not in selected]
            moves = tree_cancellation_order(two_ends, tree, q)
            proof = dict(schema='normal-core-top-reduction-v1',
                input_sha256=incidence['input_sha256'], moves=moves,
                surviving_two_handles=remaining)
            if replay_core_top_reduction(raw, coordinates, geometry, proof) is None:
                raise ArithmeticError('sampled dual tree failed independent source replay')
            residual_rank = short_graph_rank(rows, remaining, columns)
            matrix_rank = binary_rank([a_rows[r] for r in remaining])
            residual_nullity = len(remaining)-residual_rank
            if residual_rank != rank_h or matrix_rank != rank_a or residual_nullity != beta2:
                raise ArithmeticError('dual tree choice changed residual short-H nullity')
            record['sampled_dual_trees'].append(dict(label=label, dual_tree=tree,
                source_certificate=proof, source_replayed=True,
                residual_edges=len(remaining), residual_h_rank=residual_rank,
                residual_uncapped_matrix_rank=matrix_rank, residual_nullity=residual_nullity))
        record['attempted_tree_orders'] = len(orders)
    record['seconds'] = time.perf_counter()-started
    return record


def subdivisions(args):
    if args.subdivision_source is not None:
        data = json.loads(args.subdivision_source.read_text())
        sources = [r['source'] for r in data['cases'] if r.get('family') == 'subdivision']
        selected = [s for s in sources if 1 <= (len(s['triangulation']['tetrahedra'])-1)//3 <= 8]
        if sorted(len(s['triangulation']['tetrahedra']) for s in selected) != [1+3*q for q in range(1, 9)]:
            raise ArithmeticError('subdivision evidence does not contain exactly q=1 through 8')
        return selected
    from core_top_research.benchmark import source_case
    from normal_orbit_research.fixtures import export_triangulation
    answer = []
    for q in range(1, 9):
        triangulation, _ = source_case(q)
        raw = export_triangulation(triangulation)
        answer.append(dict(id='empty_layered_torus_subdivision_'+str(q),
                           triangulation=raw, coordinates=[[0]*7 for _ in raw['tetrahedra']]))
    return answer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--subdivision-source', type=Path)
    parser.add_argument('--random-trees', type=int, default=6)
    parser.add_argument('--seed', type=int, default=2610130027)
    args = parser.parse_args()
    if args.random_trees < 1:
        parser.error('--random-trees must be positive')
    corpus_path = FAST/'marked_parallelity_research/corpus.json'
    corpus = json.loads(corpus_path.read_text())['cases']
    files = [Path(__file__), corpus_path, FAST/'fastunknot/core_handlebody.py',
             FAST/'fastunknot/core_top_reduction.py', FAST/'fastunknot/core_top_reduction_verify.py',
             FAST/'fastunknot/normal_parallelity.py', FAST/'fastunknot/normal_parallelity_verify.py',
             FAST/'fastunknot/normal_parallelity_geometry.py', FAST/'fastunknot/normal_parallelity_reference.py',
             FAST/'fastunknot/normal_surface_geometry.py']
    hashes = {str(p.relative_to(FAST)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    report = dict(schema='core-chain-compatibility-audit-v1',
        started_utc=datetime.now(timezone.utc).isoformat(), python=sys.version,
        platform=platform.platform(), seed=args.seed, random_tree_orders=args.random_trees,
        source_sha256=hashes,
        subdivision_source_sha256=None if args.subdivision_source is None else
            hashlib.sha256(args.subdivision_source.read_bytes()).hexdigest(),
        conventions=dict(A='uncapped unsigned geometric cycle occurrences after the fixed primal forest, reduced mod2',
            B='source cap incidence mod2, retaining both ends of loops before reduction',
            D='all capped-total>2 rows, all empty rows, and all single-column rows with count>=2',
            H='honest one-unit or two-distinct-unit occurrence rows outside D, with a formal ground vertex',
            boundary_root='formal scheduling ground only; no topological boundary identification',
            homology='beta2 = m-q-rank(A), with independently verified rank(B)=q',
            claim='if D is G-forest then every dual tree containing D has the same short-H residual nullity beta2',
            scope='native authenticated geometric cores; arbitrary graph pairs need not satisfy the chain identity'),
        counts={}, cases=[])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    counts = Counter()
    randomizer = random.Random(args.seed)
    for family, cases in [('corpus', corpus), ('subdivision', subdivisions(args))]:
        for case in cases:
            record = audit_case(case, family, args, randomizer)
            report['cases'].append(record)
            counts[family+'_cases'] += 1
            counts[family+'_authenticated_sources'] += 1
            counts[family+'_chain_identity'] += 1
            counts[family+'_nonvacuous_chain_identity'] += record['nonvacuous_chain']
            counts[family+'_mandatory_forest'] += record['mandatory_dual_forest']
            counts[family+'_mandatory_cycle'] += not record['mandatory_dual_forest']
            if record['mandatory_dual_forest']:
                counts[family+'_eligible_beta2_zero'] += record['core_betti_mod2'][2] == 0
                counts[family+'_eligible_beta2_positive'] += record['core_betti_mod2'][2] > 0
                counts[family+'_sampled_tree_source_replays'] += len(record['sampled_dual_trees'])
                counts[family+'_sampled_tree_nullity_agreements'] += len(record['sampled_dual_trees'])
            counts[family+'_capped_parity_breaks_chain'] += not record['capped_parity_diagnostic']['chain_identity']
            counts[family+'_capped_rank_differs'] += record['capped_parity_diagnostic']['rank'] != record['ranks']['full_uncapped_a']
        report['counts'] = counts
        args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
        print(json.dumps(dict(stage=family+'_completed', counts=counts)), flush=True)
    report['finished_utc'] = datetime.now(timezone.utc).isoformat()
    args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')


if __name__ == '__main__':
    main()
