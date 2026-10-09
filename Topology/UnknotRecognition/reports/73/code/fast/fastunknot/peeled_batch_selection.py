"""Exact two-endpoint reward optimisation by weighted matching.

For an omitted set T of independently executable moves, optimise

    sum_v max({reward[i,v]: i in T} union {0}) - sum_{i in T} cost[i].

Each item has at most two rewarded vertices and nonnegative integral cost.
This is the algebraic subproblem arising from vertex-link-peeled Euler
scores on a fixed tetrahedron-disjoint coherent 3--2 move family.  It is
not an algorithm for constructing that family or recognising the unknot.

The reduction and witness evaluation use only the standard library.
Supplying a vertex cover of size at most two also gives a standard-library
linear-arithmetic-time exact solver, as applies to the canonical pulling
source with two interior poles.
The default polynomial solver imports NetworkX lazily and trusts its exact
integer maximum-weight-matching implementation.  The returned witness
independently proves its objective value, not maximum-weight optimality.
An independently supplied Edmonds dual witness can certify optimality via
verify_matching_dual; the optional backend does not export that witness.
For small instances, exhaustive_optimum provides an independent exact
cross-check; its exponential cost is explicit and separately bounded.
"""
from dataclasses import dataclass
from .cocycle_transport_verify import _shield_callback


@dataclass(frozen=True)
class _Item:
    cost: int
    rewards: tuple


def _parse(items):
    if type(items) not in (list, tuple):
        raise ValueError('items must be a list or tuple')
    result = []
    for row in items:
        if type(row) is not dict or set(row) != {'cost', 'rewards'}:
            raise ValueError('each item must contain exactly cost and rewards')
        cost, entries = row['cost'], row['rewards']
        if type(cost) is not int or cost < 0:
            raise ValueError('costs must be nonnegative integers')
        if type(entries) not in (list, tuple) or len(entries) > 2:
            raise ValueError('an item may reward at most two endpoints')
        rewards = {}
        for pair in entries:
            if type(pair) not in (list, tuple) or len(pair) != 2:
                raise ValueError('each reward must be a vertex-value pair')
            vertex, reward = pair
            if type(vertex) is not int or type(reward) is not int or reward < 0:
                raise ValueError('vertex IDs and nonnegative rewards must be integers')
            # A loop rewards one global vertex.  Its two descriptions do
            # not create two independently collectable rewards.
            rewards[vertex] = max(reward, rewards.get(vertex, 0))
        result.append(_Item(cost, tuple(sorted(rewards.items()))))
    return tuple(result)


def _indices(indices, count):
    if type(indices) not in (list, tuple, set, frozenset):
        raise ValueError('omitted indices must be a finite index collection')
    if any(type(i) is not int or not 0 <= i < count for i in indices):
        raise ValueError('omitted item index is out of range')
    if len(set(indices)) != len(indices):
        raise ValueError('an item cannot be omitted twice')
    return tuple(sorted(indices))


def _evaluate(parsed, omitted, check):
    rewards, cost = {}, 0
    for i in omitted:
        check()
        item = parsed[i]
        cost += item.cost
        for vertex, reward in item.rewards:
            rewards[vertex] = max(rewards.get(vertex, 0), reward)
    return sum(rewards.values())-cost


def evaluate_two_endpoint_rewards(items, omitted_indices, *, check=lambda: None):
    """Evaluate one feasible omitted set exactly; no optimality is inferred."""
    parsed = _parse(items)
    omitted = _indices(omitted_indices, len(parsed))
    return _evaluate(parsed, omitted, check)


def _reduction(parsed, check):
    baseline, choice = {}, {}
    for i, item in enumerate(parsed):
        check()
        for vertex, reward in item.rewards:
            baseline.setdefault(vertex, 0)
            choice.setdefault(vertex, None)
            profit = reward-item.cost
            if profit > baseline[vertex]:
                baseline[vertex], choice[vertex] = profit, i
    edges = {}
    for i, item in enumerate(parsed):
        check()
        if len(item.rewards) != 2:
            continue
        (u, first), (v, second) = item.rewards
        weight = first+second-item.cost-baseline[u]-baseline[v]
        # Nonpositive adjusted edges are unnecessary.  Among parallel
        # edges retain the highest weight, breaking ties by item index.
        if weight > 0 and ((u, v) not in edges or weight > edges[u, v][0]):
            edges[u, v] = weight, i
    return baseline, choice, edges


def two_endpoint_matching_reduction(items, *, check=lambda: None):
    """Expose the exact simple weighted graph and singleton baseline."""
    parsed = _parse(items)
    baseline, choice, edges = _reduction(parsed, check)
    return dict(
        baseline=[dict(vertex=v, value=baseline[v], item=choice[v])
                  for v in sorted(baseline)],
        baseline_value=sum(baseline.values()),
        edges=[dict(vertices=[u, v], weight=weight, item=i)
               for (u, v), (weight, i) in sorted(edges.items())],
        costs_dominate_endpoint_rewards=all(
            reward <= item.cost for item in parsed for _, reward in item.rewards))


def _validate_small_cover(cover_vertices, edges, check):
    if type(cover_vertices) not in (list, tuple):
        raise ValueError('cover_vertices must be a list or tuple')
    if (len(cover_vertices) > 2 or any(type(v) is not int for v in cover_vertices)
            or len(set(cover_vertices)) != len(cover_vertices)):
        raise ValueError('the supplied cover must have at most two distinct integer vertices')
    cover = tuple(sorted(cover_vertices))
    selected = set(cover)
    for u, v in edges:
        check()
        if u not in selected and v not in selected:
            raise ValueError('supplied cover misses a positive reduction edge')
    return cover


def _small_cover_matching(edges, cover, scale, check):
    """Exact matching for a validated cover of size <=2, in linear work."""
    cover_set = set(cover)
    top = {v: [] for v in cover}
    best = (0, (), ())

    def consider(pairs):
        nonlocal best
        # Positive transformed weights maximise original integral weight,
        # then minimise omissions.  Item order only makes remaining ties
        # deterministic; it does not claim a stronger lexicographic rule.
        score = sum(scale*edges[pair][0]-1 for pair in pairs)
        items = tuple(sorted(edges[pair][1] for pair in pairs))
        candidate = score, items, tuple(pairs)
        if score > best[0] or (score == best[0] and items < best[1]):
            best = candidate

    for (u, v), (weight, item) in edges.items():
        check()
        pair = u, v
        consider((pair,))
        if u in cover_set and v in cover_set:
            continue
        centre, outside = (u, v) if u in cover_set else (v, u)
        # Parallel edges were compressed, so these outside endpoints are
        # distinct.  At most one can be excluded by the other chosen edge.
        top[centre].append((scale*weight-1, item, outside, pair))
        top[centre].sort(key=lambda row: (-row[0], row[1], row[2]))
        del top[centre][2:]
    if len(cover) == 2:
        for first in top[cover[0]]:
            for second in top[cover[1]]:
                check()
                if first[2] != second[2]:
                    consider((first[3], second[3]))
    return set(best[2])


def solve_two_endpoint_rewards(items, *, cover_vertices=None, check=lambda: None):
    """Return an optimum using an optional exact weighted-matching backend.

    Positive singleton baselines cover the fully general algebraic case.
    In the coherent finite-manifold application every reward <= its item
    cost, so all baselines vanish and the omitted items themselves form a
    matching on their positively rewarded endpoints.  In this case ties
    are resolved in favour of retaining the largest number of items.
    For the general case the secondary rule only minimises matching edges;
    it need not minimise the number of reconstructed singleton items.

    With ``cover_vertices`` supplied, every positive reduction edge must
    meet one of at most two distinct integer IDs.  This validated path uses
    linear arithmetic work and no NetworkX import.  IDs not incident to a
    retained edge are harmless.  ``None`` selects the general backend.
    """
    parsed = _parse(items)
    baseline, choice, edges = _reduction(parsed, check)
    cover = (None if cover_vertices is None else
             _validate_small_cover(cover_vertices, edges, check))
    # A difference of one in integral total weight takes priority over
    # every possible difference in matching cardinality.  Merely deleting
    # zero-weight edges does not resolve ties between positive matchings.
    scale = len(parsed)+1
    if cover is not None:
        matching = _small_cover_matching(edges, cover, scale, check)
        optimality_basis = 'two-vertex-cover-exact-enumeration'
    elif edges:
        try:
            import networkx as nx
        except ImportError as error:
            raise RuntimeError('weighted matching requires the optional networkx package') from error
        graph = nx.Graph()
        graph.add_nodes_from(baseline)
        for (u, v), (weight, _) in edges.items():
            check()
            graph.add_edge(u, v, weight=scale*weight-1)
        check()
        matching = nx.max_weight_matching(graph, maxcardinality=False, weight='weight')
        optimality_basis = 'networkx-exact-integer-weighted-matching'
    else:
        matching = set()
        optimality_basis = 'edgeless-reduction'
    check()
    matched, matching_items, matching_value = set(), [], 0
    for pair in matching:
        check()
        u, v = sorted(pair)
        if u in matched or v in matched or (u, v) not in edges:
            raise ArithmeticError('matching backend returned an invalid edge set')
        matched.update((u, v))
        weight, item = edges[u, v]
        matching_items.append(item)
        matching_value += weight
    singleton_items = [choice[v] for v in baseline
                       if v not in matched and baseline[v] > 0]
    singleton_set = set(singleton_items)
    omitted_set = set(matching_items) | singleton_set
    omitted = tuple(i for i in range(len(parsed)) if i in omitted_set)
    value = _evaluate(parsed, omitted, check)
    bound = sum(baseline.values())+matching_value
    if value != bound:
        raise ArithmeticError('matching reconstruction disagrees with reduction value')
    dominated = all(reward <= item.cost for item in parsed for _, reward in item.rewards)
    return dict(
        omitted_indices=list(omitted),
        retained_indices=[i for i in range(len(parsed)) if i not in omitted_set],
        objective=value,
        matching_items=sorted(matching_items),
        singleton_items=[i for i in range(len(parsed)) if i in singleton_set],
        baseline_value=sum(baseline.values()), matching_value=matching_value,
        costs_dominate_endpoint_rewards=dominated,
        maximum_retention_tie_break=dominated,
        cover_vertices=None if cover is None else list(cover),
        optimality_basis=optimality_basis,
        independently_checked='feasibility-and-objective-only',
        stats=dict(items=len(parsed), rewarded_vertices=len(baseline),
                   matching_edges=len(edges)))


def exhaustive_optimum(items, *, max_items=20, check=lambda: None):
    """Independent exponential reference solver for explicitly small tests."""
    parsed = _parse(items)
    if type(max_items) is not int or max_items < 0:
        raise ValueError('max_items must be a nonnegative integer')
    if len(parsed) > max_items:
        raise ValueError('instance exceeds explicit exhaustive reference limit')
    best, omitted = 0, ()
    for mask in range(1 << len(parsed)):
        check()
        selected = tuple(i for i in range(len(parsed)) if mask & (1 << i))
        value = _evaluate(parsed, selected, check)
        if value > best or (value == best and len(selected) < len(omitted)):
            best, omitted = value, selected
    return dict(objective=best, omitted_indices=list(omitted),
                optimality_basis='exhaustive-subset-enumeration')


@_shield_callback
def verify_selection_value(items, result, *, check=lambda: None):
    """Check a feasible result's value; this does not certify optimality."""
    try:
        if type(result) is not dict or type(result.get('objective')) is not int:
            return False
        parsed = _parse(items)
        omitted = _indices(result['omitted_indices'], len(parsed))
        return result['objective'] == _evaluate(parsed, omitted, check)
    except (KeyError, TypeError, ValueError):
        return False


@_shield_callback
def verify_matching_dual(items, matching_items, certificate, *, check=lambda: None):
    """Check optimality of a matching using an independent Edmonds dual.

    ``certificate`` has exactly three fields::

        denominator: positive integer d
        vertices: [[vertex_id, nonnegative_integer_price], ...]
        odd_sets: [{vertices: [distinct_vertex_ids], price: nonnegative_integer}, ...]

    Missing vertex prices are zero.  An odd set has odd cardinality >= 3.
    Prices represent rationals with common denominator d.  Every retained
    reduction edge uv of weight w must satisfy

        y[u] + y[v] + sum(z[B] for B containing u,v) >= d*w.

    The sum of vertex prices plus sum((|B|-1)/2*z[B]) must equal d times
    the supplied matching weight.  This certifies maximum *weight*, not
    the solver's secondary preference for fewer omissions.  Arbitrary odd
    sets are allowed; laminarity is unnecessary for soundness.  Complexity
    is polynomial in the input and explicit certificate length.
    """
    try:
        parsed = _parse(items)
        _, _, edges = _reduction(parsed, check)
        matching_items = _indices(matching_items, len(parsed))
        if type(certificate) is not dict or set(certificate) != {
                'denominator', 'vertices', 'odd_sets'}:
            return False
        denominator = certificate['denominator']
        if type(denominator) is not int or denominator <= 0:
            return False
        universe = {v for item in parsed for v, _ in item.rewards}
        rows = certificate['vertices']
        if type(rows) not in (list, tuple):
            return False
        prices = {}
        for pair in rows:
            check()
            if type(pair) not in (list, tuple) or len(pair) != 2:
                return False
            vertex, price = pair
            if (type(vertex) is not int or vertex not in universe or vertex in prices
                    or type(price) is not int or price < 0):
                return False
            prices[vertex] = price
        rows = certificate['odd_sets']
        if type(rows) not in (list, tuple):
            return False
        odd_sets = []
        for row in rows:
            check()
            if type(row) is not dict or set(row) != {'vertices', 'price'}:
                return False
            vertices, price = row['vertices'], row['price']
            if (type(vertices) not in (list, tuple) or len(vertices) < 3
                    or len(vertices) % 2 != 1 or type(price) is not int or price < 0
                    or any(type(v) is not int or v not in universe for v in vertices)
                    or len(set(vertices)) != len(vertices)):
                return False
            odd_sets.append((frozenset(vertices), price))
        by_item = {i: (u, v, weight) for (u, v), (weight, i) in edges.items()}
        matched, weight_sum = set(), 0
        for i in matching_items:
            check()
            if i not in by_item:
                return False
            u, v, weight = by_item[i]
            if u in matched or v in matched:
                return False
            matched.update((u, v))
            weight_sum += weight
        for (u, v), (weight, _) in edges.items():
            check()
            slack = prices.get(u, 0)+prices.get(v, 0)
            for vertices, price in odd_sets:
                check()
                if u in vertices and v in vertices:
                    slack += price
            if slack < denominator*weight:
                return False
        dual = sum(prices.values()) + sum(
            ((len(vertices)-1)//2)*price for vertices, price in odd_sets)
        return dual == denominator*weight_sum
    except (KeyError, TypeError, ValueError):
        return False
