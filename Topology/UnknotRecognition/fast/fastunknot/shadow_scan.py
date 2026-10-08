"""Marked residue-four continuations with interruptible exact determinants.

Research report 26 supplies the marked-completion argument and signed Tait
phase. Only genuine relative components at proper prefixes may be observed.
An exhausted determinant-work budget switches to query-capped Euler
observations; exhausted query capacity leaves complete capped scanning.
No partial lower bound can certify an unknot.
"""
from .component_scan import ComponentScan, components
from .diagram import DisjointSet
from .euler_scan import ClosureEuler, EulerBudget, component_euler_bound
from .ordering import best_scan_order, repeated_stages, validate_order
from .recovered_grading import recover_shifts
from time import monotonic


def _bareiss(matrix, tick):
    """Fraction-free integer determinant; poll between elimination rows."""
    size = len(matrix)
    if not size:
        return 1
    previous, sign = 1, 1
    for k in range(size - 1):
        tick(size - k)
        pivot = next((i for i in range(k, size) if matrix[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            matrix[k], matrix[pivot] = matrix[pivot], matrix[k]
            sign = -sign
        value = matrix[k][k]
        for i in range(k + 1, size):
            tick(size - k - 1)
            row = matrix[i]
            for j in range(k + 1, size):
                row[j], remainder = divmod(value * row[j] - row[k] * matrix[k][j], previous)
                if remainder:
                    raise ArithmeticError("nonexact fraction-free determinant division")
            row[k] = 0
        previous = value
    return sign * matrix[-1][-1]


class ShadowWorkBudget(EulerBudget):
    """The marked work allowance is exhausted; Euler query capacity may remain."""


class ClosureShadow(ClosureEuler):
    """Actual suffix closures evaluated modulo q^4-1, retaining the raw phase.

    The inherited cache stores unreduced q=1 values. The second cache stores
    reduced four-vectors for the same (stage, matching) keys. The query cap is
    shared; work units bound geometry visits, matrix allocation and arithmetic
    updates, not bit operations or elapsed time. Global deadlines take priority.
    """

    def __init__(self, *args, max_work=1_000_000, **kwargs):
        if max_work is not None and (type(max_work) is not int or max_work < 0):
            raise ValueError("shadow max_work must be a nonnegative integer or None")
        super().__init__(*args, **kwargs)
        self.max_work = max_work
        self.shadow_cache = {}
        self.stats.update(engine="marked-residue-four", work_units=0, determinants=0,
                          max_cofactor_size=0, shadow_evaluations=0,
                          max_unsplit_cofactor_size=0, tait_blocks=0,
                          tait_bridge_factors=0, tait_block_determinants=0,
                          tait_disconnected=0, tait_zero_factors=0,
                          observer_mode="shadow", euler_fallback_evaluations=0,
                          euler_fallback_states=0, euler_fallback_traversed_darts=0)

    def _tick(self, amount=1):
        self._check()
        if self.max_work is not None and self.stats["work_units"] + amount > self.max_work:
            raise ShadowWorkBudget("marked continuation work budget exhausted")
        self.stats["work_units"] += amount

    def evaluate_one(self, stage, pairs):
        if not 0 <= stage < len(self.crossings):
            raise ValueError("marked continuation requires a proper prefix")
        key = (stage, tuple(pairs))
        if key not in self.cache:
            self._tick(4 * (len(self.crossings) - stage))
        return super().evaluate(stage, pairs)

    def evaluate(self, stage, pairs):
        if not 0 <= stage < len(self.crossings):
            raise ValueError("marked continuation requires a nonempty suffix")
        self._check()
        key = (stage, tuple(pairs))
        self.stats["shadow_evaluations"] += 1
        if key in self.shadow_cache:
            return self.shadow_cache[key]
        euler = self.evaluate_one(stage, pairs)
        if euler % 2:
            raise ArithmeticError("closed nonempty link has odd unreduced Euler value")
        euler //= 2
        self._prepare(stage)
        self._tick(len(self.base_alpha))
        alpha = self.base_alpha.copy()
        # evaluate_one already checked exact coverage of the suffix boundary.
        for left, right in key[1]:
            a, b = self.boundary[left], self.boundary[right]
            alpha[a], alpha[b] = b, a
        n = len(alpha) // 4
        shadow, smoothing = DisjointSet(n), DisjointSet(4 * n)
        for d, a in enumerate(alpha):
            self._tick()
            shadow.union(d // 4, a // 4)
            smoothing.union(d, a)
            smoothing.union(d, d ^ 1)  # the all-zero smoothing
        shadow_count = len({shadow.find(c) for c in range(n)})
        parity = (len({smoothing.find(d) for d in range(4 * n)}) - 1) % 2

        face = [-1] * len(alpha)
        count = 0
        for start in range(len(alpha)):
            if face[start] >= 0:
                continue
            d = start
            while face[d] < 0:
                self._tick()
                face[d] = count
                a = alpha[d]
                d = (a & -4) | ((a + 1) & 3)
            if d != start:
                raise ArithmeticError("invalid face permutation")
            count += 1
        if count != n + 2 * shadow_count:
            raise ValueError("matching completion has a nonclassical rotation system")
        real, imaginary = 0, 0
        if shadow_count == 1:
            adjacent = [set() for _ in range(count)]
            for d, a in enumerate(alpha):
                self._tick()
                adjacent[face[d]].add(face[a])
            color = [-1] * count
            color[0] = 0
            queue = [0]
            for f in queue:
                self._tick()
                for g in adjacent[f]:
                    if color[g] < 0:
                        color[g] = 1 - color[f]
                        queue.append(g)
                    elif color[g] == color[f]:
                        raise ValueError("completion is not checkerboard colorable")
            if -1 in color:
                raise ArithmeticError("connected shadow has disconnected dual")
            # Either checkerboard color is valid; use the smaller cofactor.
            black_color = 0 if color.count(0) <= color.count(1) else 1
            black = {f: i for i, f in enumerate(f for f in range(count)
                                                if color[f] == black_color)}
            size = len(black) - 1
            # Small cofactors avoid graph-decomposition overhead. Larger
            # graphs factor at articulation vertices before dense allocation.
            factor_blocks = size > 16
            self._tick(0 if factor_blocks else size * size)
            matrix = None if factor_blocks else [[0] * size for _ in range(size)]
            edges = []
            b_total = 0
            for base in range(0, len(alpha), 4):
                self._tick()
                slots = [j for j in range(4) if color[face[base + j]] == black_color]
                if slots not in ([0, 2], [1, 3]):
                    raise ArithmeticError("nonalternating checkerboard corners")
                b = int(slots == [0, 2])
                b_total += b
                u, v = (black[face[base + j]] for j in slots)
                weight = -1 if b else 1
                if factor_blocks:
                    edges.append((u, v, weight))
                elif u != v:
                    if u:
                        matrix[u - 1][u - 1] += weight
                    if v:
                        matrix[v - 1][v - 1] += weight
                    if u and v:
                        matrix[u - 1][v - 1] -= weight
                        matrix[v - 1][u - 1] -= weight
            self.stats["max_unsplit_cofactor_size"] = max(self.stats["max_unsplit_cofactor_size"], size)
            self.stats["determinants"] += 1
            if factor_blocks:
                from .tait_blocks import spanning_tree_product
                determinant = spanning_tree_product(len(black), edges, self._tick, _bareiss, self.stats)
            else:
                self.stats["max_cofactor_size"] = max(self.stats["max_cofactor_size"], size)
                determinant = _bareiss(matrix, self._tick)
            unit = ((1, 0), (0, -1), (-1, 0), (0, 1))[(b_total + size) % 4]
            real, imaginary = determinant * unit[0], determinant * unit[1]
        if (real, imaginary)[1 - parity]:
            raise ArithmeticError("determinant phase violates Jones parity")
        difference = (real, imaginary)[parity]
        if (euler + difference) % 2 or (euler - difference) % 2:
            raise ArithmeticError("nonintegral residue-four reconstruction")
        result = [0] * 4
        result[parity], result[parity + 2] = (euler + difference) // 2, (euler - difference) // 2
        self.shadow_cache[key] = tuple(result)
        return tuple(result)


class _EulerPart:
    """One-way fallback sharing the original exact cache and query allowance."""
    def __init__(self, engine):
        self.engine = engine
        self.shadow_exhausted = False

    def disable_shadow(self):
        self.shadow_exhausted = True
        self.engine.stats["observer_mode"] = "euler"

    def evaluate(self, stage, pairs):
        if not 0 <= stage < len(self.engine.crossings):
            raise ValueError("marked continuation requires a proper prefix")
        if not self.shadow_exhausted:
            try:
                return self.engine.evaluate_one(stage, pairs)
            except ShadowWorkBudget:
                self.disable_shadow()
        # The reserve is the remaining shared query allowance, not a reset of
        # the spent marked-work budget. Direct geometry is O(suffix size) per
        # new query and still checks the global deadline, even on cache hits.
        key = (stage, tuple(pairs))
        fresh = key not in self.engine.cache
        before = self.engine.stats["traversed_darts"]
        value = ClosureEuler.evaluate(self.engine, stage, key[1])
        self.engine.stats["euler_fallback_evaluations"] += 1
        self.engine.stats["euler_fallback_states"] += int(fresh)
        self.engine.stats["euler_fallback_traversed_darts"] += (
            self.engine.stats["traversed_darts"] - before)
        return value


def component_shadow_bound(scan, engine, stage, *, cap=2):
    """Norm each whole marked completed component before summing multiplicities.

    Relative chain-homotopy provenance is supplied by the scanner, not proved
    by this observer. Absolute grading shifts are irrelevant to these norms.
    """
    if not 0 <= stage < len(engine.crossings):
        raise ValueError("cannot reduce arbitrary final unmarked generators separately")
    weight_cap = getattr(scan, "rank_cap", None)
    if cap is not None and (type(cap) is not int or cap < 1):
        raise ValueError("bound cap must be a positive integer or None")
    if weight_cap is not None and (cap is None or cap > weight_cap or weight_cap < 2):
        raise ValueError("requested bound exceeds saturated multiplicities")
    bound, records = 0, []
    for group in components(scan):
        engine._tick(len(group))
        shifts = recover_shifts(scan, group, check=engine._tick)
        vector = [0] * 4
        for v in group:
            engine._tick()
            value = engine.evaluate(stage, scan.algebra.pairs[scan.mid[v]])
            sign = -1 if scan.deg[v] % 2 else 1
            for j, coefficient in enumerate(value):
                vector[(j + shifts[v]) % 4] += sign * coefficient
        multiplicity = 1
        if hasattr(scan, "weights"):
            owner = scan.owner[group[0]]
            if any(scan.owner[v] != owner for v in group):
                raise ArithmeticError("differential mixes independent owners")
            multiplicity = sum(scan.weights[owner].values())
        norm = sum(abs(a) for a in vector)
        bound += multiplicity * norm
        records.append(dict(objects=group, shadow=vector, multiplicity=multiplicity,
                            relative_q=[shifts[v] for v in group], norm=norm))
        if cap is not None and bound >= cap:
            return cap, records
    return bound, records


def shadow_compressed_khovanov_decide(pd, *, order=None, max_objects=None, seconds=None,
                                     check_d_squared=False, shape_cache=None,
                                     euler_max_states=4096, shadow_max_work=1_000_000):
    """Complete exact decision with optional marked continuation obstructions."""
    pd = [tuple(crossing) for crossing in pd]
    if order is not None:
        order = validate_order(len(pd), order)
    deadline = None if seconds is None else monotonic() + seconds
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12)) if pd else []
    engine = ClosureShadow(pd, order, max_states=euler_max_states,
                           max_work=shadow_max_work, deadline=deadline)
    if shape_cache is None:
        shape_cache = len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
    scan = ComponentScan(max_objects=max_objects, deadline=deadline,
                         shape_cache=shape_cache, rank_cap=3)
    euler_part = _EulerPart(engine)
    euler_exhausted = False
    for stage in range(len(order) + 1):
        scan._check()
        copies = sum(sum(w.values()) for w in scan.weights)
        if not euler_exhausted and stage < len(order) and (stage == 0 or copies > 1):
            try:
                euler, chi = component_euler_bound(scan, euler_part, stage, cap=3)
                records = []
                bound = 2 if euler >= 3 else 0
                if bound < 2 and not euler_part.shadow_exhausted:
                    try:
                        bound, records = component_shadow_bound(scan, engine, stage)
                    except ShadowWorkBudget:
                        # The Euler bound for this whole stage already completed.
                        # Discard any partial marked observation; future stages
                        # retain the remaining exact Euler query capacity.
                        euler_part.disable_shadow()
            except EulerBudget:
                euler_exhausted = True
                euler_part.shadow_exhausted = True
                engine.stats["observer_mode"] = "scan"
            else:
                if bound >= 2:
                    stats = dict(scan.stats, **scan.algebra.stats)
                    return dict(status="KNOTTED", method="component-euler" if euler >= 3 else "marked-residue-four",
                                reduced_rank_lower_bound_capped=2, stage=stage, crossings=len(order),
                                marked_label=pd[order[-1]][0], components=records, stats=stats,
                                euler_characteristics=chi,
                                multiplicities_capped=[sum(w.values()) for w in scan.weights],
                                order=order, shadow_stats=dict(engine.stats), shadow_exhausted=euler_part.shadow_exhausted,
                                euler_exhausted=euler_exhausted)
        if stage < len(order):
            scan.add_crossing(pd[order[stage]])
            if check_d_squared:
                scan.check_d_squared()
    rank = scan.total_rank() if pd else 2
    if rank not in (2, 3):
        raise ArithmeticError("a validated knot must have unreduced rank at least two")
    return dict(status="UNKNOT" if rank == 2 else "KNOTTED", method="closed-rank",
                rank_capped=rank, rank_cap=3, stage=len(order), crossings=len(order),
                stats=dict(scan.stats, **scan.algebra.stats), order=order,
                shadow_stats=dict(engine.stats), shadow_exhausted=euler_part.shadow_exhausted,
                euler_exhausted=euler_exhausted)
