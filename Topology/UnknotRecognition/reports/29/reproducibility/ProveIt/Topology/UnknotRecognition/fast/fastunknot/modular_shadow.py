"""Boundary-reused modular Euler obstructions with complete capped fallback.

The scanner still computes Khovanov homology over F2. Auxiliary odd primes
reduce integer completed Euler vectors only. Zero modular determinants and
small lower bounds are never unknot certificates.
"""
from time import monotonic

from .component_scan import ComponentScan, components
from .euler_scan import ClosureEuler, EulerBudget, component_euler_bound
from .modular_lattice import (crt_vector, minimum_l1_lift, threshold_is_exact,
                              validate_primes)
from .ordering import best_scan_order, repeated_stages, validate_order
from .recovered_grading import recover_shifts
from .shadow_scan import ClosureShadow, ShadowWorkBudget, _EulerPart


DEFAULT_PRIMES = (65521,)


class ModularClosureShadow(ClosureShadow):
    """One active suffix geometry, one response per prime, shared query budget."""

    def __init__(self, pd, order, *, primes=DEFAULT_PRIMES, **kwargs):
        super().__init__(pd, order, **kwargs)
        self.pd = tuple(tuple(c) for c in pd)
        self.order = tuple(order)
        self.primes = validate_primes(primes, self._check)
        self.palette = None
        self.boundary_geometry = None
        self.geometry_stage = None
        self.partitions = {}
        self.kernels = {}
        self.cofactors = {}
        self.stats.update(engine="modular-marked-residue-four",
                          boundary_preparations=0, boundary_queries=0,
                          modular_kernel_builds=0, modular_determinants=0,
                          modular_partition_hits=0, modular_cache_hits=0,
                          max_common_vertices=0, max_terminal_count=0,
                          max_modular_nullity=0, max_query_matrix=0,
                          primes_completed=0, exact_threshold_observations=0,
                          incomplete_threshold_observations=0,
                          boundary_declines=0)
        self.last_observation = None

    def _geometry(self, stage):
        self._check()
        if self.geometry_stage == stage:
            return self.boundary_geometry
        from .boundary_tait import BoundaryTait, coloring
        if self.palette is None:
            palette = coloring(self.pd, check=self._tick)
            self.palette = palette
        geometry = BoundaryTait(self.pd, self.order, stage,
                                palette=self.palette, check=self._tick)
        # A completed constructor is the publication boundary. No partial
        # geometry or elimination state is retained after interruption.
        self.boundary_geometry = geometry
        self.geometry_stage = stage
        self.partitions, self.kernels, self.cofactors = {}, {}, {}
        self.stats["boundary_preparations"] += 1
        self.stats["max_common_vertices"] = max(
            self.stats["max_common_vertices"], len(geometry.laplacian))
        self.stats["max_terminal_count"] = max(
            self.stats["max_terminal_count"], len(geometry.terminals))
        return geometry

    def _partition(self, stage, pairs):
        geometry = self._geometry(stage)
        pairs = tuple(pairs)
        if pairs not in self.partitions:
            data = geometry.partition(pairs, check=self._tick)
            self.partitions[pairs] = data
            self.stats["boundary_queries"] += 1
        return self.partitions[pairs]

    def evaluate_one(self, stage, pairs):
        if not 0 <= stage < len(self.crossings):
            raise ValueError("marked continuation requires a proper prefix")
        self._check()
        key = (stage, tuple(pairs))
        if key in self.cache or self.geometry_stage != stage:
            return super().evaluate_one(stage, key[1])
        if self.max_states is not None and self.stats["states"] >= self.max_states:
            raise EulerBudget("closure Euler state budget exhausted")
        data = self._partition(stage, key[1])
        value = data["unreduced_euler"]
        self.cache[key] = value
        self.stats["states"] += 1
        self.stats["evaluations"] += 1
        self.stats["max_coefficient_bits"] = max(
            self.stats["max_coefficient_bits"], abs(value).bit_length())
        return value

    def evaluate(self, stage, pairs, prime=None):
        if prime is None:
            prime = self.primes[0]
        if prime not in self.primes:
            raise ValueError("prime is outside this observer's validated palette")
        if not 0 <= stage < len(self.crossings):
            raise ValueError("cannot mark arbitrary final unmarked generators")
        self._check()
        pairs = tuple(pairs)
        key = (stage, pairs, prime)
        self.stats["shadow_evaluations"] += 1
        if key in self.shadow_cache:
            self.stats["modular_cache_hits"] += 1
            return self.shadow_cache[key]
        euler = self.evaluate_one(stage, pairs)
        if euler % 2:
            raise ArithmeticError("unreduced closed Euler value must be even")
        data = self._partition(stage, pairs)
        if data["unreduced_euler"] != euler:
            raise ArithmeticError("boundary Euler value disagrees with cached exact value")
        determinant = 0
        if data["shadow_components"] == 1:
            geometry = self.boundary_geometry
            if prime not in self.kernels:
                from .modular_response import ModularTerminalKernel
                kernel = ModularTerminalKernel.build(
                    geometry.laplacian, geometry.terminals, prime, check=self._tick)
                self.kernels[prime] = kernel
                self.stats["modular_kernel_builds"] += 1
                self.stats["max_modular_nullity"] = max(
                    self.stats["max_modular_nullity"], kernel.nullity)
            kernel = self.kernels[prime]
            names = {}
            partition = tuple(names.setdefault(v, len(names)) for v in data["partition"])
            cofactor_key = (prime, partition)
            if cofactor_key not in self.cofactors:
                value = kernel.query(partition, check=self._tick)
                self.cofactors[cofactor_key] = value
                self.stats["modular_determinants"] += 1
                size = kernel.nullity + len(names) - 1
                if kernel.nullity <= len(names) - 1:
                    self.stats["max_query_matrix"] = max(self.stats["max_query_matrix"], size)
            else:
                self.stats["modular_partition_hits"] += 1
            determinant = self.cofactors[cofactor_key]
        parity = (data["zero_circles"] - 1) % 2
        if data["shadow_components"] == 1 and data["phase"] % 2 != parity:
            raise ArithmeticError("connected Tait phase disagrees with smoothing parity")
        unit = ((1, 0), (0, -1), (-1, 0), (0, 1))[data["phase"]]
        value_i = (unit[0] * determinant % prime, unit[1] * determinant % prime)
        if value_i[1 - parity]:
            raise ArithmeticError("modular determinant phase violates Jones parity")
        difference = value_i[parity]
        inverse_two = (prime + 1) // 2
        reduced_euler = (euler // 2) % prime
        result = [0] * 4
        result[parity] = (reduced_euler + difference) * inverse_two % prime
        result[parity + 2] = (reduced_euler - difference) * inverse_two % prime
        self.shadow_cache[key] = tuple(result)
        return tuple(result)


def component_modular_shadow_bound(scan, engine, stage, *, cap=2):
    """Observe whole genuine components, aggregate, CRT-refine, then norm.

    The returned records support replay of this arithmetic. Provenance of the
    relative complex still requires the validated source and scanner replay.
    """
    if not 0 <= stage < len(engine.crossings):
        raise ValueError("modular observation requires a proper marked prefix")
    if cap is not None and (type(cap) is not int or cap < 1):
        raise ValueError("cap must be positive or None")
    weight_cap = getattr(scan, "rank_cap", None)
    if weight_cap is not None and (cap is None or cap > weight_cap or weight_cap < 2):
        raise ValueError("requested lower-bound cap exceeds saturated multiplicities")
    groups = []
    suffix_size = len(engine.crossings) - stage
    # A signed spanning-tree cofactor has at most binomial(s, v-1)
    # terms, and every binomial coefficient is <= 2**(s-1) for s>=1.
    tree_bound = 1 << (suffix_size - 1)
    for group in components(scan):
        engine._tick(len(group))
        shifts = recover_shifts(scan, group, check=engine._tick)
        exact_sum, coordinate_bound = 0, 0
        for v in group:
            engine._tick()
            value = engine.evaluate_one(stage, scan.algebra.pairs[scan.mid[v]])
            if value % 2:
                raise ArithmeticError("completed object has odd unreduced Euler value")
            value //= 2
            exact_sum += -value if scan.deg[v] % 2 else value
            coordinate_bound += (abs(value) + tree_bound) // 2
        multiplicity = 1
        if hasattr(scan, "weights"):
            owner = scan.owner[group[0]]
            if any(scan.owner[v] != owner for v in group):
                raise ArithmeticError("differential mixes independent component owners")
            multiplicity = sum(scan.weights[owner].values())
        groups.append(dict(objects=group, shifts=shifts, exact_sum=exact_sum,
                           coordinate_bound=coordinate_bound, multiplicity=multiplicity,
                           residues=(0, 0, 0, 0)))
    modulus, records = 1, []
    bound = 0
    for prime_index, prime in enumerate(engine.primes):
        next_modulus = modulus * prime
        records, bound = [], 0
        for group in groups:
            vector = [0] * 4
            for v in group["objects"]:
                engine._tick()
                value = engine.evaluate(stage, scan.algebra.pairs[scan.mid[v]], prime)
                sign = -1 if scan.deg[v] % 2 else 1
                for j, coefficient in enumerate(value):
                    vector[(j + group["shifts"][v]) % 4] += sign * coefficient
            vector = tuple(x % prime for x in vector)
            residues = crt_vector(group["residues"], modulus, vector, prime)
            group["residues"] = residues
            norm, lift = minimum_l1_lift(residues, next_modulus, group["exact_sum"])
            bound += group["multiplicity"] * norm
            records.append(dict(objects=group["objects"], residues=list(residues),
                                minimum_lift=list(lift), modulus=next_modulus,
                                exact_euler=group["exact_sum"],
                                coordinate_bound=group["coordinate_bound"],
                                relative_q=[group["shifts"][v] for v in group["objects"]],
                                multiplicity=group["multiplicity"], norm=norm))
            if cap is not None and bound >= cap:
                engine.last_observation = dict(stage=stage, modulus=next_modulus,
                    primes=list(engine.primes[:prime_index + 1]), threshold_exact=True,
                    obstruction=True, observed_components=len(records), total_components=len(groups))
                return cap, records
        modulus = next_modulus
        engine.stats["primes_completed"] += 1
        exact = threshold_is_exact(modulus,
            [g["coordinate_bound"] for g in groups], [g["multiplicity"] for g in groups],
            threshold=(cap - 1 if cap is not None else 1), exact_sums=True)
        engine.last_observation = dict(stage=stage, modulus=modulus,
            primes=list(engine.primes[:prime_index + 1]), threshold_exact=exact,
            obstruction=False, observed_components=len(records), total_components=len(groups))
        # cap=None requests a lower bound, not full integer reconstruction.
        if exact and cap is not None:
            engine.stats["exact_threshold_observations"] += 1
            break
    else:
        if engine.last_observation and engine.last_observation["threshold_exact"]:
            engine.stats["exact_threshold_observations"] += 1
        else:
            engine.stats["incomplete_threshold_observations"] += 1
    return bound, records


def modular_shadow_khovanov_decide(pd, *, order=None, max_objects=None, seconds=None,
                                  check_d_squared=False, shape_cache=None,
                                  euler_max_states=4096, shadow_max_work=1_000_000,
                                  primes=DEFAULT_PRIMES):
    """Complete F2 recognition with optional modular integer obstructions.

    Low-level input must be a validated classical one-component PD, as for
    the existing shadow scanner. The public recognize() API validates it.
    """
    pd = [tuple(crossing) for crossing in pd]
    if order is not None:
        order = validate_order(len(pd), order)
    deadline = None if seconds is None else monotonic() + seconds
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12)) if pd else []
    engine = ModularClosureShadow(pd, order, primes=primes, max_states=euler_max_states,
                                  max_work=shadow_max_work, deadline=deadline)
    if shape_cache is None:
        shape_cache = len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
    scan = ComponentScan(max_objects=max_objects, deadline=deadline,
                         shape_cache=shape_cache, rank_cap=3)
    euler_part, euler_exhausted = _EulerPart(engine), False
    for stage in range(len(order) + 1):
        scan._check()
        copies = sum(sum(w.values()) for w in scan.weights)
        if not euler_exhausted and stage < len(order) and (stage == 0 or copies > 1):
            try:
                euler, chi = component_euler_bound(scan, euler_part, stage, cap=3)
                records = []
                bound = 2 if euler >= 3 else 0
                if bound < 2 and not euler_part.shadow_exhausted:
                    from .boundary_tait import BoundaryDeclined
                    try:
                        bound, records = component_modular_shadow_bound(scan, engine, stage)
                    except ShadowWorkBudget:
                        euler_part.disable_shadow()
                    except BoundaryDeclined:
                        # A coloring decline means this representation cannot
                        # answer. It is never a topological obstruction.
                        engine.stats["boundary_declines"] += 1
                        euler_part.disable_shadow()
            except EulerBudget:
                euler_exhausted = True
                euler_part.shadow_exhausted = True
                engine.stats["observer_mode"] = "scan"
            else:
                if bound >= 2:
                    return dict(status="KNOTTED", method=("component-euler" if euler >= 3
                                else "marked-residue-four-modular"),
                        reduced_rank_lower_bound_capped=2, stage=stage, crossings=len(order),
                        marked_label=pd[order[-1]][0], components=records,
                        stats=dict(scan.stats, **scan.algebra.stats),
                        euler_characteristics=chi,
                        multiplicities_capped=[sum(w.values()) for w in scan.weights],
                        order=order, shadow_stats=dict(engine.stats),
                        modular_observation=engine.last_observation,
                        shadow_exhausted=euler_part.shadow_exhausted,
                        euler_exhausted=euler_exhausted)
        if stage < len(order):
            scan.add_crossing(pd[order[stage]])
            if check_d_squared:
                scan.check_d_squared()
    rank = scan.total_rank() if pd else 2
    if rank not in (2, 3):
        raise ArithmeticError("validated knot must have unreduced rank at least two")
    return dict(status="UNKNOT" if rank == 2 else "KNOTTED", method="closed-rank",
                rank_capped=rank, rank_cap=3, stage=len(order), crossings=len(order),
                stats=dict(scan.stats, **scan.algebra.stats), order=order,
                shadow_stats=dict(engine.stats), modular_observation=engine.last_observation,
                shadow_exhausted=euler_part.shadow_exhausted, euler_exhausted=euler_exhausted)
