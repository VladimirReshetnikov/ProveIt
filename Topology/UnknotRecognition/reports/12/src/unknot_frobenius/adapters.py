"""Opt-in adapters: no global monkey patches, no verdict or transfer changes.

Pass fastunknot.planar.Planar (production) or the retained fixture (tests).
Only composition changes. Each engine's own basis numbering is preserved.
"""
from __future__ import annotations
from .kernel import CompiledPlan
from .subset import noop


def accelerated_planar_class(base_class):
    """Return a Planar subclass compatible with upstream 2026-10-07 interface."""
    class AdaptivePlanar(base_class):
        def __init__(self, shape_cache=True, *, minimum_pairs=64, method="auto",
                     dense_limit=18, check=noop):
            if type(minimum_pairs) is not int or minimum_pairs < 0:
                raise ValueError("minimum_pairs must be a nonnegative integer")
            if method not in {"auto", "sparse", "fast"}:
                raise ValueError("invalid contraction method")
            if type(dense_limit) is not int or dense_limit < 0:
                raise ValueError("dense_limit must be a nonnegative integer")
            self.minimum_pairs = minimum_pairs
            self.contraction_method = method
            self.dense_limit = dense_limit
            self.contraction_check = check
            self.kernel_stats = dict(calls=0, reference_calls=0, factored_calls=0,
                                     scalar_shortcuts=0, maximum_pairs=0,
                                     maximum_components=0)
            self.component_plans = {}
            super().__init__(shape_cache=shape_cache)

        def stage(self, points, slots):
            super().stage(points, slots)
            self.component_plans = {}

        def compose(self, a, b, c, f, g):
            stats = self.kernel_stats
            stats["calls"] += 1
            if not f or not g:
                return 0
            # These shortcuts already occur in the BitAlgebra ablation engine;
            # the inspected default Planar.compose did not include them.
            if (f == 1 and a == b) or (g == 1 and b == c) or (a == b == c and f == g):
                stats["scalar_shortcuts"] += 1
                if f == 1 and a == b:
                    return g
                if g == 1 and b == c:
                    return f
                return f & 1
            pairs = f.bit_count() * g.bit_count()
            stats["maximum_pairs"] = max(stats["maximum_pairs"], pairs)
            if pairs < self.minimum_pairs:
                stats["reference_calls"] += 1
                return super().compose(a, b, c, f, g)
            key = (a, b, c)
            cp = self.component_plans.get(key)
            if cp is None:
                plan = self.compose_plan(a, b, c)
                cp = CompiledPlan.from_plan(None if plan is None else tuple(p[:4] for p in plan[0]))
                self.component_plans[key] = cp
            stats["factored_calls"] += 1
            stats["maximum_components"] = max(stats["maximum_components"], cp.variables)
            return cp.apply(f, g, method=self.contraction_method,
                            dense_limit=self.dense_limit, check=self.contraction_check)

    AdaptivePlanar.__name__ = "AdaptivePlanar"
    return AdaptivePlanar


def install_on_empty_scan(scan, *, minimum_pairs=64, method="auto", dense_limit=18):
    """Replace a fresh FastScan's algebra without changing the scanner algorithm.

    Reject nonempty scans to prevent incompatible matching IDs or numbering.
    Returns the new algebra. Resource exceptions propagate, never become verdicts.
    """
    if scan.mid != [0] or scan.deg != [0] or scan.out != [{}] or scan.points or scan.live != 1:
        raise ValueError("adapter can only be installed on a fresh empty scanner")
    cls = accelerated_planar_class(type(scan.algebra))
    scan.algebra = cls(shape_cache=scan.algebra.shape_cache, minimum_pairs=minimum_pairs,
                       method=method, dense_limit=dense_limit, check=scan._check)
    return scan.algebra
