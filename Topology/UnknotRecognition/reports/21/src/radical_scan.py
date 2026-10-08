"""Opt-in, disk-certified FastScan adapter; no recognition verdicts or CLI writes.

always = attempt full transfer at every certified stage (research control).
auto = earlier residual-fraction heuristic (not production tuned).
terminal = binary rank completion only at closed frontiers (existing principle).
adaptive = preserve cheap sparse progress, then attempt certified full transfer.
The separate production residue/adaptive modes are NOT replaced by this file.
"""
from fastunknot.scan_fast import FastScan
from radical import Complex, snapshot, binary_profile, contract_scalar, reduce_complex
from disk_frontier import certify_disk, GeometryError

class RadicalScan(FastScan):
    def __init__(self, *args, mode="adaptive", min_objects=64, residual_fraction=0.25, **kwargs):
        if mode not in ("always", "auto", "terminal", "adaptive"):
            raise ValueError("unknown radical scan mode")
        if type(min_objects) is not int or min_objects < 0:
            raise ValueError("min_objects must be a nonnegative integer")
        if not 0 <= residual_fraction <= 1:
            raise ValueError("residual_fraction must be in [0,1]")
        super().__init__(*args, **kwargs)
        self.radical_mode, self.min_objects = mode, min_objects
        self.residual_fraction = residual_fraction
        self.radical_profiles = []
        self.processed_crossings = []
        self.stats.update(radical_stages=0, radical_fallbacks=0, terminal_binary_stages=0,
                          disk_certificates=0, disk_declines=0, adaptive_switches=0)

    def add_crossing(self, slots, reduce_now=True):
        # Record the prefix only after the crossing transfer has committed.
        super().add_crossing(slots, reduce_now=False)
        self.processed_crossings.append(tuple(slots))
        if reduce_now:
            self.eliminate()
            self.stats['max_objects_after_elimination']=max(
                self.stats['max_objects_after_elimination'],self.live)

    def _install(self, c, before):
        self._check()
        inc = [set() for _ in c.mid]
        for j, row in enumerate(c.out):
            for k in row:
                inc[k].add(j)
        self.mid, self.deg, self.out, self.inc = c.mid, c.deg, c.out, inc
        self.live = c.n
        self.stats["eliminations"] += (before - c.n) // 2
        self.composed = {}

    def eliminate(self, *, update_budget=None):
        # The newly integrated upstream budget has precise Schur-pair semantics.
        # An externally requested budget is delegated, never silently ignored.
        if update_budget is not None:
            return super().eliminate(update_budget=update_budget)
        self._check()
        if self.radical_mode == 'adaptive':
            if super().eliminate(update_budget=max(256,4*self.live)):
                return True
            self.stats['adaptive_switches']+=1
        before = self.live
        if not self.points:
            c = snapshot(self)
            profile = binary_profile(c, self._check)
            mid, deg = [], []
            for (m, h), copies in sorted(profile.items()):
                if m != 0:
                    raise ArithmeticError("nonempty matching at a closed frontier")
                mid.extend([m] * copies)
                deg.extend([h] * copies)
            self._install(Complex(mid, deg, [{} for _ in mid]), before)
            self.stats["terminal_binary_stages"] += 1
            return True
        if self.radical_mode == "terminal" or (self.radical_mode == "auto" and before < self.min_objects):
            self.stats["radical_fallbacks"] += 1
            return super().eliminate()
        try:
            certificate=certify_disk(self.processed_crossings)
            if set(certificate.cyclic_order)!=set(self.points):
                raise GeometryError('recorded prefix and live frontier disagree')
        except GeometryError:
            self.stats['disk_declines']+=1
            self.stats['radical_fallbacks']+=1
            return super().eliminate()
        self.stats['disk_certificates']+=1
        self._check()
        c = snapshot(self)
        sc = contract_scalar(c, self._check)
        if self.radical_mode == "auto" and sc.r > self.residual_fraction * before:
            self.radical_profiles.append(dict(objects=before, residual=sc.r, chosen="scalar"))
            self.stats["radical_fallbacks"] += 1
            return super().eliminate()
        red = reduce_complex(c, self.algebra, contraction=sc, poll=self._check,
                             cyclic_order=certificate.cyclic_order)
        self._install(red.complex, before)
        self.stats["compositions"] += red.stats["compositions"]
        self.stats["radical_stages"] += 1
        self.radical_profiles.append(dict(red.stats, chosen="radical",
                                         prefix_sha256=certificate.prefix_sha256))
        return True
