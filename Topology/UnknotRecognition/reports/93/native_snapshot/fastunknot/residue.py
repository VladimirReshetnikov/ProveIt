"""Binary prediction of the minimal matching/degree profile of a valid scan.

This is not a replacement for the differential.  Off-diagonal and dotted
morphisms can survive when the binary residue vanishes.  Only a profile with
no consecutive occupied degrees (or a closed boundary) certifies that the
minimal differential is zero.  See synthesis/radical.tex for the proof and
the distinction from the incoming report's common-disk radical theorem.
"""
from collections import defaultdict

from .scan_fast import FastScan


def survivor_profile(scan):
    """Return {(matching id, degree): multiplicity}, without changing scan.

    The caller supplies a valid FastScan complex, in particular d^2=0.
    Only the scalar coefficient between *equal* matchings survives in the
    quotient.  Budget and race hooks are polled during binary elimination.
    Dead object slots and nonconsecutive degrees are allowed.
    """
    scan._check()
    groups = defaultdict(list)
    for a, matching in enumerate(scan.mid):
        if matching is not None:
            groups[matching, scan.deg[a]].append(a)
    ranks = {}
    for (matching, degree), sources in groups.items():
        targets = groups.get((matching, degree + 1), ())
        if not targets:
            continue
        index = {a: j for j, a in enumerate(targets)}
        pivots = {}
        for a in sources:
            scan._check()
            column = 0
            for b, value in scan.out[a].items():
                if value & 1 and scan.mid[b] == matching:
                    column ^= 1 << index[b]
            iterations = 0
            while column:
                top = column.bit_length() - 1
                old = pivots.get(top)
                if old is None:
                    pivots[top] = column
                    break
                column ^= old
                iterations += 1
                if not iterations & 255:
                    scan._check()
        ranks[matching, degree] = len(pivots)
    result = {}
    for (matching, degree), sources in groups.items():
        count = len(sources) - ranks.get((matching, degree), 0) - ranks.get((matching, degree - 1), 0)
        if count < 0:
            raise ArithmeticError("negative residue homology dimension: input must have d^2=0")
        if count:
            result[matching, degree] = count
    scan._check()
    return result


class ResidueScan(FastScan):
    """Opt-in elimination shortcut, otherwise the usual min-fill scanner."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.stats.update(residue_profiles=0, residue_shortcuts=0,
                          residue_skipped_pairs=0, residue_predicted_peak=0)

    def eliminate(self):
        if not self._try_profile():
            super().eliminate()

    def _try_profile(self):
        profile = survivor_profile(self)
        count = sum(profile.values())
        stats = self.stats
        stats["residue_profiles"] += 1
        stats["residue_predicted_peak"] = max(stats["residue_predicted_peak"], count)
        degrees = {degree for _, degree in profile}
        if self.points and any(degree + 1 in degrees for degree in degrees):
            # Residue homology determines the objects, not the radical maps.
            return False
        pairs = (self.live - count) // 2
        mid, deg = [], []
        for (matching, degree), multiplicity in sorted(profile.items()):
            self._check()
            mid.extend([matching] * multiplicity)
            deg.extend([degree] * multiplicity)
        self.mid, self.deg = mid, deg
        self.out = [{} for _ in mid]
        self.inc = [set() for _ in mid]
        self.live = count
        self.composed = {}
        stats["eliminations"] += pairs
        stats["residue_shortcuts"] += 1
        stats["residue_skipped_pairs"] += pairs
        return True


class AdaptiveScan(ResidueScan):
    """Retain sparse progress and consult residue homology only after fill grows.

    Each stage initially permits max(256, 4*objects) Schur update pairs. A
    pending pivot beyond that allowance causes one binary profile attempt.
    A certified zero differential finishes the stage; otherwise ordinary
    cancellation resumes on the partially reduced complex, without another
    profile attempt in that stage. This heuristic has no global complexity
    guarantee, and never interprets slow progress as a recognition verdict.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.stats.update(adaptive_stages=0, adaptive_switches=0,
                          adaptive_fallbacks=0, adaptive_shortcuts=0)

    def eliminate(self):
        stats = self.stats
        stats["adaptive_stages"] += 1
        if FastScan.eliminate(self, update_budget=max(256, 4 * self.live)):
            return
        stats["adaptive_switches"] += 1
        if self._try_profile():
            stats["adaptive_shortcuts"] += 1
        else:
            stats["adaptive_fallbacks"] += 1
            FastScan.eliminate(self)


def reduction_scanner(reduction):
    """Select an explicit cancellation policy with lazy full-transfer imports."""
    if reduction in ("corridor", "corridor-adaptive"):
        from .corridor import AdaptiveCorridorScan, CorridorScan
        return AdaptiveCorridorScan if reduction == "corridor-adaptive" else CorridorScan
    if reduction in ("graded", "graded-adaptive"):
        from .graded_transfer import GradedAdaptiveScan, GradedTransferScan
        return GradedAdaptiveScan if reduction == "graded-adaptive" else GradedTransferScan
    if reduction == "disk-adaptive":
        from .disk_scan import DiskAdaptiveScan
        return DiskAdaptiveScan
    if reduction == "adaptive":
        return AdaptiveScan
    if reduction == "residue":
        return ResidueScan
    raise ValueError("unknown residue reduction policy")
