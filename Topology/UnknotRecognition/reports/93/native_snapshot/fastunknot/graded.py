"""Quantum grading and exact survivor support for the F2 planar scanner.

``FastScan`` erases quantum shifts because total rank does not require them.
This opt-in subclass retains the shifts through delooping and scalar Gaussian
elimination.  It supplies the support data needed for graded transfer.  No
default scanner state or pivot rule changes.

All shifts are the scanner's raw shifts: the usual diagram-wide orientation
normalization is not applied.  Only shift differences enter morphism degrees.
"""
from collections import defaultdict
from math import comb

from .scan_fast import FastScan


class GradedScan(FastScan):
    """The ordinary scanner with a quantum shift for each live object."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.qshift = [0]

    def add_crossing(self, slots, reduce_now=True):
        old_mid, old_q = self.mid, self.qshift
        # Install the new quantum shifts before dispatching to elimination.
        super().add_crossing(slots, reduce_now=False)
        closed_counts = {}
        for matching in set(old_mid):
            if matching is not None:
                closed_counts[matching] = tuple(
                    self.algebra.glue(matching, smoothing)[1]
                    for smoothing in (0, 1))
        shifts = []
        for a, matching in enumerate(old_mid):
            if matching is None:
                continue
            if not a & 511:
                self._check()
            for smoothing, closed in enumerate(closed_counts[matching]):
                shifts.extend(old_q[a] + smoothing + closed - 2 * label.bit_count()
                              for label in range(1 << closed))
        if len(shifts) != len(self.mid):
            raise ArithmeticError("quantum shifts disagree with delooping object order")
        self.qshift = shifts
        if reduce_now:
            self.eliminate()
            self.stats["max_objects_after_elimination"] = max(
                self.stats["max_objects_after_elimination"], self.live)

    def check_grading(self):
        """Check homological and quantum degrees of every stored monomial.

        For boundary size 2k and c circles in a glued pair of matchings, a
        monomial with r dots is homogeneous exactly when
        2r = c-k+q_target-q_source.  This diagnostic is deliberately explicit
        and is not an unconditional cost in normal recognition.
        """
        if len(self.qshift) != len(self.mid):
            raise ArithmeticError("quantum shifts and object slots disagree")
        half_width = len(self.points) // 2
        entries = terms = 0
        for a, row in enumerate(self.out):
            if not row:
                continue
            self._check()
            for b, value in row.items():
                if self.deg[b] != self.deg[a] + 1:
                    raise ArithmeticError("differential changes homological degree incorrectly")
                circles = self.algebra.basis(self.mid[a], self.mid[b])[1]
                expected = circles - half_width + self.qshift[b] - self.qshift[a]
                entries += 1
                remaining = value
                while remaining:
                    bit = remaining & -remaining
                    monomial = bit.bit_length() - 1
                    if 2 * monomial.bit_count() != expected:
                        raise ArithmeticError("differential is not quantum homogeneous")
                    remaining ^= bit
                    terms += 1
                if self.mid[a] == self.mid[b] and value & 1 and value != 1:
                    raise ArithmeticError("homogeneous units must be scalar identities")
        return {"entries": entries, "terms": terms}

    def ranks_by_bidegree(self):
        """Raw (homological, quantum) multiplicities of the live objects.

        These are homology dimensions only for a closed minimal complex, or
        another complex already certified to have zero differential.
        """
        result = defaultdict(int)
        for a, matching in enumerate(self.mid):
            if matching is not None:
                result[self.deg[a], self.qshift[a]] += 1
        return dict(sorted(result.items()))


def graded_survivor_profile(scan):
    """Return {(matching, h, q): multiplicity} of the minimal complex.

    The input must be a valid homogeneous chain complex.  Only scalar
    identities between copies of the same shifted matching enter the binary
    quotient.  Dead object slots are allowed.  The operation preserves scan
    objects and maps and polls the ordinary resource hook.
    """
    scan._check()
    groups = defaultdict(list)
    for a, matching in enumerate(scan.mid):
        if matching is not None:
            groups[matching, scan.deg[a], scan.qshift[a]].append(a)
    ranks = {}
    for (matching, degree, quantum), sources in groups.items():
        targets = groups.get((matching, degree + 1, quantum), ())
        if not targets:
            continue
        index = {a: j for j, a in enumerate(targets)}
        pivots = {}
        for a in sources:
            scan._check()
            column = 0
            for b, value in scan.out[a].items():
                if value & 1 and scan.mid[b] == matching:
                    if value != 1 or scan.qshift[b] != quantum or b not in index:
                        raise ArithmeticError("invalid homogeneous scalar differential")
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
        ranks[matching, degree, quantum] = len(pivots)
    result = {}
    for (matching, degree, quantum), sources in groups.items():
        count = (len(sources) - ranks.get((matching, degree, quantum), 0)
                 - ranks.get((matching, degree - 1, quantum), 0))
        if count < 0:
            raise ArithmeticError("negative residue homology dimension: input must have d^2=0")
        if count:
            result[matching, degree, quantum] = count
    scan._check()
    return result


def radical_hom_dimension(scan, source_matching, source_q, target_matching, target_q):
    """Dimension of homogeneous radical maps between two shifted matchings.

    Equal matchings at equal shifts have only the scalar identity in degree
    zero, which cannot occur in a minimal differential.  Every remaining
    homogeneous radical map strictly increases the quantum shift.
    """
    delta = target_q - source_q
    if delta <= 0:
        return 0
    half_width = len(scan.points) // 2
    circles = scan.algebra.basis(source_matching, target_matching)[1]
    twice_dots = circles - half_width + delta
    if twice_dots & 1 or not 0 <= twice_dots <= 2 * circles:
        return 0
    return comb(circles, twice_dots // 2)


def support_has_no_differential(scan, profile):
    """Whether the entire homogeneous radical differential is forced to zero.

    This is a sufficient support certificate; failure says nothing about
    whether the actual minimal differential vanishes.  Multiplicities do not
    affect the zero test.  A closed boundary always has no radical maps.
    """
    if not scan.points:
        return True
    by_degree = defaultdict(list)
    for matching, degree, quantum in profile:
        by_degree[degree].append((matching, quantum))
    for degree, sources in by_degree.items():
        targets = by_degree.get(degree + 1, ())
        if not targets:
            continue
        if min(q for _, q in sources) >= max(q for _, q in targets):
            continue
        for matching, quantum in sources:
            scan._check()
            for target, target_q in targets:
                if radical_hom_dimension(scan, matching, quantum, target, target_q):
                    return False
    return True


def install_zero_profile(scan, profile):
    """Replace the scan by a certified zero-differential survivor profile.

    The caller supplies the support proof.  This helper deliberately does not
    change elimination counters; each reduction strategy owns its accounting.
    """
    mid, degree, quantum = [], [], []
    for (matching, h, q), multiplicity in sorted(profile.items()):
        scan._check()
        mid.extend([matching] * multiplicity)
        degree.extend([h] * multiplicity)
        quantum.extend([q] * multiplicity)
    outgoing = [{} for _ in mid]
    incoming = [set() for _ in mid]
    empty_cache = {}
    scan._check()
    scan.mid, scan.deg, scan.qshift, scan.out, scan.inc, scan.composed = (
        mid, degree, quantum, outgoing, incoming, empty_cache)
    scan.live = len(mid)


class GradedResidueScan(GradedScan):
    """Eager support-only reference for comparison with full graded transfer."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.stats.update(graded_profiles=0, graded_shortcuts=0, graded_skipped_pairs=0,
                          graded_adjacent_shortcuts=0)

    def eliminate(self):
        if not self._try_profile():
            FastScan.eliminate(self)

    def _try_profile(self):
        profile = graded_survivor_profile(self)
        self.stats["graded_profiles"] += 1
        if not support_has_no_differential(self, profile):
            return False
        degrees = {degree for _, degree, _ in profile}
        if self.points and any(degree + 1 in degrees for degree in degrees):
            self.stats["graded_adjacent_shortcuts"] += 1
        count = sum(profile.values())
        pairs = (self.live - count) // 2
        install_zero_profile(self, profile)
        self.stats["eliminations"] += pairs
        self.stats["graded_shortcuts"] += 1
        self.stats["graded_skipped_pairs"] += pairs
        return True


class GradedAdaptiveScan(GradedResidueScan):
    """Existing sparse allowance followed by the stronger support certificate."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.stats.update(graded_adaptive_stages=0, graded_adaptive_switches=0,
                          graded_adaptive_fallbacks=0)

    def eliminate(self):
        self.stats["graded_adaptive_stages"] += 1
        if FastScan.eliminate(self, update_budget=max(256, 4 * self.live)):
            return
        self.stats["graded_adaptive_switches"] += 1
        if not self._try_profile():
            self.stats["graded_adaptive_fallbacks"] += 1
            FastScan.eliminate(self)
