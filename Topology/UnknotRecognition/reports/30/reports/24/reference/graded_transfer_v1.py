"""Quantum triangular contraction for the production F2 tangle scanner.

This prototype uses a binary special contraction of the scalar differential,
then evaluates the full homological perturbation transfer in increasing quantum
shift.  It retains the radical differential; consecutive surviving degrees are
allowed.  The production source is imported, never patched.
"""
from __future__ import annotations

from collections import defaultdict

from fastunknot.scan_fast import FastScan


def bits(value):
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


class BinaryBasis:
    def __init__(self):
        self.pivots = {}

    def add(self, vector, coordinates=0):
        while vector:
            top = vector.bit_length() - 1
            old = self.pivots.get(top)
            if old is None:
                self.pivots[top] = vector, coordinates
                return True
            vector ^= old[0]
            coordinates ^= old[1]
        return False

    def solve(self, vector):
        coordinates = 0
        while vector:
            top = vector.bit_length() - 1
            old = self.pivots.get(top)
            if old is None:
                raise ArithmeticError("incomplete scalar basis")
            vector ^= old[0]
            coordinates ^= old[1]
        return coordinates


def xor_entry(row, target, value):
    if value:
        new = row.get(target, 0) ^ value
        if new:
            row[target] = new
        else:
            row.pop(target, None)


def binary_contraction(scan):
    """Return a special contraction of d0, using group-local bit matrices.

    I columns are bit masks on old objects. P and H columns are bit masks on
    survivors and old objects respectively. All coefficients are typed scalar
    identities; H lowers homological degree and preserves matching and q.
    """
    groups = defaultdict(list)
    for a, matching in enumerate(scan.mid):
        if matching is not None:
            groups[matching, scan.qshift[a], scan.deg[a]].append(a)
    keys = sorted(groups)
    images, lifts, kernels = {}, {}, {}
    for key in keys:
        scan._check()
        matching, quantum, degree = key
        sources = groups[key]
        targets = groups.get((matching, quantum, degree + 1), ())
        target_index = {v: i for i, v in enumerate(targets)}
        basis = BinaryBasis()
        nullspace = []
        for i, a in enumerate(sources):
            if not i & 255:
                scan._check()
            vector = 0
            for b, value in scan.out[a].items():
                if scan.qshift[b] == quantum:
                    if scan.mid[b] != matching or value != 1:
                        raise ArithmeticError("weight-zero map is not a typed identity")
                    vector ^= 1 << target_index[b]
            coordinates = 1 << i
            while vector:
                top = vector.bit_length() - 1
                old = basis.pivots.get(top)
                if old is None:
                    basis.pivots[top] = vector, coordinates
                    break
                vector ^= old[0]
                coordinates ^= old[1]
            if not vector:
                nullspace.append(coordinates)
        ordered = [basis.pivots[top] for top in sorted(basis.pivots)]
        images[key] = [pair[0] for pair in ordered]
        lifts[key] = [pair[1] for pair in ordered]
        kernels[key] = nullspace

    size = len(scan.mid)
    i_cols, p_cols, h_cols = [], [0] * size, [0] * size
    survivor_mid, survivor_deg, survivor_q = [], [], []
    for key in keys:
        scan._check()
        matching, quantum, degree = key
        vertices = groups[key]
        prev = matching, quantum, degree - 1
        boundaries = images.get(prev, [])
        independent = BinaryBasis()
        for v in boundaries:
            if not independent.add(v):
                raise ArithmeticError("dependent boundary basis")
        reps = []
        for v in kernels[key]:
            if independent.add(v):
                reps.append(v)
        basis_vectors = boundaries + reps + lifts[key]
        if len(basis_vectors) != len(vertices):
            raise ArithmeticError("d0 is not a chain differential")
        inverse = BinaryBasis()
        for i, v in enumerate(basis_vectors):
            if not inverse.add(v, 1 << i):
                raise ArithmeticError("scalar chain decomposition is singular")
        offset = len(i_cols)
        for v in reps:
            i_cols.append(sum(1 << vertices[j] for j in bits(v)))
            survivor_mid.append(matching)
            survivor_deg.append(degree)
            survivor_q.append(quantum)
        prev_vertices = groups.get(prev, ())
        prev_lifts = lifts.get(prev, ())
        bcount, rcount = len(boundaries), len(reps)
        for j, a in enumerate(vertices):
            if not j & 255:
                scan._check()
            coordinates = inverse.solve(1 << j)
            p_cols[a] = ((coordinates >> bcount) & ((1 << rcount) - 1)) << offset
            local_h = 0
            for b in bits(coordinates & ((1 << bcount) - 1)):
                local_h ^= prev_lifts[b]
            h_cols[a] = sum(1 << prev_vertices[b] for b in bits(local_h))
    return dict(i=i_cols, p=p_cols, h=h_cols, mid=survivor_mid,
                deg=survivor_deg, q=survivor_q)


def transfer(scan, *, certificates=False):
    """Compute the full minimal complex and optional special contraction.

    q strictly increases on every radical map. Processing q once solves
    Z = I + H delta Z exactly, with no guessed perturbation truncation.
    """
    scalar = binary_contraction(scan)
    i_cols, p_cols, h_cols = scalar['i'], scalar['p'], scalar['h']
    quanta = sorted({scan.qshift[a] for a, m in enumerate(scan.mid) if m is not None})
    radical = [[] for _ in scan.mid]
    edges = 0
    for a, row in enumerate(scan.out):
        if not row:
            continue
        for b, value in row.items():
            if scan.qshift[b] < scan.qshift[a]:
                raise ArithmeticError("negative intrinsic weight in graded input")
            if scan.qshift[b] > scan.qshift[a]:
                radical[a].append((b, value))
                edges += 1
    alg = scan.algebra
    output = [{} for _ in i_cols]
    inclusion = []
    compositions = xor_updates = 0
    for source, initial in enumerate(i_cols):
        scan._check()
        source_matching = scalar['mid'][source]
        pending = defaultdict(dict)
        lifted = {}
        for quantum in quanta:
            if quantum < scalar['q'][source]:
                continue
            w = pending.pop(quantum, {})
            z = {a: 1 for a in bits(initial)} if quantum == scalar['q'][source] else {}
            for a, value in w.items():
                for target in bits(p_cols[a]):
                    xor_entry(output[source], target, value)
                    xor_updates += 1
                for target in bits(h_cols[a]):
                    xor_entry(z, target, value)
                    xor_updates += 1
            if certificates:
                lifted.update(z)
            for a, value in z.items():
                for b, delta in radical[a]:
                    compositions += 1
                    product = alg.compose(source_matching, scan.mid[a], scan.mid[b], value, delta)
                    xor_entry(pending[scan.qshift[b]], b, product)
                    xor_updates += 1
            scan._check()
        if certificates:
            inclusion.append(lifted)
    result = dict(mid=scalar['mid'], deg=scalar['deg'], q=scalar['q'], out=output,
                  scalar=scalar, radical_edges=edges, compositions=compositions,
                  coefficient_xors=xor_updates)
    if not certificates:
        return result

    # The optional reverse transfer constructs P' and H' for independent
    # full identities. It is excluded from production-mode timings.
    projection, homotopy = [], []
    for source, matching in enumerate(scan.mid):
        if matching is None:
            projection.append({})
            homotopy.append({})
            continue
        pending = defaultdict(dict)
        pending[scan.qshift[source]][source] = 1
        proj, hom = {}, {}
        for quantum in quanta:
            if quantum < scan.qshift[source]:
                continue
            y = pending.pop(quantum, {})
            hy = {}
            for a, value in y.items():
                for target in bits(p_cols[a]):
                    xor_entry(proj, target, value)
                for target in bits(h_cols[a]):
                    xor_entry(hy, target, value)
            hom.update(hy)
            for a, value in hy.items():
                for b, delta in radical[a]:
                    product = alg.compose(matching, scan.mid[a], scan.mid[b], value, delta)
                    xor_entry(pending[scan.qshift[b]], b, product)
        projection.append(proj)
        homotopy.append(hom)
    result.update(inclusion=inclusion, projection=projection, homotopy=homotopy)
    return result


def matrix_compose(alg, source_mid, middle_mid, target_mid, first, second):
    result = [{} for _ in first]
    for a, row in enumerate(first):
        for b, f in row.items():
            for c, g in second[b].items():
                xor_entry(result[a], c, alg.compose(source_mid[a], middle_mid[b], target_mid[c], f, g))
    return result


def matrix_add(*matrices):
    result = [{} for _ in matrices[0]]
    for matrix in matrices:
        for a, row in enumerate(matrix):
            for b, value in row.items():
                xor_entry(result[a], b, value)
    return result


def check_certificate(scan, result):
    """Check all special contraction identities in the actual cobordism ring."""
    alg, old, new = scan.algebra, scan.mid, result['mid']
    differential = [row or {} for row in scan.out]
    reduced = result['out']
    inc, proj, hom = result['inclusion'], result['projection'], result['homotopy']
    comp = lambda a,b,c,f,g: matrix_compose(alg,a,b,c,f,g)
    old_identity = [{a: 1} if matching is not None else {} for a, matching in enumerate(old)]
    new_identity = [{a: 1} for a in range(len(new))]
    checks = {
        'dI=ID': (comp(new,old,old,inc,differential), comp(new,new,old,reduced,inc)),
        'Pd=DP': (comp(old,old,new,differential,proj), comp(old,new,new,proj,reduced)),
        'PI=1': (comp(new,old,new,inc,proj), new_identity),
        'dH+Hd=1+IP': (matrix_add(comp(old,old,old,differential,hom),
                                     comp(old,old,old,hom,differential)),
                             matrix_add(old_identity,comp(old,new,old,proj,inc))),
        'H^2=0': (comp(old,old,old,hom,hom), [{} for _ in old]),
        'HI=0': (comp(new,old,old,inc,hom), [{} for _ in new]),
        'PH=0': (comp(old,old,new,hom,proj), [{} for _ in old]),
        'D^2=0': (comp(new,new,new,reduced,reduced), [{} for _ in new]),
    }
    for name, (left, right) in checks.items():
        if left != right:
            raise ArithmeticError(f"contraction identity failed: {name}")
    return tuple(checks)


class GradedTransferScan(FastScan):
    """Opt-in scanning prototype; no implicit recognition-filter changes."""
    def __init__(self, *args, certificates=False, transfer_minimum=0, **kwargs):
        super().__init__(*args, **kwargs)
        self.qshift = [0]
        self.certificates = certificates
        self.transfer_minimum = transfer_minimum
        self.stats.update(graded_transfer_stages=0, graded_transfer_radical_edges=0,
                          graded_transfer_compositions=0, graded_transfer_coefficient_xors=0,
                          graded_transfer_peak_survivors=0)
        self.history = []

    def add_crossing(self, slots, reduce_now=True):
        old_mid, old_q = self.mid, self.qshift
        super().add_crossing(slots, reduce_now=False)
        self.qshift = [old_q[a] + smoothing + circles - 2 * label.bit_count()
                       for a, matching in enumerate(old_mid) if matching is not None
                       for smoothing in (0, 1)
                       for circles in (self.algebra.glue(matching, smoothing)[1],)
                       for label in range(1 << circles)]
        if reduce_now:
            self.eliminate()
            self.stats['max_objects_after_elimination'] = max(
                self.stats['max_objects_after_elimination'], self.live)

    def eliminate(self):
        if self.live < self.transfer_minimum:
            return super().eliminate()
        before = self.live
        result = transfer(self, certificates=self.certificates)
        if self.certificates:
            check_certificate(self, result)
        self.mid, self.deg, self.qshift, self.out = (
            result['mid'], result['deg'], result['q'], result['out'])
        self.live = len(self.mid)
        self.inc = [set() for _ in self.mid]
        for a, row in enumerate(self.out):
            for b in row:
                self.inc[b].add(a)
        self.composed = {}
        stats = self.stats
        stats['eliminations'] += (before - self.live) // 2
        stats['graded_transfer_stages'] += 1
        stats['graded_transfer_radical_edges'] += result['radical_edges']
        stats['graded_transfer_compositions'] += result['compositions']
        stats['graded_transfer_coefficient_xors'] += result['coefficient_xors']
        stats['graded_transfer_peak_survivors'] = max(stats['graded_transfer_peak_survivors'], self.live)
        self.history.append(dict(before=before, survivors=self.live,
                                 radical_edges=result['radical_edges'],
                                 compositions=result['compositions'],
                                 coefficient_xors=result['coefficient_xors']))


class GradedAdaptiveScan(GradedTransferScan):
    """Use the existing sparse-work allowance before the general transfer.

    Completed sparse cancellations are retained. The fallback computes the
    surviving radical maps even when the earlier degree-gap shortcut cannot
    apply. This remains a cost heuristic, without a competitive-time claim.
    """
    def eliminate(self):
        if FastScan.eliminate(self, update_budget=max(256, 4 * self.live)):
            return
        GradedTransferScan.eliminate(self)
