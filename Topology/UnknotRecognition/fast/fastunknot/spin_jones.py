"""Exact Jones computation with two orientations per frontier edge.

A certified integral turning cochain replaces a geometric plane drawing.
Orienting each smoothing circle gives weights t^4+t^-4=-A^2-A^-2,
where A=B^2, t=z*B, z^4=-1.  The tensor contraction therefore needs
at most 2^w states at an arbitrary w-edge frontier, with no disk promise.
An input-sized power-of-two B makes the scalar evaluation faithful and
allows full Laurent recovery.  Certified separators give the uncapped
general bit bound 2^O(sqrt(n)); polynomial factors are absorbed.  Polynomial one is inconclusive
for unknot recognition.
"""
from collections import Counter, defaultdict

from .diagram import Diagram
from .filters import FilterLimit
from .geometry import SMOOTHINGS
from .ordering import best_scan_order, order_profile, validate_order
from .potts import _budget
from .separator_order import width_bounded_scan_order


class SpinLimit(FilterLimit):
    """Local work exhaustion, without an unfinished invariant value."""

    def __init__(self, message, *, transitions=0, peak_states=0,
                 completed_crossings=0):
        super().__init__(message)
        self.transitions = transitions
        self.peak_states = peak_states
        self.completed_crossings = completed_crossings


def faithful_base_log(crossings):
    """log2(B), with B^8 >= 4*4^n, for both identity and recovery."""
    if type(crossings) is not int or crossings < 0:
        raise ValueError('crossings must be a nonnegative integer')
    return (2*crossings+9)//8


def turn_certificate(diagram, *, outer_face=0, check=lambda: None):
    """Build integral directed edge turns from a dual spanning tree.

    For phi=sigma*alpha each face corner turns -1.  Thus sum b_d=|f|-4
    for a bounded face and |f|+4 for the selected outer face; b_alpha(d)
    equals -b_d.  The returned cochain uses O(n) records of O(log n) bits.
    """
    check()
    faces, alpha = diagram.faces(), diagram.alpha()
    if type(outer_face) is not int or not 0 <= outer_face < max(1, len(faces)):
        raise ValueError('outer_face must identify a face')
    if not alpha:
        return dict(algorithm='integral-turn-cochain-v1', crossing_count=0,
                    outer_face=0, dart_turns=[])
    where = [0]*len(alpha)
    for face, darts in enumerate(faces):
        check()
        for dart in darts:
            where[dart] = face
    parent = [-1]*len(faces)
    parent_dart = [-1]*len(faces)
    parent[outer_face] = outer_face
    visit = [outer_face]
    for face in visit:
        check()
        for dart in faces[face]:
            other = where[alpha[dart]]
            if parent[other] == -1:
                parent[other] = face
                parent_dart[other] = alpha[dart]
                visit.append(other)
    if len(visit) != len(faces):
        raise ArithmeticError('turning construction requires a connected dual')
    demand = [len(face)-4 for face in faces]
    demand[outer_face] += 8
    turns = [0]*len(alpha)
    for face in reversed(visit[1:]):
        check()
        dart = parent_dart[face]
        turns[dart], turns[alpha[dart]] = demand[face], -demand[face]
        demand[parent[face]] += demand[face]
    if demand[outer_face]:
        raise ArithmeticError('spherical turning demands do not balance')
    certificate = dict(algorithm='integral-turn-cochain-v1',
                       crossing_count=diagram.crossings,
                       outer_face=outer_face, dart_turns=turns)
    if not verify_turn_certificate(diagram.pd, certificate, check=check):
        raise ArithmeticError('constructed turning certificate failed verification')
    return certificate


def verify_turn_certificate(pd, certificate, *, check=lambda: None):
    """Check face equations directly, independently of the dual-tree solver.

    Malformed certificates return False.  A caller's cancellation exception
    propagates.  The PD is independently validated as a classical knot.
    """
    check()
    try:
        diagram = Diagram.from_pd(pd)
    except (TypeError, ValueError):
        return False
    if not isinstance(certificate, dict):
        return False
    if (certificate.get('algorithm') != 'integral-turn-cochain-v1'
            or type(certificate.get('crossing_count')) is not int
            or certificate['crossing_count'] != diagram.crossings):
        return False
    turns = certificate.get('dart_turns')
    outer = certificate.get('outer_face')
    faces, alpha = diagram.faces(), diagram.alpha()
    if (not isinstance(turns, (list, tuple)) or len(turns) != len(alpha)
            or any(type(value) is not int for value in turns)
            or type(outer) is not int or not 0 <= outer < max(1, len(faces))):
        return False
    for dart, other in enumerate(alpha):
        if not dart & 1023:
            check()
        if turns[dart] != -turns[other]:
            return False
    for index, face in enumerate(faces):
        check()
        if sum(turns[dart] for dart in face) != len(face)-4+8*(index == outer):
            return False
    check()
    return True


def _crossing_table(diagram, crossing, old, new, turns, base_log):
    """Sparse two-spin tensor, summing orientations of self-loop edges.

    All monomials for fixed boundary arrows have one z-coordinate.  Their
    integer coefficients use (binary shift, signed multiplicity) records.
    Multiplication uses shifts and additions only, never large products.
    """
    row = diagram.pd[crossing]
    labels = tuple(sorted(set(row)))
    alpha = diagram.alpha()
    base = 4*crossing
    assigned = [(slot, turns[base+slot]) for slot in range(4)
                if base+slot < alpha[base+slot]]
    edge_shift = sum(abs(turn) for _, turn in assigned)
    collected = defaultdict(Counter)
    for bits in range(1 << len(labels)):
        arrow = {label: (bits >> i) & 1 for i, label in enumerate(labels)}
        outgoing = [arrow[row[slot]] if base+slot < alpha[base+slot]
                    else 1-arrow[row[slot]] for slot in range(4)]
        if sum(outgoing) != 2:
            continue
        old_key = sum(arrow[label] << i for i, label in enumerate(old))
        new_key = sum(arrow[label] << i for i, label in enumerate(new))
        edge_turn = sum((2*outgoing[slot]-1)*turn for slot, turn in assigned)
        for smoothing, pairs in enumerate(SMOOTHINGS):
            if any(outgoing[a] == outgoing[b] for a, b in pairs):
                continue
            local_turn = 0
            for a, b in pairs:
                incoming, leaving = (b, a) if outgoing[a] else (a, b)
                local_turn += -1 if (leaving-incoming) % 4 == 1 else 1
            exponent = 4+2*(1-2*smoothing)+local_turn+edge_shift+edge_turn
            if exponent < 0:
                raise ArithmeticError('negative shifted tensor exponent')
            phase = (local_turn+edge_turn) % 8
            collected[old_key, new_key][phase % 4, base_log*exponent] += (
                1 if phase < 4 else -1)
    table = defaultdict(list)
    for (old_key, new_key), raw in sorted(collected.items()):
        nonzero = [(phase, shift, count) for (phase, shift), count in sorted(raw.items())
                   if count]
        if nonzero:
            phases = {phase for phase, _, _ in nonzero}
            if len(phases) != 1:
                raise ArithmeticError('tensor boundary arrows have inconsistent phases')
            terms = tuple((shift, count) for _, shift, count in nonzero)
            table[old_key].append((new_key, (nonzero[0][0], terms)))
    return table


def _multiply_terms(coefficient, terms):
    phase, value = coefficient
    tensor_phase, monomials = terms
    phase += tensor_phase
    answer = sum((value << shift)*multiplier for shift, multiplier in monomials)
    return phase % 4, answer if phase < 4 else -answer


def _normalize_valuation(shift, value):
    """Exact integer 2**shift * value, with an odd signed mantissa (or zero).

    Normalize binary factors, including those introduced by signed carries;
    this is a representation of the evaluated integer, not formal monomials.
    """
    if not value:
        return 0, 0
    magnitude = abs(value)
    trailing = (magnitude & -magnitude).bit_length()-1
    return shift+trailing, value >> trailing


def _add_valuations(left, right):
    ls, lv = left
    rs, rv = right
    if not lv:
        return right
    if not rv:
        return left
    if ls < rs:
        return _normalize_valuation(ls, lv+(rv << (rs-ls)))
    return _normalize_valuation(rs, rv+(lv << (ls-rs)))


def _valuation_terms(terms):
    phase, monomials = terms
    least = min(shift for shift, _ in monomials)
    return phase, least, tuple((shift-least, value) for shift, value in monomials)


def _multiply_valuation(coefficient, terms):
    phase, shift, value = coefficient
    tensor_phase, least, monomials = terms
    phase += tensor_phase
    answer = sum((value << offset)*multiplier for offset, multiplier in monomials)
    shift, answer = _normalize_valuation(shift+least, answer)
    return phase % 4, shift, answer if phase < 4 else -answer


def _gather(value, positions):
    return sum(((value >> position) & 1) << i for i, position in enumerate(positions))


def reconstruct_spin_jones(result, *, check=lambda: None):
    """Recover a completed faithful scalar, checking its normalization first.

    This is a decoder, not an independent verification of the state sum.
    The supplied normalization must equal the exact value prescribed by n,
    writhe, scaling and base, including before the identity shortcut.
    """
    check()
    n = result['crossing_count']
    base_log = result['base_log2']
    if type(base_log) is not int or base_log != faithful_base_log(n):
        raise ValueError('reconstruction requires the faithful input-sized base')
    scalar, expected = result['scaled_bracket'], result['unknot_scaled_bracket']
    writhe, shift = result['writhe'], result['bracket_shift']
    if (type(scalar) is not int or type(expected) is not int
            or type(writhe) is not int or abs(writhe) > n or (writhe-n) % 2
            or type(shift) is not int or shift < 6*n+4):
        raise ValueError('invalid completed turn-spin scalar metadata')
    check()
    # The required absolute value is (2^(8*base_log)+1)*2^normalization_shift.
    # Its two set bits characterize it exactly. Check the length first, so a
    # forged enormous shift cannot trigger an enormous allocation from a small
    # supplied integer. This avoids rebuilding a large normalization integer.
    normalization_shift = base_log*(shift+6*writhe-4)
    absolute = abs(expected)
    negative = bool((writhe+1) % 2)
    if (not expected or (expected < 0) != negative
            or absolute.bit_length() != normalization_shift+8*base_log+1
            or absolute.bit_count() != 2
            or absolute >> normalization_shift != (1 << (8*base_log))+1):
        raise ArithmeticError('inconsistent Jones normalization')
    check()
    if scalar == expected:
        return {0: 1}
    exponent = 16*n+4-shift-6*writhe
    numerator = -scalar if (writhe+1) % 2 else scalar
    denominator = (1 << (8*base_log))+1
    if exponent >= 0:
        numerator <<= base_log*exponent
    else:
        denominator <<= -base_log*exponent
    encoded, remainder = divmod(numerator, denominator)
    if remainder:
        raise ArithmeticError('normalized Jones encoding is not integral')
    base = 1 << (8*base_log)
    polynomial = {}
    position = 0
    while encoded:
        check()
        if position > 4*n:
            raise ArithmeticError('Jones polynomial exceeds its degree bound')
        digit = encoded % base
        if digit >= base//2:
            digit -= base
        if digit:
            polynomial[2*n-position] = digit
        encoded = (encoded-digit)//base
        position += 1
    if (sum(map(abs, polynomial.values())) > 1 << (2*n)
            or (polynomial == {0: 1}) != (scalar == expected)):
        raise ArithmeticError('Jones recovery violates its certified bounds')
    check()
    return dict(sorted(polynomial.items()))


def spin_jones_exact(diagram, *, max_states=4096, max_transitions=200_000,
                     order=None, check=lambda: None, statistics=None,
                     include_polynomial=False, certify_order=True, outer_face=0,
                     arithmetic='valuation'):
    """Faithful identity/full-Jones query with two states per frontier edge.

    The default certifies the existing square-root-width separator order.
    ``certify_order=False`` is useful for fixed-order comparisons and has
    the stated poly(n)*2^O(w) deterministic bit bound for its actual maximum
    frontier w.  A collision-free table gives poly(n)*2^w; ordinary Python
    dictionaries retain the wider deterministic envelope even under collisions.
    Valuation arithmetic factors powers of two from each exact coefficient;
    ``arithmetic='shifted'`` retains the original dense-integer arithmetic.
    Returned scalars and decoding conventions are identical in both modes.
    """
    _budget(max_states, 'max_states')
    _budget(max_transitions, 'max_transitions')
    if type(include_polynomial) is not bool or type(certify_order) is not bool:
        raise ValueError('include_polynomial and certify_order must be boolean')
    if arithmetic not in ('valuation', 'shifted'):
        raise ValueError('arithmetic must be valuation or shifted')
    valued = arithmetic == 'valuation'
    check()
    n = diagram.crossings
    if order is not None:
        order = validate_order(n, order)
    if type(outer_face) is not int or not 0 <= outer_face < max(1, n+2 if n else 0):
        raise ValueError('outer_face must identify a face')
    if n and (max_states == 0 or max_transitions == 0):
        raise SpinLimit('turn-spin Jones filter budget is zero')
    order_certificate = None
    if certify_order:
        if order is not None and n:
            greedy = best_scan_order(diagram.pd, tries=min(n, 12), check=check)
            order = min((order, greedy), key=lambda candidate: order_profile(diagram.pd, candidate))
        order_certificate = width_bounded_scan_order(diagram.pd, order=order, check=check)
        order = order_certificate['order']
        if statistics is not None:
            statistics['order_certificate'] = order_certificate
    elif order is None:
        order = best_scan_order(diagram.pd, tries=max(1, min(n, 12)), check=check)
    certificate = turn_certificate(diagram, outer_face=outer_face, check=check)
    turns = certificate['dart_turns']
    base_log = faithful_base_log(n)
    cochain_l1 = sum(map(abs, turns))//2
    tensor_shift = 4*n+cochain_l1
    bracket_shift = max(tensor_shift, 6*n+4)
    states, active = {0: (0, 0, 1) if valued else (0, 1)}, []
    peak, transitions, max_boundary, coefficient_bits = 1, 0, 0, 1
    mantissa_bits, max_valuation = 1, 0
    for position, crossing in enumerate(order):
        check()
        row = diagram.pd[crossing]
        local = set(row)
        old = tuple(label for label in active if label in local)
        keep = tuple(i for i, label in enumerate(active) if label not in local)
        positions = tuple(active.index(label) for label in old)
        new = tuple(sorted(label for label, count in Counter(row).items()
                           if count == 1 and label not in active))
        following_active = [active[i] for i in keep]+list(new)
        table = _crossing_table(diagram, crossing, old, new, turns, base_log)
        if valued:
            table = {key: [(target, _valuation_terms(terms)) for target, terms in entries]
                     for key, entries in table.items()}
        following = {}
        for state, coefficient in states.items():
            old_key = _gather(state, positions)
            kept = _gather(state, keep)
            for new_key, terms in table.get(old_key, ()):
                if max_transitions is not None and transitions >= max_transitions:
                    raise SpinLimit('turn-spin transition budget exhausted',
                                    transitions=transitions, peak_states=peak,
                                    completed_crossings=position)
                transitions += 1
                if not transitions & 255:
                    check()
                target = kept | (new_key << len(keep))
                if valued:
                    phase, shift, contribution = _multiply_valuation(coefficient, terms)
                    previous_phase, ps, previous = following.get(target, (phase, 0, 0))
                    if phase != previous_phase:
                        raise ArithmeticError('frontier arrows have inconsistent phases')
                    shift, value = _add_valuations((ps, previous), (shift, contribution))
                else:
                    phase, contribution = _multiply_terms(coefficient, terms)
                    previous_phase, previous = following.get(target, (phase, 0))
                    if phase != previous_phase:
                        raise ArithmeticError('frontier arrows have inconsistent phases')
                    shift, value = 0, previous+contribution
                if value:
                    following[target] = (phase, shift, value) if valued else (phase, value)
                    peak = max(peak, len(following))
                    bits = abs(value).bit_length()
                    coefficient_bits = max(coefficient_bits, bits+shift)
                    mantissa_bits = max(mantissa_bits, bits)
                    max_valuation = max(max_valuation, shift)
                else:
                    following.pop(target, None)
                if max_states is not None and len(following) > max_states:
                    raise SpinLimit('turn-spin frontier budget exhausted',
                                    transitions=transitions, peak_states=peak,
                                    completed_crossings=position)
        states, active = following, following_active
        max_boundary = max(max_boundary, len(active))
    if active or any(states):
        raise ArithmeticError('turn-spin scan ended with an open frontier')
    check()
    if valued:
        phase, shift, mantissa = states.get(0, (0, 0, 0))
        scalar = mantissa << shift
    else:
        phase, scalar = states.get(0, (0, 0))
    if phase:
        raise ArithmeticError('closed bracket has nonreal cyclotomic coordinates')
    if n:
        scalar <<= base_log*(bracket_shift-tensor_shift)
    else:
        # The empty PD represents one circle, rather than an empty diagram.
        scalar = -((1 << (8*base_log))+1)
    writhe = diagram.writhe()
    expected = ((1 << (8*base_log))+1) << (base_log*(bracket_shift+6*writhe-4))
    if (writhe+1) % 2:
        expected = -expected
    coefficient_bits = max(coefficient_bits, abs(scalar).bit_length(),
                           abs(expected).bit_length())
    result = dict(algorithm='integral-turn-spin-v1', ring='Z[z]/(z^4+1)',
                  arithmetic=arithmetic,
                  crossing_count=n, writhe=writhe, base_log2=base_log,
                  bracket_shift=bracket_shift, tensor_shift=tensor_shift,
                  cochain_l1=cochain_l1, scaled_bracket=scalar,
                  unknot_scaled_bracket=expected, differs=scalar != expected,
                  peak_states=peak, transitions=transitions, max_boundary=max_boundary,
                  max_coefficient_bits=coefficient_bits,
                  max_frontier_mantissa_bits=mantissa_bits,
                  max_frontier_valuation=max_valuation,
                  turn_certificate=certificate)
    if order_certificate is not None:
        result['order_certificate'] = order_certificate
    if include_polynomial:
        polynomial = reconstruct_spin_jones(result, check=check)
        result['jones_polynomial'] = dict(variable='t', coefficients_hex=[
            [degree, hex(value)] for degree, value in polynomial.items()])
    check()
    result['polynomial_identity'] = dict(algorithm='turn-spin-kronecker-v1',
        crossing_count=n, is_one=scalar == expected, coefficient_l1_bound_log2=2*n,
        encoding_base_log2=8*base_log, base_rule='B=2^ceil((2*n+2)/8), A=B^2')
    if statistics is not None:
        statistics.update(result)
    return result


def witness_from_spin(result, *, kind='turn-spin-jones-polynomial-nontrivial'):
    """JSON-safe exact obstruction, or None when polynomial identity is proved."""
    if result['scaled_bracket'] == result['unknot_scaled_bracket']:
        return None
    witness = dict(kind=kind, **result)
    witness['differs'] = True
    for name in ('scaled_bracket', 'unknot_scaled_bracket'):
        witness[name+'_hex'] = hex(witness.pop(name))
    return witness


def spin_jones_obstruction(diagram, **options):
    return witness_from_spin(spin_jones_exact(diagram, **options))
