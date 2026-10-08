"""Exact full Jones polynomial from a two-state planar tensor network.

The combinatorial rotation cochain is part of the calculation, not optional
framing data.  Each bounded face has four quarter turns and the distinguished
outer face has minus four.  This forces every smoothed circle to have turning
number +1 or -1, so its two orientations contribute z**4 + z**-4.

Substitute A=i*z**2 and factor i once per crossing.  The two smoothing
weights then become z**2 and -z**-2; all arithmetic stays in Z[z,z**-1].
For writhe w and n crossings, V(z**-8) is
(-1)**((n-w)//2) * z**(-6*w) * F(z)/(z**4+z**-4).

At crossing frontier w there are at most 2**w binary spin keys.  Laurent
degrees and coefficient bit lengths are polynomial in the input.  Together
with the maintained certified separator order this gives exact full Jones
computation in poly(n)*2**O(sqrt(n)).  Polynomial identity is still not an
unknot certificate.  Resource failures never publish a partial polynomial.
"""
from __future__ import annotations

from .filters import FilterLimit
from .ordering import best_scan_order, validate_order


class TensorLimit(FilterLimit):
    """Local exhaustion with counters, never a partially computed invariant."""

    def __init__(self, message, *, transitions=0, peak_states=0,
                 completed_crossings=0):
        super().__init__(message)
        self.transitions = transitions
        self.peak_states = peak_states
        self.completed_crossings = completed_crossings


def _budget(value, name):
    if value is not None and (type(value) is not int or value < 0):
        raise ValueError(name + " must be a nonnegative integer or None")


def rotation_cochain(diagram, *, outer_face=0, check=lambda: None):
    """Return checked integer dart bends from a dual spanning tree.

    Face walks use rho(alpha(d)).  Their local corner contribution is +1.
    Therefore sum(beta[d] for d in face) must be 4-len(face), except for
    -4-len(face) at the chosen outer face.  All other dual edges receive zero.
    Antisymmetry and every face equation are checked independently afterwards.
    The contract is a validated classical one-component Diagram.
    """
    check()
    n = diagram.crossings
    if type(outer_face) is not int or outer_face < 0:
        raise ValueError("outer_face must be a nonnegative integer")
    if not n:
        if outer_face:
            raise ValueError("the crossing-free case has only outer face zero")
        return ()
    alpha, faces = diagram.alpha(), diagram.faces()
    if outer_face >= len(faces):
        raise ValueError("outer_face is outside the face list")
    if len(faces) != n + 2:
        raise ValueError("the rotation cochain requires a connected spherical projection")
    dart_face = [-1] * (4*n)
    for f, face in enumerate(faces):
        check()
        for dart in face:
            dart_face[dart] = f
    dual = [[] for _ in faces]
    for dart, other in enumerate(alpha):
        if dart < other:
            check()
            f, g = dart_face[dart], dart_face[other]
            if f != g:
                dual[f].append((g, dart))
                dual[g].append((f, other))
    parent = {outer_face: None}
    parent_dart, queue = {}, [outer_face]
    for f in queue:
        check()
        for g, dart in dual[f]:
            if g not in parent:
                parent[g] = f
                parent_dart[g] = alpha[dart]  # dart on the child's face
                queue.append(g)
    if len(queue) != len(faces):
        raise ValueError("the face dual is disconnected")
    demand = [4-len(face) for face in faces]
    demand[outer_face] -= 8
    if sum(demand):
        raise ArithmeticError("the planar face rotation demands do not balance")
    beta = [0] * (4*n)
    for f in reversed(queue[1:]):
        check()
        dart = parent_dart[f]
        beta[dart], beta[alpha[dart]] = demand[f], -demand[f]
        demand[parent[f]] += demand[f]
    if demand[outer_face]:
        raise ArithmeticError("dual-tree rotation routing did not close")
    for dart, other in enumerate(alpha):
        if beta[dart] != -beta[other]:
            raise ArithmeticError("dart rotation antisymmetry failed")
    for f, face in enumerate(faces):
        check()
        expected = -4 if f == outer_face else 4
        if len(face) + sum(beta[d] for d in face) != expected:
            raise ArithmeticError("a routed face rotation equation failed")
    return tuple(beta)


def _local_tensor(vertex, alpha, beta):
    """At most six binary dart patterns, with one or two Laurent monomials."""
    base, entries = 4*vertex, []
    for mask in range(16):
        if mask.bit_count() != 2:
            continue
        spin = tuple(1 if mask & (1 << j) else -1 for j in range(4))
        if any(alpha[base+j]//4 == vertex
               and spin[j] != -spin[alpha[base+j] % 4] for j in range(4)):
            continue
        edge_turn = sum(spin[j]*beta[base+j] for j in range(4)
                        if base+j < alpha[base+j])
        polynomial = {}
        for smoothing, pairs in enumerate((((0, 1), (2, 3)),
                                            ((0, 3), (1, 2)))):
            if any(spin[a] != -spin[b] for a, b in pairs):
                continue
            corner_turn = sum(-spin[a] * (1 if (b-a) % 4 == 1 else -1)
                              for a, b in pairs)
            exponent = 2-4*smoothing + edge_turn + corner_turn
            polynomial[exponent] = polynomial.get(exponent, 0) + (1-2*smoothing)
        polynomial = tuple((e, c) for e, c in polynomial.items() if c)
        if polynomial:
            entries.append((mask, polynomial))
    return tuple(entries)


def _divide_loop(polynomial, check):
    """Exact Laurent division by z**4+z**-4 with a checked zero remainder."""
    if not polynomial:
        return {}
    # Multiply numerator and denominator by z**4, then shift only the
    # numerator by its least exponent to use ordinary monic long division.
    least = min(polynomial) + 4
    remainder = {e+4-least: c for e, c in polynomial.items()}
    quotient = {}
    while remainder:
        check()
        degree = max(remainder)
        if degree < 8:
            raise ArithmeticError("tensor bracket is not divisible by the loop polynomial")
        coefficient = remainder.pop(degree)
        qdegree = degree-8
        quotient[qdegree+least] = coefficient
        value = remainder.get(qdegree, 0)-coefficient
        if value:
            remainder[qdegree] = value
        else:
            remainder.pop(qdegree, None)
    return quotient


def _decode_integer(value, *, crossings, writhe, laurent_shift, encoding_bits, check):
    """Recover Jones coefficients from one exact integer tensor contraction.

    z=2**encoding_bits, x=z**8 >= 4*4**n.  ``value`` equals z**(-g)*F(z),
    where g=laurent_shift is the sum of the per-vertex least exponents.
    Consequently x**(2*n)*V(x**-1) is
       sign*z**(16*n+4-6*w+g)*value/(z**8+1).
    Negative powers are moved into the denominator before exact division.
    Only the final normalized polynomial needs faithful base-x encoding;
    intermediate table values may coincide or vanish at this specialization.
    """
    n, w, k = crossings, writhe, encoding_bits
    check()
    if k < 1 or 8*k < 2*n+2:
        raise ValueError("the tensor integer encoding base is too small")
    if (n-w) % 2:
        raise ArithmeticError("crossing count and writhe have incompatible parity")
    sign = -1 if ((n-w)//2) % 2 else 1
    base = 1 << (8*k)
    # This comparison is a whole-polynomial identity test by the coefficient
    # bound.  It avoids normalization division and decoding for the identity.
    identity_exponent = 6*w-4-laurent_shift
    if identity_exponent >= 0 and value == sign*((base+1) << (k*identity_exponent)):
        check()
        return {0: 1}, True
    exponent = 16*n+4-6*w+laurent_shift
    numerator, denominator = sign*value, base+1
    if exponent >= 0:
        numerator <<= k*exponent
    else:
        denominator <<= -k*exponent
    check()
    encoded, remainder = divmod(numerator, denominator)
    if remainder:
        raise ArithmeticError("tensor integer Jones normalization is not exact")
    answer, degree = {}, 0
    half, mask = base >> 1, base-1
    while encoded:
        check()
        if degree > 4*n:
            raise ArithmeticError("decoded Jones polynomial exceeds its degree bound")
        digit = encoded & mask
        if digit >= half:
            digit -= base
        if digit:
            answer[2*n-degree] = digit
        encoded = (encoded-digit) >> (8*k)
        degree += 1
    return answer, False


def _add_valuations(left, right, encoding_bits):
    """Add normalized exact pairs z**v*m, where z=2**encoding_bits.

    A nonzero mantissa is not divisible by z.  Zero is represented by None.
    Normalizing after every addition removes monomial padding exactly, even
    when specialized coefficients acquire additional factors of z by carries.
    The representation is of the evaluated rational number, not its formal
    Laurent polynomial; intermediate faithfulness is unnecessary.
    """
    if left is None:
        return right
    if right is None:
        return left
    lv, lm = left
    rv, rm = right
    if lv < rv:
        exponent, mantissa = lv, lm+(rm << (encoding_bits*(rv-lv)))
    else:
        exponent, mantissa = rv, rm+(lm << (encoding_bits*(lv-rv)))
    if not mantissa:
        return None
    magnitude = abs(mantissa)
    zero_bits = (magnitude & -magnitude).bit_length()-1
    shift = zero_bits//encoding_bits
    return exponent+shift, mantissa >> (encoding_bits*shift)


def tensor_jones(diagram, *, order=None, certified=True, outer_face=0,
                 arithmetic="laurent",
                 max_states=None, max_transitions=None, check=lambda: None,
                 statistics=None):
    """Compute the full normalized Jones polynomial of a validated knot.

    ``certified=True`` constructs and verifies the existing separator witness
    and compares it with a supplied/greedy order; this is the default and the
    scope of the universal sqrt(n) bound.  With ``certified=False``, the exact
    supplied/greedy order is used without a universal width promise.

    ``arithmetic="laurent"`` keeps exact sparse Laurent coefficient tables.
    ``arithmetic="integer"`` evaluates at a coefficient-bounded power of two,
    uses valuation-normalized signed integer shifts, then recovers all Jones
    coefficients exactly. ``arithmetic="integer-global"`` retains a simpler
    global shift as an arithmetic ablation; it can retain large monomial pads.
    All modes have the same output contract and frontier bound.

    Limits count represented nonzero spin keys and completed compatible local
    tensor transitions.  Deadline checks additionally occur in coefficient
    loops.  Neither limit is a byte-memory budget.  ``statistics`` is updated
    only after the full polynomial and its normalization checks are complete.
    """
    _budget(max_states, "max_states")
    _budget(max_transitions, "max_transitions")
    if type(certified) is not bool:
        raise ValueError("certified must be Boolean")
    if arithmetic not in ("laurent", "integer", "integer-global"):
        raise ValueError("arithmetic must be laurent, integer or integer-global")
    check()
    n = diagram.crossings
    if order is not None:
        order = validate_order(n, order)
    if n and (max_states == 0 or max_transitions == 0):
        raise TensorLimit("tensor Jones budget is zero")
    beta = rotation_cochain(diagram, outer_face=outer_face, check=check)
    certificate = None
    if n and certified:
        from .separator_order import width_bounded_scan_order, verify_width_bounded_order
        prepared = width_bounded_scan_order(diagram.pd, order=order, check=check)
        if not verify_width_bounded_order(diagram.pd, prepared, check=check):
            raise ArithmeticError("tensor Jones separator certificate failed verification")
        order, certificate = prepared["order"], prepared
    elif order is None:
        order = (best_scan_order(diagram.pd, tries=min(n, 12), check=check)
                 if n else [])
    alpha = diagram.alpha() if n else ()
    integer_mode = arithmetic != "laurent"
    valuation_mode = arithmetic == "integer"
    encoding_bits = max(1, (2*n+9)//8)
    laurent_shift = 0
    states = {0: (0, 1)} if valuation_mode else ({0: 1} if integer_mode else {0: {0: 1}})
    active = []
    peak, transitions, max_boundary = 1, 0, 0
    peak_terms, max_terms, coefficient_bits, exponent_abs = 1, 1, 1, 0
    valuation_abs = 0
    for position, vertex in enumerate(order):
        check()
        base = 4*vertex
        incident = {min(base+j, alpha[base+j]) for j in range(4)}
        loops = {edge for edge in incident if edge//4 == alpha[edge]//4}
        active_positions = {edge: j for j, edge in enumerate(active)}
        touched = incident & active_positions.keys()
        surviving = tuple(j for j, edge in enumerate(active) if edge not in touched)
        new_edges = sorted(incident-touched-loops)
        new_positions = {edge: j for j, edge in enumerate(new_edges)}
        after = [active[j] for j in surviving] + new_edges
        options = []
        local = _local_tensor(vertex, alpha, beta)
        least = min((e for _, polynomial in local for e, _ in polynomial), default=0)
        if integer_mode and not valuation_mode:
            laurent_shift += least
        for mask, polynomial in local:
            required_mask = required_value = born = 0
            for j in range(4):
                dart, bit = base+j, (mask >> j) & 1
                edge = min(dart, alpha[dart])
                if edge in loops:
                    continue
                canonical_bit = bit if dart == edge else 1-bit
                if edge in active_positions:
                    k = active_positions[edge]
                    required_mask |= 1 << k
                    required_value |= canonical_bit << k
                else:
                    born |= canonical_bit << new_positions[edge]
            encoded_polynomial = (tuple(((e-least)*encoding_bits, c) for e, c in polynomial)
                                  if integer_mode and not valuation_mode else polynomial)
            options.append((required_mask, required_value, born, encoded_polynomial))
        following = {}
        for state, coefficient in states.items():
            check()
            retained = sum(((state >> old) & 1) << new
                           for new, old in enumerate(surviving))
            for required_mask, required_value, born, polynomial in options:
                if state & required_mask != required_value:
                    continue
                if max_transitions is not None and transitions >= max_transitions:
                    raise TensorLimit("tensor Jones transition budget exhausted",
                                      transitions=transitions, peak_states=peak,
                                      completed_crossings=position)
                transitions += 1
                target = retained | (born << len(surviving))
                if valuation_mode:
                    check()
                    output = following.get(target)
                    for shift, scalar in polynomial:
                        term = (coefficient[0]+shift, scalar*coefficient[1])
                        output = _add_valuations(output, term, encoding_bits)
                    if output is not None:
                        following[target] = output
                        coefficient_bits = max(coefficient_bits, abs(output[1]).bit_length())
                        valuation_abs = max(valuation_abs, abs(output[0]))
                    else:
                        following.pop(target, None)
                elif integer_mode:
                    check()
                    output = following.get(target, 0)
                    for shift, scalar in polynomial:
                        output += scalar*(coefficient << shift)
                    if output:
                        following[target] = output
                        coefficient_bits = max(coefficient_bits, abs(output).bit_length())
                    else:
                        following.pop(target, None)
                else:
                    output = following.setdefault(target, {})
                    for shift, scalar in polynomial:
                        for k, (exponent, value) in enumerate(coefficient.items()):
                            if not k & 255:
                                check()
                            destination = exponent+shift
                            result = output.get(destination, 0)+scalar*value
                            if result:
                                output[destination] = result
                            else:
                                output.pop(destination, None)
                    if not output:
                        following.pop(target, None)
                peak = max(peak, len(following))
                if max_states is not None and len(following) > max_states:
                    raise TensorLimit("tensor Jones frontier budget exhausted",
                                      transitions=transitions, peak_states=peak,
                                      completed_crossings=position)
        states, active = following, after
        max_boundary = max(max_boundary, len(active))
        if not integer_mode:
            term_count = 0
            for polynomial in states.values():
                check()
                term_count += len(polynomial)
                max_terms = max(max_terms, len(polynomial))
                for exponent, coefficient in polynomial.items():
                    exponent_abs = max(exponent_abs, abs(exponent))
                    coefficient_bits = max(coefficient_bits, abs(coefficient).bit_length())
            peak_terms = max(peak_terms, term_count)
    if active or any(states):
        raise ArithmeticError("tensor Jones contraction ended with an open frontier")
    writhe = diagram.writhe() if n else 0
    if (n-writhe) % 2:
        raise ArithmeticError("crossing count and writhe have incompatible parity")
    identity_shortcut = False
    if n and integer_mode:
        if valuation_mode:
            laurent_shift, scalar_value = states.get(0, (0, 0))
        else:
            scalar_value = states.get(0, 0)
        answer, identity_shortcut = _decode_integer(scalar_value, crossings=n,
                 writhe=writhe, laurent_shift=laurent_shift,
                 encoding_bits=encoding_bits, check=check)
    elif n:
        normalized = _divide_loop(states.get(0, {}), check)
        sign = -1 if ((n-writhe)//2) % 2 else 1
        answer = {}
        for exponent, coefficient in normalized.items():
            check()
            exponent -= 6*writhe
            if exponent % 8:
                raise ArithmeticError("a normalized knot Jones exponent is not integral")
            answer[-exponent//8] = sign*coefficient
    else:
        answer = {0: 1}
    if not answer or sum(answer.values()) != 1:
        raise ArithmeticError("normalized knot Jones evaluation at one is not one")
    if any(abs(e) > 2*n for e in answer) or sum(map(abs, answer.values())) > 4**n:
        raise ArithmeticError("normalized Jones degree or coefficient bound failed")
    check()
    result = dict(algorithm="binary-rotation-tensor-v1", crossing_count=n,
                  arithmetic=arithmetic,
                  writhe=writhe, outer_face=outer_face, certified=certified,
                  order=list(order), max_boundary=max_boundary,
                  peak_states=peak, transitions=transitions,
                  max_polynomial_terms=None if integer_mode else max_terms,
                  peak_polynomial_terms=None if integer_mode else peak_terms,
                  max_coefficient_bits=coefficient_bits,
                  max_abs_intermediate_exponent=None if integer_mode else exponent_abs,
                  rotation_l1=sum(abs(beta[d]) for d in range(len(beta))
                                  if d < alpha[d]),
                  differs=answer != {0: 1},
                  polynomial_identity=dict(algorithm="binary-rotation-tensor-v1",
                                           crossing_count=n, is_one=answer == {0: 1}),
                  jones_polynomial=dict(variable="t", coefficients_hex=[
                      [e, hex(c)] for e, c in sorted(answer.items())]))
    if integer_mode:
        result["integer_encoding"] = dict(z_bits=encoding_bits, x_bits=8*encoding_bits,
                                           laurent_shift=laurent_shift,
                                           identity_shortcut=identity_shortcut,
                                           mode="valuation" if valuation_mode else "global-shift")
        if valuation_mode:
            result["integer_encoding"]["max_abs_valuation"] = valuation_abs
    if certificate is not None:
        result["order_certificate"] = certificate
    if statistics is not None:
        statistics.update(result)
    return result


def tensor_jones_obstruction(diagram, **options):
    """A full-polynomial nontriviality witness, or inconclusive on identity.

    A completed identity result remains available through ``statistics`` for
    the recognizer's independent fallback.  Jones identity is never promoted
    to an unknot verdict.
    """
    result = tensor_jones(diagram, **options)
    if not result["differs"]:
        return None
    return dict(kind="tensor-jones-polynomial-nontrivial", **result)
