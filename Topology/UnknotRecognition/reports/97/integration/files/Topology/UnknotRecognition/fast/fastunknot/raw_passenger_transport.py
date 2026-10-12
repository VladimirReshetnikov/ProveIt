"""Transport one exact unsigned row through source column-leaf cancellation.

This is an algebra-only operation on an authenticated occurrence matrix.
It does not recover geometric markings, cyclic order, signs, or an embedding.
Donor counts must be the original, uncapped nonnegative integers: replacing
them by zero/one/at-least-two data can preserve a cancellation decision while
changing the transported row.
"""

from .column_cancellation_verify import verify_column_cancellations


def transport_raw_passenger(counts, cancellations, passenger, *, check=lambda: None):
    """Return the sparse surviving row after a complete source-leaf schedule.

    ``counts`` maps nonnegative integer donor row IDs to dictionaries mapping
    nonnegative integer column IDs to exact nonnegative integer counts.
    ``cancellations`` is a complete list of ``[row, column]`` source column
    leaves. ``passenger`` is an extra row in the same column space; columns
    appearing only in this row are permitted and survive unchanged.

    The independent timestamp checker validates the donor schedule. At a
    pivot ``(r, g)``, the extra row changes by

        passenger[h] += passenger[g] * counts[r][h]    (h != g),

    and column ``g`` disappears. Every donor row is read only once during
    transport; no donor matrix fill is constructed. There are at most as
    many arithmetic updates as nonzero off-pivot source incidences.

    Inputs are not mutated. Explicit zero coefficients are omitted from the
    result. Malformed data or a non-complete/non-leaf schedule raises
    ``ValueError``. Exceptions raised by ``check`` propagate unchanged.
    """
    check()
    if type(passenger) is not dict:
        raise ValueError('passenger must be an exact nonnegative count dictionary')
    result = {}
    for column, value in passenger.items():
        check()
        if (type(column) is not int or column < 0 or
                type(value) is not int or value < 0):
            raise ValueError('passenger keys and values must be nonnegative integers')
        if value:
            result[column] = value
    if not verify_column_cancellations(counts, cancellations, check=check):
        raise ValueError('invalid complete source column-leaf cancellation schedule')

    for row, pivot in cancellations:
        check()
        coefficient = result.pop(pivot, 0)
        if not coefficient:
            continue
        for column, multiplicity in counts[row].items():
            check()
            if column != pivot and multiplicity:
                result[column] = result.get(column, 0) + coefficient * multiplicity
    check()
    return result
