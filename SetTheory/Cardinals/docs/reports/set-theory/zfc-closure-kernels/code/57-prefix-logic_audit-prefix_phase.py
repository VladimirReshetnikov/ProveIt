"""Uniform left-context premise for the prefix-right decrement excursion.

Left zipper segments are ordered from the register boundary towards the
left. Runs denote a*n+c bits for every n>=0. This checker proves that the
concrete left context starts with a nonempty run of ones and then at least
two zeros. No assumption about the older remaining tape is made.
"""

from __future__ import annotations


def assert_prefix_phase(left: list[tuple]) -> dict:
    canonical: list[tuple[int, int, int]] = []
    for segment in left:
        if segment[0] == "b":
            assert len(segment) == 2
            bit, coefficient, constant = segment[1], 0, 1
        else:
            assert segment[0] == "r" and len(segment) == 4, (
                "prefix phase requires only literal cells and affine runs", segment)
            _, bit, coefficient, constant = segment
        assert bit in (0, 1)
        assert isinstance(coefficient, int) and isinstance(constant, int)
        assert coefficient >= 0 and constant >= 0
        if coefficient == constant == 0:
            continue
        if canonical and canonical[-1][0] == bit:
            _, old_coefficient, old_constant = canonical[-1]
            canonical[-1] = (bit, old_coefficient + coefficient,
                             old_constant + constant)
        else:
            canonical.append((bit, coefficient, constant))
    # Do not drop trailing zero runs: their first two cells can witness the
    # premise, even when the remaining tape is all blank. Requiring explicit
    # zeros is conservative and sufficient for every certified runtime call.
    assert len(canonical) >= 2, ("missing explicit prefix phase delimiter", canonical)
    one, zero = canonical[:2]
    assert one[0] == 1 and one[2] >= 1, (
        "prefix decrement requires a nonempty header/phase one-run for all n>=0", canonical)
    assert zero[0] == 0 and zero[2] >= 2, (
        "prefix decrement requires two preceding phase zeros for all n>=0", canonical)
    return {
        "one_run_coefficient": one[1],
        "one_run_minimum": one[2],
        "zero_run_coefficient": zero[1],
        "zero_run_minimum": zero[2],
    }


if __name__ == "__main__":
    assert assert_prefix_phase([("b", 1), ("r", 1, 1, 3), ("b", 0),
                                ("b", 0), ("b", 1)])["one_run_minimum"] == 4
    for invalid in [[], [("b", 0), ("b", 0)],
                    [("r", 1, 1, 0), ("b", 0), ("b", 0)],
                    [("b", 1), ("r", 0, 1, 1), ("b", 1)],
                    [("b", 1), ("b", 0), ("b", 1), ("b", 0)]]:
        try:
            assert_prefix_phase(invalid)
        except AssertionError:
            pass
        else:
            raise AssertionError(("invalid phase accepted", invalid))
    print("prefix phase positive and negative checks passed")
