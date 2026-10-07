"""Squarefree-variable inventory for arbitrary fixed systems of equations."""
from __future__ import annotations
from fractions import Fraction
from typing import Sequence
from energy_inventory import FiniteAbelianGroup, Element, Scalar, rational, response_coefficients


class SystemInventory:
    """steps[j] is the group increment from assigning this label to position j.

    Different labels can have different steps. The same label is selected once
    even when it occupies multiple positions. Zero and nonunit coefficients are
    permitted, including over composite cyclic groups.
    """
    def __init__(self, group: FiniteAbelianGroup, positions: int) -> None:
        if positions < 1:
            raise ValueError("positions must be positive")
        self.group, self.positions = group, positions
        self.elements = group.elements()
        self.A = [[0] * group.size for _ in range(1 << positions)]
        self.A[0][0] = 1
        self.masks = sorted(range(1 << positions), key=int.bit_count, reverse=True)

    def subset_steps(self, steps: Sequence[Element]) -> list[Element]:
        if len(steps) != self.positions:
            raise ValueError("wrong number of positions")
        shifts = [self.group.zero] * (1 << self.positions)
        for mask in range(1, len(shifts)):
            low = mask & -mask
            shifts[mask] = self.group.add(shifts[mask ^ low], steps[low.bit_length() - 1])
        return shifts

    def apply(self, steps: Sequence[Element], coefficients: Sequence[Scalar]) -> None:
        if len(coefficients) < self.positions + 1 or coefficients[0] != 1:
            raise ValueError("invalid response coefficients")
        shifts = self.subset_steps(steps)
        for mask in self.masks:
            sub = mask
            while sub:
                c = coefficients[sub.bit_count()]
                if c:
                    src, out = self.A[mask ^ sub], self.A[mask]
                    for ix, value in enumerate(src):
                        if value:
                            j = self.group.index(self.group.add(self.elements[ix], shifts[sub]))
                            out[j] += c * value
                sub = (sub - 1) & mask

    def add_label(self, steps: Sequence[Element], probability: Scalar) -> None:
        p = rational(probability)
        if not 0 <= p <= 1:
            raise ValueError("probability outside [0,1]")
        self.apply(steps, [1] + [p] * self.positions)

    def count(self) -> Scalar:
        return self.A[-1][0]

    def derivative(self, steps: Sequence[Element], probability: Scalar) -> Scalar:
        h = response_coefficients(probability, self.positions)
        shifts = self.subset_steps(steps)
        mask = (1 << self.positions) - 1
        return sum(h[sub.bit_count()] * self.A[mask ^ sub][self.group.index(self.group.scale(-1, shifts[sub]))]
                   for sub in range(1, mask + 1))

    def replace_probability(self, steps: Sequence[Element], p: Scalar, q: Scalar) -> None:
        h = response_coefficients(p, self.positions)
        self.apply(steps, [1] + [(q - p) * h[k] for k in range(1, self.positions + 1)])


def system_round(models: Sequence[tuple[FiniteAbelianGroup,
                                         Sequence[Sequence[Element]], Scalar]],
                 probabilities: Sequence[Scalar], positions: int) -> dict:
    """Round a signed sum of position-dependent system counts.

    A model is (group, steps_by_label, signed_coefficient).
    steps_by_label[i][j] is label i's increment in position j.
    All models use the same label order and number of positions.
    """
    p = [rational(x) for x in probabilities]
    if not models or any(len(steps) != len(p) for _, steps, _ in models):
        raise ValueError("nonempty models with shared label counts required")
    if any(not 0 <= q <= 1 for q in p):
        raise ValueError("probabilities outside [0,1]")
    weights = [rational(w) for _, _, w in models]
    inventories = []
    for group, steps, _ in models:
        inv = SystemInventory(group, positions)
        for label_steps, probability in zip(steps, p):
            inv.add_label(label_steps, probability)
        inventories.append(inv)
    value = sum(w * inv.count() for w, inv in zip(weights, inventories))
    initial, trace = value, []
    for i, old in enumerate(p):
        if old in (0, 1):
            continue
        deriv = sum(w * inv.derivative(steps[i], old)
                    for w, inv, (_, steps, _) in zip(weights, inventories, models))
        new = Fraction(int(deriv >= 0))
        previous = value
        for inv, (_, steps, _) in zip(inventories, models):
            inv.replace_probability(steps[i], old, new)
        value = sum(w * inv.count() for w, inv in zip(weights, inventories))
        assert value == previous + (new - old) * deriv and value >= previous
        p[i] = new
        trace.append({"index": i, "new": int(new), "objective": str(value)})
    return {"selected_indices": [i for i, q in enumerate(p) if q == 1],
            "initial_objective": initial, "final_objective": value, "trace": trace}
