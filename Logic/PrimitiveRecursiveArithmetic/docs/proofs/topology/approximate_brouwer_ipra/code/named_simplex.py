"""Finite approximation for a supplied evaluator A(x,s) and mixed-stage modulus.

The assumed modulus contract is
  ||A(x,s) - A(y,t)||∞ ≤ 2^(-m)
if s,t ≥ m and ||x-y||∞ ≤ 2^(-mu(m)).
The tail checker tests its instances on one returned cell at one caller-chosen
stage. Run python code/named_simplex.py --bits 1 --tail 3 4 8 for an example.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import json

from brouwer import (
    Cell, barycentric, cell_vertices, check_size, check_witness, find_witness,
    rational_point, sample_grid,
)


@dataclass(frozen=True)
class NamedWitness:
    dimension: int
    bits: int
    mesh: int
    cell: Cell
    rows: tuple

    @property
    def stage(self):
        return self.bits + 2

    @property
    def anchor(self):
        return barycentric(self.cell.base, self.mesh)


def find_named_witness(dimension, bits, evaluate, modulus):
    """Search using only stage bits+2, retaining just the chosen cell's rows."""
    check_size(dimension, 1)
    if type(bits) is not int or bits < 0:
        raise ValueError("bits must be a nonnegative integer")
    m = bits + 2
    mu = modulus(m)
    if type(mu) is not int or mu < 0:
        raise ValueError("modulus must return a nonnegative integer")
    mesh = 2 ** max(m, mu)
    samples = sample_grid(dimension, mesh, lambda x: evaluate(x, m))
    cell = find_witness(dimension, mesh, samples)
    rows = tuple(samples[u] for u in cell_vertices(cell))
    return NamedWitness(dimension, bits, mesh, cell, rows)


def check_named_tail(witness, evaluate, stage):
    """Verify the finite table implication for y = A(anchor,stage)."""
    m = witness.stage
    if type(stage) is not int or stage < m:
        raise ValueError("tail stage must be an integer at least bits+2")
    d, mesh = witness.dimension, witness.mesh
    if mesh < 2 ** m:
        raise ValueError("mesh is too coarse for this accuracy")
    vertices = list(cell_vertices(witness.cell))
    if len(witness.rows) != len(vertices):
        raise ValueError("certificate has the wrong number of sample rows")
    samples = dict(zip(vertices, witness.rows))
    check_witness(d, mesh, samples, witness.cell)
    # Check membership of the stored rows in the supplied evaluator's graph.
    for u in vertices:
        fresh = rational_point(evaluate(barycentric(u, mesh), m), d)
        if fresh != samples[u]:
            raise ValueError("stored row differs from the stage-m evaluation")
    x = witness.anchor
    y = rational_point(evaluate(x, stage), d)
    deviation = max(abs(a - b) for row in witness.rows for a, b in zip(y, row))
    omega = Q(1, 2 ** m)
    if deviation > omega:
        raise ValueError("mixed-stage estimate failed on the returned cell")
    residual = max(abs(a - b) for a, b in zip(x, y))
    bound = Q(2 * d, d + 1) * (Q(1, mesh) + omega)
    target = Q(1, 2 ** witness.bits)
    if not residual <= bound < target:
        raise AssertionError("finite certificate bound violated")
    return {"stage": stage, "anchor": x, "tail_sample": y,
            "max_distance_to_cell_samples": deviation, "modulus_bound": omega,
            "residual": residual, "residual_bound": bound, "target": target}


def staged_rotation(x, s):
    """Approximate a cyclic rotation by mixing it with the first vertex.

    The sup distance of two outputs is at most the input sup distance plus
    |alpha_s-alpha_t|. At s,t >= m the latter is at most 2^(-m-2),
    so mu(m)=m+1 gives the required mixed-stage bound.
    """
    alpha = Q(1, 2 ** (s + 2))
    rotation = x[1:] + x[:1]
    return tuple((1 - alpha) * z + (alpha if i == 0 else 0)
                 for i, z in enumerate(rotation))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimension", type=int, default=2)
    parser.add_argument("--bits", type=int, default=1)
    parser.add_argument("--tail", nargs="+", type=int)
    args = parser.parse_args()
    witness = find_named_witness(args.dimension, args.bits, staged_rotation, lambda m: m + 1)
    stages = args.tail if args.tail is not None else [witness.stage, witness.stage + 2]
    result = {"mesh": witness.mesh, "selection_stage": witness.stage,
              "base": witness.cell.base, "permutation": witness.cell.order,
              "checks": [check_named_tail(witness, staged_rotation, s) for s in stages]}
    print(json.dumps(result, default=str, indent=2))


if __name__ == "__main__":
    main()
