"""Generate test grids by explicit isotopy moves, with reproducible seeds.

Stabilizations are used ONLY to manufacture examples, never by the recognizer.
"""
from __future__ import annotations
import random
from unknot.grid import Grid, Move, moves


def stabilize(grid: Grid, row: int, column: int,
              row_after: bool = True, column_after: bool = True) -> Grid:
    if not 0 <= row < grid.size or column not in grid.rows[row]:
        raise ValueError("choose an existing corner")
    insert_row = row + int(row_after)
    insert_column = column + int(column_after)
    shifted_row = row + (row >= insert_row)
    shifted_column = column + (column >= insert_column)
    corners = {(r + (r >= insert_row), c + (c >= insert_column))
               for r, pair in enumerate(grid.rows) for c in pair}
    corners.remove((shifted_row, shifted_column))
    corners.update(((shifted_row, insert_column), (insert_row, shifted_column),
                    (insert_row, insert_column)))
    result = Grid.from_rows([[c for r, c in corners if r == i]
                             for i in range(grid.size + 1)])
    # Check the exact inverse, not just an invariant of the result.
    if Move("destabilize", insert_row, insert_column).apply(result) != grid:
        raise ArithmeticError("stabilization inverse did not recover input")
    return result


def scramble(grid: Grid, target_size: int, seed: int,
             exchanges_per_level: int = 30) -> Grid:
    if target_size < grid.size:
        raise ValueError("target size is smaller than initial size")
    rng = random.Random(seed)
    current = grid
    while current.size < target_size:
        row = rng.randrange(current.size)
        column = rng.choice(current.rows[row])
        current = stabilize(current, row, column, bool(rng.getrandbits(1)),
                            bool(rng.getrandbits(1)))
        for _ in range(exchanges_per_level):
            choices = [move for move in moves(current) if move.kind != "destabilize"]
            if choices:
                current = rng.choice(choices).apply(current)
            current = current.shift(rng.randrange(current.size), rng.randrange(current.size))
    return current.canonical()
