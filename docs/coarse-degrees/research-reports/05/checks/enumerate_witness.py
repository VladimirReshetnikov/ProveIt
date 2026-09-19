#!/usr/bin/env python3
"""Finite c.e. approximations to the diagonal set defined in the paper.

Only positive enumerations are certified. A zero in a displayed finite
approximation does NOT certify that the corresponding final bit is zero.
A timed-out program is UNKNOWN, not proved divergent.

Enumeration of partial numerical functions:
    phi_0(x) = 0; phi_1(x) = 1; phi_2(x) = x % 2.
    phi_e, e >= 3, is the register program with code e - 3.

Register programs use registers R_0, R_1, ... containing natural numbers.
Initially R_0 is the input and all other registers are zero. Execution starts
at instruction 0. HALT outputs R_0. INC(r, next) increments R_r and jumps.
DECJZ(r, zero, nonzero) jumps to zero if R_r = 0; otherwise it decrements
R_r and jumps to nonzero. An out-of-range program counter is a nonhalting
sink. This is the usual unrestricted-register machine model.

Cantor pairing: pair(a,b) = (a+b)(a+b+1)/2 + b.
List encoding: [] -> 0; head :: tail -> 1 + pair(head, code(tail)).
Instructions: HALT -> 0; INC -> 1+2*pair(r,next);
              DECJZ -> 2+2*pair(r,pair(zero,nonzero)).
Every finite program has a code. This machine's universality is a standard
background fact, not an additional theorem verified by the finite tests.

Python 3.9+, standard library only.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from functools import lru_cache
from math import isqrt
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple

Instruction = Tuple[int, ...]
Program = Tuple[Instruction, ...]


def pair(a: int, b: int) -> int:
    if a < 0 or b < 0:
        raise ValueError("pairing arguments must be nonnegative")
    return (a + b) * (a + b + 1) // 2 + b


def unpair(value: int) -> Tuple[int, int]:
    if value < 0:
        raise ValueError("pairing code must be nonnegative")
    diagonal = (isqrt(8 * value + 1) - 1) // 2
    b = value - diagonal * (diagonal + 1) // 2
    return diagonal - b, b


def encode_list(items: Sequence[int]) -> int:
    result = 0
    for item in reversed(items):
        result = 1 + pair(item, result)
    return result


def decode_list(value: int) -> List[int]:
    if value < 0:
        raise ValueError("list code must be nonnegative")
    result: List[int] = []
    while value:
        head, value = unpair(value - 1)
        result.append(head)
    return result


def encode_instruction(inst: Instruction) -> int:
    if inst == (0,):
        return 0
    if len(inst) == 3 and inst[0] == 1:
        return 1 + 2 * pair(inst[1], inst[2])
    if len(inst) == 4 and inst[0] == 2:
        return 2 + 2 * pair(inst[1], pair(inst[2], inst[3]))
    raise ValueError("invalid instruction")


def decode_instruction(code: int) -> Instruction:
    if code < 0:
        raise ValueError("instruction code must be nonnegative")
    if code == 0:
        return (0,)
    if code % 2:
        register, next_pc = unpair((code - 1) // 2)
        return (1, register, next_pc)
    register, targets = unpair((code - 2) // 2)
    zero_pc, nonzero_pc = unpair(targets)
    return (2, register, zero_pc, nonzero_pc)


def encode_program(program: Sequence[Instruction]) -> int:
    return encode_list([encode_instruction(inst) for inst in program])


@lru_cache(maxsize=4096)
def decode_program(code: int) -> Program:
    return tuple(decode_instruction(inst) for inst in decode_list(code))


def run_program(program: Program, argument: int, budget: int) -> Optional[int]:
    """Return a witnessed output, or None for no observed halting output."""
    if argument < 0 or budget < 0:
        raise ValueError("argument and budget must be nonnegative")
    registers: Dict[int, int] = {0: argument}
    pc = 0
    for _ in range(budget):
        if not 0 <= pc < len(program):
            return None  # No halting instruction was reached.
        inst = program[pc]
        opcode = inst[0]
        if opcode == 0:
            return registers.get(0, 0)
        register = inst[1]
        value = registers.get(register, 0)
        if opcode == 1:
            registers[register] = value + 1
            pc = inst[2]
        elif opcode == 2:
            if value == 0:
                pc = inst[2]
            else:
                registers[register] = value - 1
                pc = inst[3]
        else:
            raise ValueError("invalid opcode")
    return None


def evaluate_phi(index: int, argument: int, budget: int) -> Optional[int]:
    if index < 0 or argument < 0 or budget < 0:
        raise ValueError("index, argument, and budget must be nonnegative")
    if budget == 0:
        return None
    if index == 0:
        return 0
    if index == 1:
        return 1
    if index == 2:
        return argument % 2
    return run_program(decode_program(index - 3), argument, budget)


def column_position(column: int, offset: int) -> int:
    if column < 0 or offset < 0:
        raise ValueError("column and offset must be nonnegative")
    return (1 << column) * (2 * offset + 1) - 1


def column_coordinates(position: int) -> Tuple[int, int]:
    if position < 0:
        raise ValueError("position must be nonnegative")
    value = position + 1
    lowbit = value & -value
    column = lowbit.bit_length() - 1
    offset = (value // lowbit - 1) // 2
    return column, offset


def finite_column_ones(observations: Sequence[Optional[int]]) -> Set[int]:
    """Indices confirmed as 1 before the first not-confirmed-binary value."""
    result: Set[int] = set()
    for j, output in enumerate(observations):
        if output not in (0, 1):
            break
        if output == 0:
            result.add(j)
    return result


@dataclass(frozen=True)
class Approximation:
    stage: int
    ones: Tuple[int, ...]
    computations_attempted: int


def approximate_witness(stage: int) -> Approximation:
    """A_s: inspect n < s, using a budget of s for each required computation."""
    if stage < 0:
        raise ValueError("stage must be nonnegative")
    ones: Set[int] = set()
    attempts = 0
    column = 0
    while column_position(column, 0) < stage:
        offset = 0
        while True:
            position = column_position(column, offset)
            if position >= stage:
                break
            attempts += 1
            output = evaluate_phi(column, position, stage)
            if output not in (0, 1):
                # Any later bit needs this computation to have a binary value.
                break
            if output == 0:
                ones.add(position)
            offset += 1
        column += 1
    return Approximation(stage, tuple(sorted(ones)), attempts)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", type=int, default=1024)
    parser.add_argument("--prefix", type=int, default=128,
                        help="display at most this many finite-approximation bits")
    parser.add_argument("--output", type=Path,
                        help="write JSON here instead of standard output")
    args = parser.parse_args()
    if args.stage < 0 or args.prefix < 0:
        parser.error("--stage and --prefix must be nonnegative")
    approximation = approximate_witness(args.stage)
    ones = set(approximation.ones)
    result = {
        "construction": "dyadic-column c.e. diagonal witness",
        "stage": args.stage,
        "confirmed_one_count": len(ones),
        "confirmed_one_positions": list(approximation.ones),
        "finite_approximation_prefix": "".join(
            "1" if n in ones else "0" for n in range(min(args.stage, args.prefix))
        ),
        "computations_attempted": approximation.computations_attempted,
        "warning": (
            "A displayed 0 is only absence from A_s, not a decision of final "
            "nonmembership. Timeouts are unknown. This does not compute the "
            "perfect-family branches or verify an infinite theorem."
        ),
    }
    text = json.dumps(result, indent=2) + "\n"
    try:
        if args.output:
            args.output.write_text(text, encoding="utf-8")
        else:
            print(text, end="")
    except OSError as exc:
        parser.exit(1, "Could not write output: %s\n" % exc)


if __name__ == "__main__":
    main()
