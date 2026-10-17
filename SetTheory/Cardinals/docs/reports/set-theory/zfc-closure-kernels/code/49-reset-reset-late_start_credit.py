#!/usr/bin/env python3
"""Exact finite stack-credit certificates for ProveIt's frozen enumerator.

This is a source-level mathematical checker, not a new binary machine or a
Lean proof. Command meanings are the literal Enum254.lean definitions at
ProveIt commit fab89c5d26b81cd2ccab2ee5d213ff23725c7726. New results:

* Clean roots with pl=0 and np in {0,1,2,4,5,6} admit arbitrary tw,ws,d,h.
* A finite exact conservative stack-credit calculation admits late starts.
* An arbitrary-data AX command shields the old data below eight logical
  axioms, giving a broader, effectively checkable dirty-root criterion.

The count 10 for later AX commands assumes theorem-valued active formulas;
the first AX in an entirely dirty state guarantees only 8 good stack cells.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
from math import isqrt
from pathlib import Path
import random
import re

PIN = "fab89c5d26b81cd2ccab2ee5d213ff23725c7726"
DIRTY_RESET_COUNTERS = (0, 1, 2, 4, 5, 6)


def pair(a: int, b: int) -> int:
    assert a >= 0 and b >= 0
    return b + (a + b) * (a + b + 1) // 2


def unpair(n: int) -> tuple[int, int]:
    assert n >= 0
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


@dataclass(frozen=True)
class Command:
    op: int
    fields: tuple[int, ...]

    @property
    def effect(self) -> int:
        return 1 if self.op == 1 else -1 if self.op == 2 else 10 if self.op >= 3 else 0

    @property
    def kind(self) -> str:
        return ("MP", "DROP", "NIP")[self.op] if self.op < 3 else "AX"


def read_command(n: int) -> tuple[Command, int]:
    op, r = unpair(n)
    fields = []
    for _ in range(3 if op >= 3 else 1):
        a, r = unpair(r)
        fields.append(a)
    return Command(op, tuple(fields)), r


@lru_cache(maxsize=None)
def decode(n: int) -> tuple[Command, ...]:
    result = []
    while True:
        c, r = read_command(n)
        result.append(c)
        if r == 0:
            return tuple(result)
        assert r - 1 < n
        n = r - 1


def pack(c: Command, rest: int) -> int:
    for value in reversed(c.fields):
        rest = pair(value, rest)
    return pair(c.op, rest)


def encode(commands: tuple[Command, ...]) -> int:
    assert commands
    r = pack(commands[-1], 0)
    for c in reversed(commands[:-1]):
        r = pack(c, r + 1)
    return r


# Delta[n] counts all DROP occurrences minus NIP occurrences in candidates < n.
_delta = [0]


def delta_before(n: int) -> int:
    while len(_delta) <= n:
        commands = decode(len(_delta) - 1)
        value = _delta[-1] + sum((c.op == 1) - (c.op == 2) for c in commands)
        assert value >= 0
        _delta.append(value)
    return _delta[n]


@lru_cache(maxsize=None)
def canonical_credit(n: int) -> dict:
    """Exact minimal credit when MP adds 0, DROP 1, NIP -1 and AX 10.

    At every future command prefix DROP-NIP >= -Delta[n], by the marked
    occurrence injection. Once ceil(Delta[n]/10) AX commands are completed,
    every later prefix has nonnegative relative balance. Consequently the
    global minimum is found by this finite scan, including its initial zero.
    """
    delta = delta_before(n)
    target_ax = (delta + 9) // 10
    balance = minimum = ax_count = commands_seen = 0
    candidate = n
    witness = None
    stop_position = None
    while ax_count < target_ax:
        for position, c in enumerate(decode(candidate)):
            balance += c.effect
            commands_seen += 1
            ax_count += c.op >= 3
            if balance < minimum:
                minimum = balance
                witness = [candidate, position]
            if ax_count == target_ax:
                stop_position = [candidate, position]
                break
        candidate += 1
    # Single-command AX candidates P(s,0), s>=3, give an explicit bound.
    s = max(3, (isqrt(8 * n + 1) - 1) // 2)
    if s * (s + 1) // 2 < n:
        s += 1
    explicit_last = (s + target_ax - 1) * (s + target_ax) // 2 if target_ax else n
    assert target_ax == 0 or stop_position[0] <= explicit_last
    assert minimum >= -delta
    return dict(np=n, credit=-minimum, delta=delta, target_ax=target_ax,
                commands_scanned=commands_seen, stop=stop_position,
                negative_minimum_at=witness,
                explicit_candidate_bound=explicit_last)


def required_credit(pl: int, np: int) -> dict:
    """Credit for an arbitrary finite current suffix, then candidates >= np."""
    prefix = decode(pl - 1) if pl else ()
    balance = minimum = 0
    for c in prefix:
        balance += c.effect
        minimum = min(minimum, balance)
    tail = canonical_credit(np)
    credit = max(0, -minimum, tail["credit"] - balance)
    return dict(pl=pl, np=np, credit=credit, initial_suffix_commands=len(prefix),
                initial_suffix_balance=balance, initial_suffix_minimum=minimum,
                canonical_tail=tail)


def advance_control(pl: int, np: int) -> tuple[Command, int, int]:
    value, new_np = (np, np + 1) if pl == 0 else (pl - 1, np)
    command, new_pl = read_command(value)
    return command, new_pl, new_np


def virtual_control(pl: int, np: int, ac: int, s1: int, s2: int) -> tuple[int, int]:
    """Exact control part of DirtyRoot254.virtual, before one command."""
    if pl == 0:
        fpl, fnp, fs1 = np, np + s1 + 1, 0
    else:
        fpl, fnp, fs1 = pl - 1, np, s1
    op, rest = unpair(pair(fs1, s2) + fpl)
    return pair(ac + op, rest) + 1, fnp


def certify_control_root(pl: int, np: int, ac: int = 0,
                         s1: int = 0, s2: int = 0) -> dict:
    """Sufficient all-working-data criterion for a structured-program root.

    A negative answer is inconclusive, except a first NIP permits the explicit
    counterexample h=1. This does not certify any binary tape representation.
    """
    control = dict(pl=pl, np=np, ac=ac, s1=s1, s2=s2)
    if not any((pl, ac, s1, s2)) and np in DIRTY_RESET_COUNTERS:
        return dict(control=control, accepted=True, reason="finite_reset_to_candidate7",
                    guaranteed_good_prefix=8 if np == 6 else 10,
                    canonical_credit_bound=delta_before(7))
    vpl, vnp = virtual_control(pl, np, ac, s1, s2)
    first, r1, n1 = advance_control(vpl, vnp)
    if first.op >= 3:
        credit = required_credit(r1, n1)
        return dict(control=control, accepted=credit["credit"] <= 8,
                    reason="AX_eight_axiom_shield", credit=credit,
                    virtual_control=[vpl, vnp], first_command=first.__dict__)
    if first.op == 2:
        return dict(control=control, accepted=False,
                    reason="first_NIP_halts_for_initial_cache1",
                    virtual_control=[vpl, vnp])
    second, r2, n2 = advance_control(r1, n1)
    if first.op in (0, 1) and second.op == 0:
        credit = required_credit(r2, n2)
        return dict(control=control, accepted=credit["credit"] == 0,
                    reason="two_command_active_formula_reset", credit=credit,
                    virtual_control=[vpl, vnp],
                    command_kinds=[first.kind, second.kind])
    return dict(control=control, accepted=False, reason="no_certificate_in_this_family",
                virtual_control=[vpl, vnp])


@dataclass(frozen=True)
class State:
    pl: int
    np: int
    tw: int
    ws: int
    d: int
    h: int


def pre_ax_step(s: State) -> State | None:
    """Semantic command execution, restricted to the pre-AX finite trace."""
    c, pl, np = advance_control(s.pl, s.np)
    x = c.fields[0]
    d = s.d + x
    if c.op == 0:
        succeeds = 4 * pair(s.tw, d) == s.h
        return State(pl, np, d if succeeds else 0,
                     pair(0, s.ws) if succeeds else s.ws, d, 0)
    if c.op == 1:
        return State(pl, np, s.h, pair(s.tw, s.ws), d, s.h)
    if c.op == 2:
        if s.h == 1:
            return None
        head, tail = unpair(s.ws)
        return State(pl, np, s.tw, tail, d, head)
    raise ValueError("AX reached: use the structural axiom-stack certificate")


def raw_pre_ax_step(s: State) -> State | None:
    """Independent direct transcription of the literal nested-unpair execAt."""
    z, n = (s.np, s.np + 1) if s.pl == 0 else (s.pl - 1, s.np)
    op = unpair(z)[0]
    x = unpair(unpair(z)[1])[0]
    r = unpair(unpair(z)[1])[1]
    if op == 0:
        if 4 * pair(s.tw, s.d + x) == s.h:
            return State(r, n, s.d + x, pair(0, s.ws), s.d + x, 0)
        return State(r, n, 0, s.ws, s.d + x, 0)
    if op == 1:
        return State(r, n, s.h, pair(s.tw, s.ws), s.d + x, s.h)
    if op == 2:
        if s.h == 1:
            return None
        return State(r, n, s.tw, unpair(s.ws)[1], s.d + x, unpair(s.ws)[0])
    raise ValueError("AX reached")


def reset_trace(np: int, tw: int, ws: int, d: int, h: int) -> dict:
    assert np in DIRTY_RESET_COUNTERS
    s = State(0, np, tw, ws, d, h)
    records = []
    while advance_control(s.pl, s.np)[0].op < 3:
        c = advance_control(s.pl, s.np)[0]
        next_state = pre_ax_step(s)
        assert next_state == raw_pre_ax_step(s)
        assert next_state is not None, (s, c)
        records.append(c.kind)
        s = next_state
        assert len(records) <= 7
    c, next_pl, next_np = advance_control(s.pl, s.np)
    assert (c, next_pl, next_np) == (Command(3, (0, 0, 0)), 0, 7)
    if np != 6:
        assert s.tw == s.h == 0
    if np == 0:
        old_tail = pair(0, ws) if 4 * pair(tw, d) == h else ws
        assert s == State(0, 6, 0, pair(0, old_tail), d + 2, 0)
    # The first eight stack entries are rho1..rho8, with arbitrary parameters;
    # the exact next two are All(d,h),tw. They are good too for the clean case.
    good = 8 + 2 * (np != 6)
    assert good >= delta_before(7)
    return dict(start_np=np, pre_AX_commands=records, state_before_AX=s.__dict__,
                root_after_AX=[0, 7], good_prefix=good,
                hidden_tail_read_after_AX=False)


def verify_reset_cases() -> dict:
    count = branch_count = large_count = 0
    for np in DIRTY_RESET_COUNTERS:
        for tw in range(7):
            for ws in range(7):
                for d in range(7):
                    for h in range(7):
                        reset_trace(np, tw, ws, d, h)
                        count += 1
        # Directly force the initial MP success and adjacent failure values.
        first, _, _ = advance_control(0, np)
        if first.op == 0:
            for tw in range(12):
                for ws in range(12):
                    for d in range(12):
                        target = 4 * pair(tw, d + first.fields[0])
                        for h in (target, target + 1, max(0, target - 1)):
                            reset_trace(np, tw, ws, d, h)
                            branch_count += 1
    rng = random.Random(20261017)
    for _ in range(256):
        np = rng.choice(DIRTY_RESET_COUNTERS)
        values = [rng.getrandbits(rng.choice((64, 256, 1024, 4096))) for _ in range(4)]
        reset_trace(np, *values)
        large_count += 1
    bad = pre_ax_step(State(0, 3, 0, 0, 0, 1))
    assert bad is None
    return dict(exhaustive_grid_cases=count, forced_MP_branch_cases=branch_count,
                large_integer_cases=large_count, maximum_input_bits=4096,
                np3_explicit_immediate_halt=True)


def verify_occurrences(limit: int) -> dict:
    drops = set()
    mapped = set()
    d = n = 0
    commands_seen = ax = 0
    for candidate in range(limit):
        assert delta_before(candidate) == d - n
        commands = decode(candidate)
        assert encode(commands) == candidate
        for position, c in enumerate(commands):
            if c.op == 1:
                drops.add((candidate, position))
                d += 1
            elif c.op == 2:
                changed = list(commands)
                changed[position] = Command(1, c.fields)
                image = (encode(tuple(changed)), position)
                assert image[0] < candidate and image in drops and image not in mapped
                mapped.add(image)
                assert d >= n + 1
                n += 1
            commands_seen += 1
            ax += c.op >= 3
    # Independent inverse map: outstanding DROP occurrences cross the cut.
    crossing = 0
    for candidate, position in drops:
        commands = list(decode(candidate))
        commands[position] = Command(2, commands[position].fields)
        crossing += encode(tuple(commands)) >= limit
    assert crossing == d - n == delta_before(limit)
    return dict(candidates=limit, command_occurrences=commands_seen,
                DROP_occurrences=d, NIP_occurrences=n, AX_occurrences=ax,
                injective_images=len(mapped), crossing_pairs=crossing)


def verify_credit(limit: int) -> dict:
    histogram = {}
    for n in range(limit):
        certificate = canonical_credit(n)
        k = certificate["credit"]
        histogram[k] = histogram.get(k, 0) + 1
        # Replay independently using an actual protected-depth counter until
        # the advertised cutoff, then twenty additional candidate programs.
        last = (certificate["stop"] or [n, 0])[0] + 20
        depth = k
        min_depth = depth
        for candidate in range(n, last + 1):
            for c in decode(candidate):
                if c.op == 1:
                    depth += 1
                elif c.op == 2:
                    assert depth > 0
                    depth -= 1
                elif c.op >= 3:
                    depth += 10
                min_depth = min(min_depth, depth)
        assert min_depth >= 0
        if k:
            assert min_depth == 0
    return dict(late_starts_checked=limit, exact_credit_histogram=histogram,
                model="MP adds0; DROP adds1; NIP removes1; AX adds10",
                actual_machine_necessity_claimed=False)


def source_identities() -> dict:
    here = Path(__file__).resolve().parent
    source = here / "sources" / "Enum254.lean"
    text = source.read_text()
    definitions = {}
    for name in ("axStack", "gate", "cstep", "pack", "encL", "fetch", "execAt", "enumStep"):
        pattern = r"(?m)^def " + name + r"\b.*?(?=\n(?:/--|def |theorem |inductive |structure |/-!))"
        body = re.search(pattern, text, re.S).group()
        definitions[name] = hashlib.sha256(body.encode()).hexdigest()
    return dict(commit=PIN, path="Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean",
                file_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                semantic_definition_sha256=definitions)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=5000)
    parser.add_argument("--control-limit", type=int, default=256)
    args = parser.parse_args()
    assert args.limit > 0
    result = dict(source=source_identities(), resets=verify_reset_cases(),
                  occurrence_certificate=verify_occurrences(args.limit),
                  finite_credit_checks=verify_credit(args.limit),
                  small_credit_examples=[canonical_credit(n) for n in range(20)],
                  simple_reset_starts=list(DIRTY_RESET_COUNTERS),
                  complete_binary_machine_claimed=False, Lean_checked=False)
    controls = [certify_control_root(0, n) for n in range(args.control_limit)]
    result["clean_control_census"] = dict(limit=args.control_limit,
        accepted_np=[x["control"]["np"] for x in controls if x["accepted"]],
        rejected_are_not_general_obstructions=True, every_result=controls)
    result["representative_traces"] = [reset_trace(n, 7, 19, 3, 4 * pair(7, 3))
                                       for n in DIRTY_RESET_COUNTERS]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: result[key] for key in ("resets", "occurrence_certificate",
                                                  "finite_credit_checks")}, indent=2))
    print("Accepted clean counter values:", result["clean_control_census"]["accepted_np"])


if __name__ == "__main__":
    main()
