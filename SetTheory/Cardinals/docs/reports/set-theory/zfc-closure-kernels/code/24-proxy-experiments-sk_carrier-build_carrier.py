#!/usr/bin/env python3
"""Literal two-symbol TM -> a closed, unoptimized SK term.

No eta rule, extensionality, additional combinator, oracle, or initial tape
is hidden in the serialized payload.  K is the *literal* successful result.
The build uses immutable DAGs only to share its own work; serialization unfolds
the full tree.  This is a reference carrier, not a small-state TM compiler.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from functools import lru_cache
from pathlib import Path


class Terms:
    def __init__(self):
        self.nodes = []
        self.ids = {}
        self.free = []
        self.K = self.atom("K")
        self.S = self.atom("S")
        self.I = self.app(self.S, self.K, self.K)
        self.false = self.app(self.K, self.I)
        self.nil = self.false

    def node(self, row):
        if row in self.ids:
            return self.ids[row]
        result = len(self.nodes)
        self.ids[row] = result
        self.nodes.append(row)
        kind = row[0]
        if kind == "V":
            fv = frozenset((row[1],))
        elif kind == "A":
            fv = self.free[row[1]] | self.free[row[2]]
        elif kind == "L":
            fv = self.free[row[2]] - {row[1]}
        else:
            fv = frozenset()
        self.free.append(fv)
        return result

    def atom(self, name):
        return self.node((name,))

    def var(self, name):
        return self.node(("V", name))

    def app(self, *items):
        assert items
        result = items[0]
        for item in items[1:]:
            result = self.node(("A", result, item))
        return result

    def lam(self, names, body):
        for name in reversed(names.split()):
            body = self.node(("L", name, body))
        return body

    @lru_cache(None)
    def abstract(self, name, body):
        """The three basic SK bracket-abstraction clauses; no eta clause."""
        if name not in self.free[body]:
            return self.app(self.K, body)
        row = self.nodes[body]
        if row == ("V", name):
            return self.I
        assert row[0] == "A", (name, row)
        return self.app(self.S, self.abstract(name, row[1]),
                        self.abstract(name, row[2]))

    @lru_cache(None)
    def compile(self, term):
        row = self.nodes[term]
        if row[0] == "L":
            return self.abstract(row[1], self.compile(row[2]))
        if row[0] == "A":
            return self.app(self.compile(row[1]), self.compile(row[2]))
        return term

    def boolean(self, bit):
        # The first selector represents tape zero and rightward movement.
        return self.K if bit == 0 else self.false

    def tuple(self, *items):
        # Closed data: lambda observer. observer item_1 ... item_n.
        observer = self.var("data_observer")
        return self.abstract("data_observer", self.app(observer, *items))

    def pair(self, first, second):
        return self.tuple(first, second)

    def cons(self, head, tail):
        # lambda cons nil. cons head tail
        cons = self.var("data_cons")
        return self.compile(self.lam("data_cons data_nil",
                                     self.app(cons, head, tail)))

    def list(self, items):
        result = self.nil
        for item in reversed(items):
            result = self.cons(item, result)
        return result

    def state(self, value, width):
        return self.list([self.boolean((value >> shift) & 1)
                          for shift in reversed(range(width))])

    def action(self, write, direction, state):
        # lambda halt active. active write direction next_state
        return self.app(self.K, self.tuple(write, direction, state))

    def view(self, term, fuel=1000000):
        """Left-spine (weak head) SK evaluation; return head, arguments, steps.

        Nodes are immutable: shared subtrees are never destructively updated.
        Consequently each contraction is literally a tree contraction.
        """
        stack, steps = [], 0
        current = term
        while True:
            while self.nodes[current][0] == "A":
                _, left, right = self.nodes[current]
                stack.append(right)
                current = left
            if current == self.K and len(stack) >= 2:
                if steps >= fuel:
                    raise TimeoutError(f"SK budget {fuel} exhausted")
                first = stack.pop()
                stack.pop()
                current = first
            elif current == self.S and len(stack) >= 3:
                if steps >= fuel:
                    raise TimeoutError(f"SK budget {fuel} exhausted")
                first, second, third = stack.pop(), stack.pop(), stack.pop()
                current = self.app(first, third, self.app(second, third))
            else:
                return current, list(reversed(stack)), steps
            steps += 1

    def whnf(self, term, fuel=1000000):
        head, arguments, steps = self.view(term, fuel)
        return self.app(head, *arguments), steps

    @lru_cache(None)
    def counts(self, term):
        row = self.nodes[term]
        if row[0] == "K":
            return 1, 0
        if row[0] == "S":
            return 0, 1
        if row[0] == "A":
            k1, s1 = self.counts(row[1])
            k2, s2 = self.counts(row[2])
            return k1+k2, s1+s2
        raise ValueError("Payload is not pure closed SK")

    def bits(self, term, one_constant=False):
        """Prefix codec: K=00, S=01, app=1; o=0 for one-constant trees."""
        pending = [term]
        while pending:
            current = pending.pop()
            row = self.nodes[current]
            if row[0] == "A":
                yield "1"
                pending.append(row[2])
                pending.append(row[1])
            elif row[0] == "K":
                yield "100" if one_constant else "00"
            elif row[0] == "S":
                yield "10100" if one_constant else "01"
            else:
                raise ValueError("Payload is not pure closed SK")

    def parse_bcl(self, bits):
        """Independent stack parser; rejects trailing, truncated, non-binary data."""
        frames, pos, finished = [], 0, None
        while pos < len(bits):
            if finished is not None:
                raise ValueError("Trailing BCL data")
            char = bits[pos]
            pos += 1
            if char == "1":
                frames.append(None)
                continue
            if char != "0" or pos == len(bits) or bits[pos] not in "01":
                raise ValueError("Invalid/truncated BCL atom")
            value = self.K if bits[pos] == "0" else self.S
            pos += 1
            while frames and frames[-1] is not None:
                value = self.app(frames.pop(), value)
            if frames:
                frames[-1] = value
            else:
                finished = value
        if frames or finished is None:
            raise ValueError("Truncated BCL expression")
        return finished


def interpreter(t):
    """Build the transparent lambda skeleton, then eliminate every binder."""
    a, v, L = t.app, t.var, t.lam
    # Curry's fixed point combinator; intentionally use only basic abstraction.
    half = L("x", a(v("f"), a(v("x"), v("x"))))
    fix = t.compile(L("f", a(half, half)))
    cons = t.compile(L("h tail c n", a(v("c"), v("h"), v("tail"))))

    # Scott-list path through a complete binary tree of Church pairs.
    look_body = L("look path tree", a(v("path"),
                    L("b rest", a(v("look"), v("rest"),
                                   a(v("tree"), v("b")))),
                    v("tree")))
    lookup = a(fix, t.compile(look_body))

    # Exactly the same F is used for the full run and the one-step trace tests.
    fresh_left = a(cons, v("w"), v("left"))
    fresh_right = a(cons, v("w"), v("right"))
    right_move = a(v("right"),
        L("b rest", a(v("rec"), v("next"), fresh_left, v("b"), v("rest"))),
        a(v("rec"), v("next"), fresh_left, t.K, t.nil))
    left_move = a(v("left"),
        L("b rest", a(v("rec"), v("next"), v("rest"), v("b"), fresh_right)),
        a(v("rec"), v("next"), t.nil, t.K, fresh_right))
    act_handler = L("w direction next",
                    a(v("direction"), right_move, left_move))
    selected = a(lookup, v("q"), v("table"), v("bit"))
    F_lambda = L("table rec q left bit right", a(selected, t.K, act_handler))
    F = t.compile(F_lambda)
    run = t.compile(L("table", a(fix, a(F, v("table")))))
    config = t.compile(L("q left bit right observer",
                        a(v("observer"), v("q"), v("left"),
                          v("bit"), v("right"))))
    return {"F": F, "run": run, "config": config, "fix": fix,
            "lookup": lookup, "cons": cons}


def parse_tm(path):
    transitions, start = {}, None
    for lineno, raw in enumerate(Path(path).read_text().splitlines(), 1):
        line = raw.strip()
        if line.startswith("#! start "):
            if start is not None:
                raise ValueError("Repeated start declaration")
            start = int(line.split()[2])
        elif line and not line.startswith("#"):
            parts = line.split()
            if len(parts) != 5:
                raise ValueError(f"Bad line {lineno}: {line}")
            q, bit, write, direction, nxt = parts
            q, bit, write, nxt = map(int, (q, bit, write, nxt))
            if min(q, nxt) < 0 or bit not in (0, 1) or write not in (0, 1):
                raise ValueError(f"Bad transition at {lineno}")
            if direction not in ("L", "R") or (q, bit) in transitions:
                raise ValueError(f"Bad direction or duplicate at {lineno}")
            transitions[q, bit] = (write, direction, nxt)
    if start is None:
        raise ValueError("Require literal #! start N declaration")
    return start, transitions


def compile_machine(t, core, start, transitions):
    labels = [start] + [q for q, _ in transitions] + [v[2] for v in transitions.values()]
    width = max(labels).bit_length()
    states = [t.state(q, width) for q in range(1 << width)]
    rows = []
    for q in range(1 << width):
        actions = []
        for bit in (0, 1):
            if (q, bit) not in transitions:
                actions.append(t.K)  # Scott Halt = lambda h a. h.
            else:
                write, direction, nxt = transitions[q, bit]
                actions.append(t.action(t.boolean(write),
                                        t.boolean(direction == "L"), states[nxt]))
        rows.append(t.pair(*actions))
    while len(rows) > 1:
        rows = [t.pair(rows[i], rows[i+1]) for i in range(0, len(rows), 2)]
    table = rows[0]
    P = t.app(core["run"], table, states[start], t.nil, t.K, t.nil)
    assert not t.free[P]
    return {"P": P, "table": table, "states": states, "width": width}


def write_payload(t, term, path, one_constant=False):
    digest = hashlib.sha256()
    bit_count, buffer = 0, []
    packed, accumulator, pending_bits = bytearray(), 0, 0
    with Path(path).open("wb") as output:
        for chunk in t.bits(term, one_constant):
            buffer.append(chunk)
            bit_count += len(chunk)
            accumulator = (accumulator << len(chunk)) | int(chunk, 2)
            pending_bits += len(chunk)
            while pending_bits >= 8:
                pending_bits -= 8
                packed.append(accumulator >> pending_bits)
                accumulator &= (1 << pending_bits)-1
            if len(buffer) >= 8192:
                data = "".join(buffer).encode("ascii")
                output.write(data)
                digest.update(data)
                buffer = []
        data = "".join(buffer).encode("ascii")
        output.write(data)
        digest.update(data)
    if pending_bits:
        packed.append(accumulator << (8-pending_bits))
    Path(str(path)+".bin").write_bytes(packed)
    return {"bits": bit_count, "ascii_bytes": bit_count,
            "packed_bytes_ceiling": (bit_count+7)//8,
            "sha256_ascii_no_newline": digest.hexdigest(),
            "packed_file": Path(str(path)+".bin").name,
            "packed_bit_order": "most significant bit first; zero pad final byte",
            "sha256_packed": hashlib.sha256(packed).hexdigest()}


def generate(tm_path, output_dir):
    out = Path(output_dir)
    out.mkdir(parents=True, exist_ok=True)
    start, transitions = parse_tm(tm_path)
    t = Terms()
    core = interpreter(t)
    machine = compile_machine(t, core, start, transitions)
    P = machine["P"]
    k, s = t.counts(P)
    metrics = {
        "input_sha256": hashlib.sha256(Path(tm_path).read_bytes()).hexdigest(),
        "start": start,
        "defined_states": len(set(q for q, _ in transitions)),
        "transitions": len(transitions),
        "state_path_bits": machine["width"],
        "K_leaves": k, "S_leaves": s,
        "application_nodes": k+s-1,
        "tree_nodes": 2*(k+s)-1,
        "compilation": "basic SK bracket abstraction, no eta optimization",
        "successful_result": "literal K with no pending arguments",
        "bcl_convention": "K=00; S=01; application=1",
        "one_constant_convention": "o=0; application=1; K->(o o); S->(o (o o))",
        "components": {},
    }
    for name, term in {**core, "table": machine["table"]}.items():
        ck, cs = t.counts(term)
        metrics["components"][name] = {"K": ck, "S": cs, "bcl_bits": 3*(ck+cs)-1}
    metrics["P253.bcl"] = write_payload(t, P, out / "P253.bcl")
    metrics["P253.one.btree"] = write_payload(t, P, out / "P253.one.btree", True)
    assert metrics["P253.bcl"]["bits"] == 3*(k+s)-1
    assert metrics["P253.one.btree"]["bits"] == 4*k+6*s-1
    # Reparse exactly what was emitted and compare structural identity.
    assert t.parse_bcl((out / "P253.bcl").read_text()) == P
    metrics["serialized_bcl_roundtrip"] = True
    (out / "metrics.json").write_text(json.dumps(metrics, indent=2)+"\n")
    return metrics


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tm", type=Path)
    parser.add_argument("--output", type=Path, default=Path(__file__).parent)
    args = parser.parse_args()
    print(json.dumps(generate(args.tm, args.output), indent=2))
