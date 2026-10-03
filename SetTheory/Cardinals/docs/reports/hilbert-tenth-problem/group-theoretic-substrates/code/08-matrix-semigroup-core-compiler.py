#!/usr/bin/env python3
"""Authored fixed U15 -> directed rewriting -> numerical SL4 semigroup compiler.

Standard library only. Reads a pinned 30-cell DATA table; no upstream source is
imported or executed. This executable starts at finite U15 tapes, not arbitrary
Turing machine source programs. See PROOF.md for the published universality step.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
TABLE_SHA256 = "0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a"
STATES = tuple("ABCDEFGHIJKLMNO")
BITS = ("0", "1")
ALPHABET = BITS + STATES + ("[", "]", "X")
SEPARATOR = "#"
TERMINAL = "X"
TOP_CODES = {a: i + 1 for i, a in enumerate(ALPHABET + (SEPARATOR,))}
I2 = ((1, 0), (0, 1))
P = ((1, 2), (0, 1))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def mul(a, b):
    """Exact 2 by 2 integer matrix multiplication."""
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def inv(a):
    require(det(a) == 1, "Expected determinant one")
    return ((a[1][1], -a[0][1]), (-a[1][0], a[0][0]))


def e(j):
    require(type(j) is int and j >= 0, "Index must be a natural integer")
    return ((1 + 4 * j, 2), (-8 * j * j, 1 - 4 * j))


def phi(word):
    require(type(word) is str and all(c in TOP_CODES for c in word),
            "Unknown word letter")
    out = I2
    for c in word:
        out = mul(out, e(TOP_CODES[c]))
    return out


def block(a, b):
    return ((a[0][0], a[0][1], 0, 0),
            (a[1][0], a[1][1], 0, 0),
            (0, 0, b[0][0], b[0][1]),
            (0, 0, b[1][0], b[1][1]))


def table():
    raw = (ROOT / "data/u15_table.json").read_bytes()
    require(hashlib.sha256(raw).hexdigest() == TABLE_SHA256, "Table hash mismatch")
    result = json.loads(raw)
    require(set(result) == {q + a for q in STATES for a in BITS}, "Table domain")
    require([k for k, v in result.items() if v is None] == ["J1"], "Halting cell")
    for key, row in result.items():
        if row is not None:
            require(type(row) is list and len(row) == 3, "Malformed transition")
            require(type(row[0]) is int and row[0] in (0, 1)
                    and row[1] in ("L", "R") and row[2] in STATES,
                    "Malformed transition fields")
    return result


def rewriting_rules():
    result = []

    def add(lhs, rhs, kind, **metadata):
        require(lhs and rhs and set(lhs + rhs) <= set(ALPHABET), "Rule alphabet")
        result.append(dict(id=len(result) + 1, lhs=lhs, rhs=rhs,
                           kind=kind, **metadata))

    transitions = table()
    for q in STATES:
        for a in BITS:
            row = transitions[q + a]
            if row is None:
                continue
            b, direction, p = str(row[0]), row[1], row[2]
            for c in BITS:
                if direction == "R":
                    lhs, rhs = q + a + c, b + p + c
                else:
                    lhs, rhs = c + q + a, p + c + b
                add(lhs, rhs, "transition", cell=q + a, context=c)
            if direction == "R":
                lhs, rhs = q + a + "]", b + p + "0]"
            else:
                lhs, rhs = "[" + q + a, "[" + p + "0" + b
            add(lhs, rhs, "transition", cell=q + a, context="boundary")
    add("J1", "X", "halt")
    for a in BITS:
        add(a + "X", "X", "cleanup_left")
        add("X" + a, "X", "cleanup_right")
    add("[X]", "X", "finish")
    require(len(result) == 93, "Rule census")
    require(len({(r["lhs"], r["rhs"]) for r in result}) == len(result),
            "Duplicate rules")
    return result


def inner_tiles(rules=None):
    rules = rewriting_rules() if rules is None else rules
    result = []

    def add(h, g, kind, **metadata):
        result.append(dict(id=len(result) + 1, h=h, g=g, kind=kind, **metadata))

    for a in ALPHABET:
        add(a, a, "copy", letter=a)
    for r in rules:
        add(r["rhs"], r["lhs"], "rewrite", rule_id=r["id"])
    add(SEPARATOR, SEPARATOR, "separator")
    require(len(result) == 114, "Tile census")
    return result


def compile_packet():
    rules = rewriting_rules()
    tiles = inner_tiles(rules)
    generators = []
    for tile in tiles:
        i = tile["id"]
        generators.append(dict(name=f"A{i}", tile_id=i,
                               matrix=block(phi(tile["h"]), e(i))))
    for tile in tiles:
        i = tile["id"]
        lower = mul(mul(inv(P), inv(e(i))), P)
        generators.append(dict(name=f"B{i}", tile_id=i,
                               matrix=block(inv(phi(tile["g"])), lower)))
    generators.append(dict(name="C", matrix=block(inv(phi(TERMINAL + SEPARATOR)), P)))
    matrices = [g["matrix"] for g in generators]
    require(len(matrices) == len(set(matrices)) == 229, "Distinct generator census")
    entries = [v for matrix in matrices for row in matrix for v in row]
    maximum = max(abs(v) for v in entries)
    ledger = dict(states=15, tape_symbols=2, defined_transitions=29,
                  undefined_halting_cells=["J1"], alphabet_size=len(ALPHABET),
                  top_alphabet_size=len(TOP_CODES), transition_rules=87,
                  halt_rules=1, cleanup_rules=4, finish_rules=1,
                  rules=len(rules), copy_tiles=len(ALPHABET),
                  rewrite_tiles=len(rules), separator_tiles=1,
                  inner_tiles=len(tiles), generators=len(generators),
                  maximum_absolute_generator_entry=maximum,
                  maximum_generator_entry_magnitude_bits=maximum.bit_length(),
                  sum_generator_entry_magnitude_bits=sum(abs(v).bit_length() for v in entries),
                  nonzero_generator_entries=sum(v != 0 for v in entries),
                  matrix_dimension=4, all_determinants=1,
                  input_word_length="len(left)+len(right)+4",
                  target_word_length="len(left)+len(right)+5",
                  encoder_2x2_multiplications="len(left)+len(right)+5",
                  target_entry_magnitude_bit_bound="12*(len(left)+len(right)+5)+1",
                  bit_bound_note="Conservative: max row-sum norm of E_j for 1<=j<=21 is 3611<2^12")
    return dict(schema="fixed-u15-sl4-semigroup-v1", table_sha256=TABLE_SHA256,
                alphabet=ALPHABET, terminal=TERMINAL, separator=SEPARATOR,
                top_codes=TOP_CODES, rules=rules, tiles=tiles,
                generators=generators, ledger=ledger)


def from_tape(left, right):
    """Finite halves are nearest-head first; start A scans blank zero.

    Cells -i-1 contain left[i]; cells i+1 contain right[i]. Every unlisted
    tape cell is zero. Leading/trailing zero padding is allowed.
    """
    require(type(left) is str and type(right) is str and
            set(left + right) <= set(BITS), "Tape halves must be binary strings")
    word = "[" + left[::-1] + "A0" + right + "]"
    return dict(left_nearest_first=left, right_nearest_first=right,
                configuration_word=word, target=target_from_word(word))


def target_from_word(word):
    require(type(word) is str and set(word) <= set(ALPHABET), "Bad input word")
    return block(inv(phi(word + SEPARATOR)), P)


def rewrite_occurrences(word, rules=None):
    rules = rewriting_rules() if rules is None else rules
    for rule in rules:
        pos = word.find(rule["lhs"])
        while pos >= 0:
            yield rule["id"], pos, word[:pos] + rule["rhs"] + word[pos + len(rule["lhs"]):]
            pos = word.find(rule["lhs"], pos + 1)


def derivation_to_tiles(start_word, steps, packet=None):
    """Compile checked (rule_id,offset) directed steps to an inner-tile witness."""
    packet = compile_packet() if packet is None else packet
    copies = {t["letter"]: t["id"] for t in packet["tiles"] if t["kind"] == "copy"}
    rewrite = {t["rule_id"]: t["id"] for t in packet["tiles"] if t["kind"] == "rewrite"}
    rules = {r["id"]: r for r in packet["rules"]}
    separator = packet["tiles"][-1]["id"]
    word, sequence = start_word, []
    for rid, pos in steps:
        require(type(rid) is int and rid in rules and type(pos) is int and pos >= 0,
                "Bad derivation step")
        rule = rules[rid]
        require(word[pos:pos + len(rule["lhs"])] == rule["lhs"], "Inapplicable step")
        sequence.extend(copies[a] for a in word[:pos])
        sequence.append(rewrite[rid])
        sequence.extend(copies[a] for a in word[pos + len(rule["lhs"]):])
        sequence.append(separator)
        word = word[:pos] + rule["rhs"] + word[pos + len(rule["lhs"]):]
    require(word == TERMINAL, "Derivation does not end at X")
    return sequence


def tiles_to_product(sequence):
    require(all(type(i) is int and 1 <= i <= 114 for i in sequence), "Bad tile IDs")
    return [f"A{i}" for i in sequence] + ["C"] + [f"B{i}" for i in reversed(sequence)]


def save_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def main():
    # Output is a total finite integer serialization, subject only to resources.
    # Python's optional decimal-digit guard must not reject long valid tapes.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build = sub.add_parser("build")
    build.add_argument("--output", default=str(ROOT / "data/semigroup.json"))
    target = sub.add_parser("target")
    target.add_argument("--left", default="")
    target.add_argument("--right", default="")
    args = parser.parse_args()
    if args.command == "build":
        packet = compile_packet()
        save_json(args.output, packet)
        save_json(ROOT / "data/ledger.json", packet["ledger"])
        lines = ["Literal fixed generator list in row-major order; all entries are integers.",
                 "Ordering: A1,...,A114,B1,...,B114,C. No inverses are adjoined.", ""]
        for generator in packet["generators"]:
            lines.append(generator["name"])
            lines.extend(" ".join(str(value) for value in row)
                         for row in generator["matrix"])
            lines.append("")
        (ROOT / "data/matrices.txt").write_text("\n".join(lines))
        print(json.dumps(packet["ledger"], indent=2, sort_keys=True))
    else:
        print(json.dumps(from_tape(args.left, args.right), indent=2))


if __name__ == "__main__":
    main()
