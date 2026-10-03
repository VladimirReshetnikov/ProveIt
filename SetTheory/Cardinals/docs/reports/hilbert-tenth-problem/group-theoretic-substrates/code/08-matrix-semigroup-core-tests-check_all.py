#!/usr/bin/env python3
"""Independent-semantics checks for the locally authored matrix construction."""
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import compiler as c


def check(ok, message):
    if not ok:
        raise AssertionError(message)


def mm(a, b):
    n = len(a)
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(n))
                       for j in range(n)) for i in range(n))


def identity(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def determinant(a):
    # Independent exact Leibniz determinant, 24 terms at dimension four.
    value = 0
    for p in itertools.permutations(range(len(a))):
        parity = sum(p[i] > p[j] for i in range(len(a)) for j in range(i + 1, len(a)))
        term = -1 if parity % 2 else 1
        for i, j in enumerate(p):
            term *= a[i][j]
        value += term
    return value


def words(max_length):
    return ["".join(w) for n in range(max_length + 1)
            for w in itertools.product("01", repeat=n)]


def independent_table():
    compact = "0RB1RA_1RC1RA_0LG0LE_0LF1LE_1RA1LD_1LD1LD_0LH1LG_1LI1LG_0RA1LJ_1LK---_0RL1RN_0RM1RL_0LB1RL_0LC0RO_0RN1RN"
    result = {}
    for state, pair in zip("ABCDEFGHIJKLMNO", compact.split("_")):
        for read in range(2):
            entry = pair[3 * read:3 * read + 3]
            result[state + str(read)] = None if entry == "---" else [int(entry[0]), entry[1], entry[2]]
    return result


TABLE = independent_table()


def word_oracle(word):
    """List tape model, independently implementing one U15 move."""
    check(word[0] == "[" and word[-1] == "]", "Configuration boundaries")
    positions = [i for i, a in enumerate(word) if a in "ABCDEFGHIJKLMNO"]
    check(len(positions) == 1, "Unique state")
    at = positions[0]
    state = word[at]
    tape = list(word[1:at] + word[at + 1:-1])
    head = at - 1
    row = TABLE[state + tape[head]]
    if row is None:
        return word[:at] + "X" + word[at + 2:]
    write, direction, next_state = row
    tape[head] = str(write)
    head += 1 if direction == "R" else -1
    if head < 0:
        tape.insert(0, "0")
        head = 0
    if head == len(tape):
        tape.append("0")
    return "[" + "".join(tape[:head]) + next_state + "".join(tape[head:]) + "]"


def marker_pattern(word):
    if word.count("C") != 1:
        return False
    split = word.index("C")
    left, right = word[:split], word[split + 1:]
    return (all(v.startswith("A") for v in left)
            and right == tuple("B" + v[1:] for v in reversed(left)))


def check_marker_exhaustive(generators, depth=8):
    symbols = ("A1", "A2", "B1", "B2", "C")
    lower = {name: tuple(tuple(generators[name][i][j] for j in (2, 3)) for i in (2, 3))
             for name in symbols}
    count, accepting = 0, 0

    def walk(word, matrix):
        nonlocal count, accepting
        count += 1
        accepted = matrix == c.P
        check(accepted == marker_pattern(word), "Marker normal form failed: " + str(word))
        accepting += accepted
        if len(word) < depth:
            for name in symbols:
                walk(word + (name,), mm(matrix, lower[name]))

    walk((), identity(2))
    return dict(tile_indices=[1, 2], maximum_generator_word_length=depth,
                tested_words=count, words_equal_to_marker=accepting)


def main():
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    packet = c.compile_packet()
    saved = json.loads((ROOT / "data/semigroup.json").read_text())
    check(json.loads(json.dumps(packet)) == saved, "Saved numerical packet differs from compiler")
    check(c.table() == TABLE, "Independent table transcription disagrees")
    matrices = {g["name"]: tuple(tuple(row) for row in g["matrix"])
                for g in packet["generators"]}
    for name, matrix in matrices.items():
        check(determinant(matrix) == 1, "Not SL4: " + name)
    check(len(set(matrices.values())) == 229, "Duplicate numerical generators")
    # Conjugacy formula uses an independently powered lower shear.
    for j in range(115):
        qj = ((1, 0), (2 * j, 1))
        qi = ((1, 0), (-2 * j, 1))
        check(c.e(j) == mm(mm(qi, ((1, 2), (0, 1))), qj), "Conjugacy formula")
    local_cases = 0
    for left in words(3):
        for right in words(3):
            for state in "ABCDEFGHIJKLMNO":
                for read in "01":
                    before = "[" + left + state + read + right + "]"
                    found = list(c.rewrite_occurrences(before, packet["rules"]))
                    check(len(found) == 1, "Ordinary configuration not deterministic")
                    check(found[0][2] == word_oracle(before), "Machine/rewrite mismatch")
                    local_cases += 1
    cleanup_start_cases, cleanup_edges = 0, 0
    for left in words(3):
        for right in words(3):
            pending, seen = ["[" + left + "X" + right + "]"], set()
            while pending:
                word = pending.pop()
                if word in seen:
                    continue
                seen.add(word)
                following = list(c.rewrite_occurrences(word, packet["rules"]))
                if not following:
                    check(word == "X", "Bad terminal cleanup word")
                for rid, _, after in following:
                    check(len(after) < len(word), "Nondecreasing cleanup")
                    check(packet["rules"][rid - 1]["kind"].startswith("cleanup")
                          or packet["rules"][rid - 1]["kind"] == "finish", "Foreign cleanup step")
                    cleanup_edges += 1
                    pending.append(after)
            check("X" in seen, "Cleanup missing terminal")
            cleanup_start_cases += 1
    # Every short valid A/0 start is compared step-for-step for a bounded prefix.
    simulations, total_prefix_steps, observed_halts, max_steps = 0, 0, 0, 300
    for left in words(3):
        for right in words(3):
            word = c.from_tape(left, right)["configuration_word"]
            for step in range(max_steps):
                expected = word_oracle(word)
                found = list(c.rewrite_occurrences(word, packet["rules"]))
                check(len(found) == 1 and found[0][2] == expected, "Simulation mismatch")
                total_prefix_steps += 1
                word = expected
                if "X" in word:
                    observed_halts += 1
                    break
            simulations += 1
    # Fully materialized accepting main-interface witness, including matrix product.
    loaded = c.from_tape("011", "")
    start, word = loaded["configuration_word"], loaded["configuration_word"]
    steps, derivation = [], [word]
    for _ in range(100):
        if word == "X":
            break
        found = list(c.rewrite_occurrences(word, packet["rules"]))
        check(found, "Accepting example blocked")
        rid, at, word = found[0]
        steps.append((rid, at))
        derivation.append(word)
    check(word == "X", "Example did not halt within explicitly bounded test")
    sequence = c.derivation_to_tiles(start, steps, packet)
    tile_map = {tile["id"]: tile for tile in packet["tiles"]}
    hword = "".join(tile_map[i]["h"] for i in sequence)
    gword = "".join(tile_map[i]["g"] for i in sequence)
    check(start + "#" + hword == gword + "X#", "Constrained correspondence mismatch")
    names = c.tiles_to_product(sequence)
    product = identity(4)
    for name in names:
        product = mm(product, matrices[name])
    check(product == loaded["target"], "Literal accepting product does not hit target")
    witness = dict(input=loaded, rewrite_steps=steps, derivation=derivation,
                   inner_tile_sequence=sequence, generator_word=names,
                   product=product, rewrite_step_count=len(steps),
                   tile_count=len(sequence), generator_word_length=len(names))
    c.save_json(ROOT / "evidence/accepting-witness.json", witness)
    check(c.target_from_word("X") == matrices["C"], "Zero-step terminal witness")
    check(c.derivation_to_tiles("X", [], packet) == [], "Zero-step tile witness")
    # Malformed encoders and source words are rejected even under python -O.
    invalid_count = 0
    for args in ((None, ""), ("", 1), ("2", ""), ("", "x"), (True, "0")):
        try:
            c.from_tape(*args)
        except ValueError:
            invalid_count += 1
        else:
            raise AssertionError("Invalid input accepted")
    for word in ("#", "A#0", None):
        try:
            c.target_from_word(word)
        except ValueError:
            invalid_count += 1
        else:
            raise AssertionError("Bad target word accepted")
    random_cases = 100
    rng = random.Random(20261003)
    for _ in range(random_cases):
        left = "".join(rng.choice("01") for _ in range(rng.randrange(200)))
        right = "".join(rng.choice("01") for _ in range(rng.randrange(200)))
        item = c.from_tape(left, right)
        upper = tuple(tuple(item["target"][i][j] for j in range(2)) for i in range(2))
        check(mm(upper, c.phi(item["configuration_word"] + "#")) == identity(2), "Target inverse order")
        check(max(abs(v).bit_length() for row in item["target"] for v in row)
              <= 12 * (len(left) + len(right) + 5) + 1, "Encoder bit bound")
    marker = check_marker_exhaustive(matrices)
    # Exercise the standalone CLI beyond Python's default 4,300-digit guard.
    long_left = "01" * 4096
    cli = subprocess.run([sys.executable, str(ROOT / "compiler.py"), "target",
                          "--left", long_left, "--right", ""],
                         text=True, capture_output=True, check=True)
    long_packet = json.loads(cli.stdout)
    check(long_packet == json.loads(json.dumps(c.from_tape(long_left, ""))),
          "Long-input standalone CLI serialization mismatch")
    result = dict(status="pass", optimization_mode=not __debug__,
                  independent_table_cells=30, determinant_checks=229,
                  local_machine_rewrite_cases=local_cases,
                  cleanup_start_cases=cleanup_start_cases, cleanup_edges=cleanup_edges,
                  bounded_simulation_inputs=simulations,
                  maximum_prefix_steps_per_input=max_steps,
                  compared_prefix_steps=total_prefix_steps,
                  observed_halts=observed_halts,
                  nonhalting_caveat="Failure to halt in a tested prefix is not evidence of nonhalting",
                  accepting_witness=dict(rewrite_steps=len(steps), inner_tiles=len(sequence),
                                         generator_word_length=len(names)),
                  marker_exhaustion=marker, invalid_inputs_rejected=invalid_count,
                  random_encoder_cases=random_cases,
                  long_cli_input_bits=len(long_left),
                  long_cli_output_bytes=len(cli.stdout.encode()),
                  semigroup_json_sha256=hashlib.sha256((ROOT / "data/semigroup.json").read_bytes()).hexdigest())
    c.save_json(ROOT / ("evidence/tests-optimized.json" if not __debug__ else "evidence/tests.json"), result)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
