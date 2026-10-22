#!/usr/bin/env python3
"""Reproduce a small independent audit of the closed binary-tag formulas.

This script contains a self-contained toy model. It does not import, download,
or execute repository code. It compares literal bit-word construction with the
finite-sum formulas used in effective_tag91_recipe.txt, sections 4 and 5.
Run: python3 tag91_closed_formula_toy_audit.py
"""
import json


def geom(base, count):
    """Finite geometric sum, including the empty sum."""
    return (base ** count - 1) // (base - 1)


def content(bits, base=3):
    result = 0
    for bit in reversed(bits):
        result = result * base + bit
    return result


def audit():
    alphabet_size = 3
    letter_width = 8
    deletion = 16
    production_bound = 3
    rows = 1 + (2 * production_bound * (letter_width + 1) + 1) * (deletion - 1)
    appendant_length = rows * deletion
    productions = [[0, 2], [0], [2, 0, 2]]

    def encode_letter(letter):
        return ([0] * (2 * (letter + 1)) + [1]
                + [0] * (letter_width - 2 * (letter + 1)))

    tracks = []
    for phase in range(deletion):
        if phase % 2:
            track = [0] * rows
        elif deletion - 2 * alphabet_size <= phase and phase + 2 <= deletion:
            letter = (deletion - phase) // 2 - 1
            if letter == 1:
                track = [0] * rows
            else:
                track = [bit for y in productions[letter] for bit in encode_letter(y)][1:]
                track += [1] * (rows - len(track))
        else:
            track = [1] * rows
        tracks.append(track)
    appendant = [tracks[phase][row]
                 for row in range(rows) for phase in range(deletion)]

    # Independent finite-sum calculation, without constructing tracks.
    base = 3 ** deletion
    appendant_formula = geom(base, rows) * geom(9, deletion // 2 - alphabet_size)
    for letter, production in enumerate(productions):
        if letter == 1:
            continue
        prefix_length = len(production) * (letter_width + 1) - 1
        value = base ** prefix_length * geom(base, rows - prefix_length)
        value += sum(base ** (j * (letter_width + 1) + 2 * (y + 1) - 1)
                     for j, y in enumerate(production))
        appendant_formula += 3 ** (deletion - 2 * (letter + 1)) * value

    initial_letters = [0, 2, 2, 0]
    initial_word = []
    for letter in initial_letters:
        for token in encode_letter(letter):
            initial_word.extend(appendant if token else [0])
    initial_formula = sum(
        appendant_formula * 3 ** (j * (appendant_length + letter_width)
                                  + 2 * (letter + 1))
        for j, letter in enumerate(initial_letters))

    receipt = {
        "toyParameters": {
            "kA": alphabet_size,
            "L": letter_width,
            "b": deletion,
            "Rmax": production_bound,
            "sigma": rows,
            "a": appendant_length,
        },
        "appendantFormulaMatches": appendant_formula == content(appendant),
        "initialWordFormulaMatches": initial_formula == content(initial_word),
        "leadingBit": appendant[0],
        "wordLengthMatches":
            len(initial_word) == len(initial_letters) * (appendant_length + letter_width),
    }
    assert receipt["appendantFormulaMatches"]
    assert receipt["initialWordFormulaMatches"]
    assert receipt["leadingBit"] == 1
    assert receipt["wordLengthMatches"]
    return receipt


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))

