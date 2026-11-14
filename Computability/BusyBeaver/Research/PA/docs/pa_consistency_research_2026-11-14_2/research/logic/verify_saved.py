#!/usr/bin/env python3
"""Regenerate frozen search inputs and check saved best grammar token words.

This validates preparation and reassociation only, not physical execution or
the changed proof-word compiler. It performs no stochastic search.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
NAMES = {
    "node58": "H", "node55": "D", "node70": "A", "node65": "C",
    "node49": "P", "node72": "readH", "node75": "readDcons",
    "node142": "guardcopy", "node150": "guardcmp",
}


def word(path):
    obj = json.loads(path.read_text())
    rules = obj["rules"]

    def walk(x):
        if isinstance(x, list):
            assert x in [["leaf", "inc", 1], ["leaf", "breakTo", 1]]
            return ["+" if x[1] == "inc" else "close"]
        if x == "node60":
            return ["+", "+"]
        if x == "node61":
            return ["+"] * 4
        if x in rules:
            return walk(rules[x][0]) + walk(rules[x][1])
        return [NAMES[x]]

    return walk(obj["root"])


def main():
    assert __debug__, "Do not run with Python -O."
    files = ["brouwer_inputs.txt", "brouwer_variants.json",
             "brouwer_explosion_inputs.txt", "brouwer_explosion_variants.json",
             "logic_anneal.cpp", "brouwer_explosion.cpp", "screen.cpp", "leaf_attrs.txt"]
    regenerated = []
    with tempfile.TemporaryDirectory(prefix="pa_logic_replay_") as name:
        temp = Path(name)
        shutil.copytree(HERE / "upstream", temp / "upstream")
        for script in ["make_brouwer.py", "make_brouwer_explosion.py"]:
            shutil.copy2(HERE / script, temp / script)
            subprocess.run([sys.executable, "-B", str(temp / script)], check=True,
                           capture_output=True, text=True)
        for file in files:
            assert (temp / file).read_bytes() == (HERE / file).read_bytes(), file
            regenerated.append({"file": file, "sha256": hashlib.sha256((HERE / file).read_bytes()).hexdigest()})
    best = []
    for grammar, variants, count in [
        ("brouwer.best.grammar.json", "brouwer_variants.json", 190),
        ("bexp.best.grammar.json", "brouwer_explosion_variants.json", 194),
    ]:
        tokens = word(HERE / grammar)
        assert len(tokens) == count
        matches = [x["id"] for x in json.loads((HERE / variants).read_text()) if x["tokens"] == tokens]
        assert matches, grammar
        best.append({"grammar": grammar, "macro_tokens": count, "matching_variant_ids": matches})
    print(json.dumps({"status": "PASS", "regenerated_files": regenerated, "saved_best_grammars": best,
                      "boundary": "Exact preparation and macro-word preservation. No physical or all-store proof-compiler verification."}, indent=2))


if __name__ == "__main__":
    main()
