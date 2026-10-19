#!/usr/bin/env python3
"""Map every failed scanner premise to semantic grammar ancestry."""
from pathlib import Path
from functools import lru_cache
import argparse
import json


def run(reference, audit_path):
    source = json.loads((reference / "reference/grammar/closed-sequence-grammar-next22.json").read_text())
    symbols = json.loads((reference / "reference/grammar/semantic-symbols.json").read_text())
    encode = {v: k for k, v in symbols.items()}
    grammar = json.loads((reference / "grammar.json").read_text())
    rules = {word: (a, b) for word, a, b in grammar["rules"]}
    words = {int(q): "".join(encode[x] for x in word) for q, word in source["flattened_semantic_words"].items()}
    words.update({int(q): word for q, word in grammar.get("root_word_overrides", {}).items()})
    if "modified_AX_word" in grammar:
        words[76] = grammar["modified_AX_word"]
    by_ast = {int(index): words[int(q)] for q, index in source["sequence_ast_roots"].items()}

    @lru_cache(None)
    def changed(index):
        if index in by_ast and by_ast[index] in rules:
            return expand(by_ast[index])
        row = source["ast_dag"][index]
        if row[0] == "L":
            return "L", tuple(row[1]), "ast:" + str(index)
        return "N", changed(row[1]), changed(row[2]), "ast:" + str(index)

    @lru_cache(None)
    def expand(word):
        if len(word) == 1:
            tree = changed(source["atoms"][symbols[word]]["ast"])
            return tree[:-1] + (word + ":" + tree[-1],)
        a, b = rules[word]
        return "N", expand(a), expand(b), word

    root = changed(source["original_ast"])
    violations = json.loads(audit_path.read_text())["violations"]
    result = []
    for pc in sorted({row["pc"] for row in violations}):
        node, nodes = root, []
        for k, bit in enumerate(pc):
            assert node[0] == "N"
            nodes.append(dict(prefix=pc[:k], remaining=pc[k:], label=node[-1]))
            node = node[int(bit) + 1]
        assert node[0] == "L"
        chains = [nodes[k:] for k in range(len(pc) - 5) if pc[k:k + 6] == "000000"]
        assert chains
        result.append(dict(pc=pc, instruction=node[1], zero6_chains=chains,
                           trailing_zero6_chain=chains[-1]))
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--reference", required=True, type=Path)
    ap.add_argument("--audit", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    result = run(args.reference.resolve(), args.audit.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Mapped {len(result)} distinct offending source paths")


if __name__ == "__main__":
    main()
