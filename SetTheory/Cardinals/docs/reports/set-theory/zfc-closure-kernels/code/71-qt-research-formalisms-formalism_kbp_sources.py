#!/usr/bin/env python3
"""1296 fine-source controls for the independently certified K/B/Peirce basis.

These consume no fourth AX parameter.  Exact source and table verification
requires the corresponding changed command codec and twelve-push contract.
No binary state bound is asserted by this emitter.
"""
import hashlib
import itertools
import json
import argparse
from pathlib import Path
import formalism_fusions as common

d = common.d
ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--peirce-f", action="store_true",
                        help="use ((p->F)->p)->p; EFQ is derived from K,B,rho6")
    args = parser.parse_args()
    spec = d.load_spec()
    old = spec["ax_rows"]("a", "old_cache", "b", "c", "u")
    oldbundle = spec["bundle"]("a", "b", "c")
    redexes = d.redexes(oldbundle)
    fine = json.loads((common.BASE / "macro_to_fine.json").read_text())
    C = d.imp
    bases = {
        "K": C("a", C("b", "a")),
        "B": C(C("a", "b"), C(C("b", "c"), C("a", "c"))),
        "P": C(C(C("a", "b"), "a"), "a"),
    }
    if args.peirce_f:
        bases["P"] = C(C(C("a", 1), "a"), "a")
    variants = []
    hashes = set()
    maps = list(itertools.permutations("abc"))
    for ordering in itertools.permutations("KBP"):
        for labels in itertools.product(maps, repeat=3):
            mappings = {basis: dict(zip("abc", images)) for basis, images in zip("KBP", labels)}
            roots = [common.rewrite_labels(bases[x], mappings[x]) for x in ordering] + old[2:]
            for mask in (32,):
                bundle = d.normalize(oldbundle,
                    {p for i, p in enumerate(redexes) if mask & (1 << i)})
                word = [166, 121, 180, 176]
                word += [m for formula in roots for m in d.emit(formula)]
                word += d.emit(bundle) + d.TAIL
                stack, events = d.execute_macros(word[:-len(d.TAIL)])
                assert stack == ["old_top", old[0]] + roots + [bundle]
                assert events == [(176, 2)] and 158 not in word
                text = "".join(fine[str(m)] for m in word)
                sha = hashlib.sha256(text.encode()).hexdigest()
                if sha in hashes:
                    continue
                hashes.add(sha)
                variants.append({"id": len(variants), "basis_order": ordering,
                    "independent_label_images": dict(zip("KBP", labels)), "DNE_mask": mask,
                    "AX_stack_pushes": 12, "logical_rows": 10,
                    "AX_reads": ["selector", "additive_a", "additive_b"],
                    "rows": [old[0]] + roots, "bundle": bundle, "word": word,
                    "fine_AX": text, "fine_length": len(text),
                    "fine_sha256": sha})
    assert len(variants) == (648 if args.peirce_f else 1296)
    prefix = "formalism_kbpf_sources" if args.peirce_f else "formalism_kbp_sources"
    result = {"status": "PASS_SYMBOLIC_SOURCE_ONLY",
              "scope": "Changed three-field AX codec; no binary state bound",
              "positive_basis_certificate": ("formalism_kbpf_proof.txt" if args.peirce_f
                                             else "formalism_kbp_proof.txt"),
              "auxiliary_EFQ": ("Derived from K, B and unchanged rho6" if args.peirce_f
                                 else None),
              "variants": variants}
    (ROOT / (prefix + ".json")).write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print(json.dumps({"variants": len(variants), "min_fine_length": min(v["fine_length"] for v in variants),
                      "max_fine_length": max(v["fine_length"] for v in variants)}, indent=2))


if __name__ == "__main__":
    main()
