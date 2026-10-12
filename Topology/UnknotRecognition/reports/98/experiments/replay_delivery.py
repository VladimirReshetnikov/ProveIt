"""Replay saved graph proofs against their separate source example files.

Run from the delivery root with PYTHONPATH=src. This checks graph semantics,
not geometric provenance, ball status, or a knot verdict.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from checker import verify_packet, verify_coloring_recipe
from coloring import color_at
from report91_adapter import translate
from gauge_cuts import compile_grammar


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def check_address(grammar: dict, recipe: dict, address: dict) -> tuple[int, int, int]:
    """Resolve one actual source occurrence, not an aliased grammar rule."""
    node = len(grammar["nodes"]) - 1
    for branch in address["path"]:
        current = grammar["nodes"][node]
        if current["op"] == "leaf" or type(branch) is not int:
            raise ValueError("invalid occurrence path")
        if not 0 <= branch < len(current["children"]):
            raise ValueError("invalid child occurrence")
        node = current["children"][branch]
    leaf = grammar["nodes"][node]
    if leaf["op"] != "leaf":
        raise ValueError("address does not end at a leaf")
    edge = address["leaf_edge"]
    if type(edge) is not int or not 0 <= edge < len(leaf["edges"]):
        raise ValueError("invalid leaf edge index")
    u, v, capacity = leaf["edges"][edge]
    return (color_at(recipe, address["path"], u),
            color_at(recipe, address["path"], v), capacity)


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    out: dict[str, Any] = {"complete_packets": {}, "positive_recipes": {}}
    for path in sorted((root / "data").glob("*_certificate.json")):
        stem = path.name.removesuffix("_certificate.json")
        source = read_json(root / "examples" / (stem + ".json"))
        out["complete_packets"][stem] = verify_packet(read_json(path), source)
    for path in sorted((root / "data").glob("*_coloring.json")):
        stem = path.name.removesuffix("_coloring.json")
        source = read_json(root / "examples" / (stem + ".json"))
        out["positive_recipes"][stem] = verify_coloring_recipe(read_json(path), source)

    grammar = read_json(root / "examples/prism.json")
    recipe = read_json(root / "data/prism_coloring.json")
    verified = verify_coloring_recipe(recipe, grammar)
    obstruction = read_json(root / "data/prism_obstruction.json")
    keys = [(tuple(a["path"]), a["leaf_edge"]) for a in obstruction["cut_edges"]]
    if len(set(keys)) != len(keys):
        raise ValueError("duplicate cut occurrence")
    cost = 0
    for addr in obstruction["cut_edges"]:
        a, b, weight = check_address(grammar, recipe, addr)
        if a == b or weight != addr["capacity"]:
            raise ValueError("invalid cut address")
        cost += weight
    if cost != verified["root_row"][0] or cost > grammar["k"]:
        raise ValueError("incomplete cut edge inventory")
    if len(obstruction["mark_edges"]) != 2:
        raise ValueError("both marks must be witnessed")
    for color, addr in enumerate(obstruction["mark_edges"]):
        a, b, _ = check_address(grammar, recipe, addr)
        if a != color or b != color:
            raise ValueError("incorrect mark witness")
    out["prism_obstruction"] = {"checked": True, "cost": cost,
                                  "cut_edges": len(keys), "mark_edges": 2}

    original = read_json(root / "examples/report91_triangular_prism.json")
    translated = translate(original, 3)
    out["report91_fixture"] = verify_packet(compile_grammar(translated), translated)
    out["scope"] = "saved graph proof replay; no geometric or knot claim"
    (root / "data/delivery_replay.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
