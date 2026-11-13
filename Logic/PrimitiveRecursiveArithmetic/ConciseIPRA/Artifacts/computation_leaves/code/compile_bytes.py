"""Untrusted trace translator: four-field supply certificates to axiom leaves.

The supported inputs are successful integer/list compact477 certificates.
Arithmetic parameters allocated by discarded supplies are specialized to zero.
The trusted checker imports none of this module.
"""
import copy
import json
from pathlib import Path


def opener(scope):
    def opening(tree, image=None, depth=0):
        if type(tree) is list:
            return [opening(child, image, depth + 5 - len(tree)) for child in tree]
        if type(tree) is not int:
            raise TypeError("the translator supports exact integer/list syntax")
        if scope <= tree < depth:
            return tree
        # This is the eager compact477 opener: even depths also check image.
        return depth % 2 * opening(image, depth=3)
    return opening


def map_parameters(tree, names):
    if type(tree) is list:
        return [map_parameters(child, names) for child in tree]
    return names.get(tree, tree) if tree < 0 else tree


def computation(goal, scope):
    """Recognize the constructed computation schema, returning its packet."""
    if type(goal) is not list or len(goal) != 2:
        return None
    left = goal[0]
    if type(left) is not list or len(left) != 3:
        return None
    counter, seed, body = left
    if counter == 0:
        source = 0
    elif type(counter) is list and len(counter) == 1 and counter[0]:
        source = counter[0]
    else:
        return None
    i = opener(scope)
    try:
        expected = [[source and [source], seed, body],
                    i(body, [source, seed, body], 3) if source else seed]
    except (TypeError, ValueError, RecursionError):
        return None
    return [[], source, seed, body] if expected == goal else None


def extract(certificate):
    data = copy.deepcopy(certificate)
    goal, floor = data.pop()
    statistics = {"packets": 0, "supplies": 0, "hypotheses": 0}

    def check(context, target, scope):
        i = opener(scope)
        normalized = i(target)
        for formula, origin in reversed(context):
            if normalized == formula:
                statistics["hypotheses"] += 1
                return {"kind": "hyp", "goal": target, "scope": scope,
                        "origin": origin}
        packet = data.pop()
        statistics["packets"] += 1
        major, source, seed, body = packet
        major_proof = check(context, major, scope)
        active_target = target
        if major:
            hypothesis = major * 3
            kind = "major"
        elif seed:
            hypothesis = [[source and [source], seed, body],
                          i(body, [source, seed, body], 3) if source else seed]
            kind = "supply"
            statistics["supplies"] += 1
        else:
            active_target = i(*active_target, body, 2)
            hypothesis = active_target
            kind = "intro"
        new_scope = scope - 1
        i = opener(new_scope)
        retained = i(hypothesis, bool(major or 3 % len(active_target)) * new_scope)
        origin = {"kind": kind, "formula": retained}
        selected = i(body, source)  # eager in the upstream lambda profile
        if (major, active_target) != (source and [source, seed] or [body] * 3,
                                     i(body, seed)):
            selected = active_target
        continuation_goal = i(selected, [new_scope])
        continuation = check(context + [(retained, origin)], continuation_goal,
                             new_scope)
        return {"kind": kind, "goal": target, "scope": scope,
                "packet": packet, "major": major_proof,
                "continuation": continuation}

    proof = check([([], {"kind": "neutral"})], goal, floor)
    return proof, goal, floor, statistics


def compile_proof(proof, goal, floor):
    statistics = {"packets": 0, "leaves": 0, "discarded_supplies": 0,
                  "hypotheses": 0}

    def emit(node, context, target, scope, names):
        i = opener(scope)
        if i(target) in context:
            statistics["hypotheses"] += 1
            return []
        leaf = computation(target, scope)
        if leaf is not None:
            statistics["packets"] += 1
            statistics["leaves"] += 1
            return [leaf]
        if node["kind"] == "hyp":
            raise ValueError("an eliminated supply did not reconstruct as a leaf")
        updated = dict(names)
        old_fresh = node["scope"] - 1
        if node["kind"] == "supply":
            updated[old_fresh] = 0
            statistics["discarded_supplies"] += 1
            return emit(node["continuation"], context, target, scope, updated)
        new_scope = scope - 1
        updated[old_fresh] = new_scope
        packet = map_parameters(node["packet"], updated)
        major, source, seed, body = packet
        major_stream = emit(node["major"], context, major, scope, updated)
        active_target = target
        if major:
            hypothesis = major * 3
        else:
            active_target = i(*active_target, body, 2)
            hypothesis = active_target
        i = opener(new_scope)
        retained = i(hypothesis, bool(major or 3 % len(active_target)) * new_scope)
        selected = i(body, source)
        if (major, active_target) != (source and [source, seed] or [body] * 3,
                                     i(body, seed)):
            selected = active_target
        next_goal = i(selected, [new_scope])
        continuation_stream = emit(node["continuation"], context + [retained],
                                   next_goal, new_scope, updated)
        statistics["packets"] += 1
        return [packet] + major_stream + continuation_stream

    stream = emit(proof, [[]], goal, floor, {})
    return list(reversed(stream)) + [[goal, floor]], statistics


def convert(certificate):
    proof, goal, floor, extracted = extract(certificate)
    result, compiled = compile_proof(proof, goal, floor)
    return result, {"extracted": extracted, "compiled": compiled}


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("target", type=Path)
    args = parser.parse_args()
    result, statistics = convert(json.loads(args.source.read_text()))
    args.target.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print(json.dumps(statistics, indent=2))
