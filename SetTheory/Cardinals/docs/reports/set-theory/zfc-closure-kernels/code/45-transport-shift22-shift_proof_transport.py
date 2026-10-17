#!/usr/bin/env python3
"""Exact bidirectional proof transport for the shift-only fixed-zero kernel.

The forward compiler derives arbitrary free-name substitutions by first
generalizing ALL distinct free names, then instantiating the universal
closure in reverse order at the desired names. No fresh intermediates are
needed in that forward construction: no original free name remains free
when instantiation begins. Arbitrary named GEN/UI use uniform shifts.

The reverse compiler derives unrestricted UI0 in the original source28
kernel using a fresh UI instance followed by whole-formula contraction.
All compilers are off-machine completeness witnesses. The target checker
performs only its ordinary fixed-zero quantifier rules, MP and two shifts.
"""
from __future__ import annotations

from copy import deepcopy

import four_kernel as old
import shift_kernel as new


class _Builder:
    def __init__(self, instructions=(), formulas=()):
        self.instructions = deepcopy(list(instructions))
        self.formulas = list(formulas)

    def emit(self, instruction, formula):
        self.instructions.append(instruction)
        self.formulas.append(formula)
        return len(self.instructions) - 1

    def shift(self, line, amount):
        if not new.integer(amount):
            raise ValueError("integer shift required")
        if not new.free_names(self.formulas[line]):
            return line
        op = "up" if amount >= 0 else "down"
        for _ in range(abs(amount)):
            line = self.emit({"op": op, "line": line}, new.rename_step(op, self.formulas[line]))
        return line

    def generalize(self, line, name):
        original = self.formulas[line]
        current = self.shift(line, -name)
        current = self.emit({"op": "gen_zero", "line": current},
                            new.All(new.close_name(self.formulas[current], 0)))
        current = self.shift(current, name)
        if self.formulas[current] != new.All(new.close_name(original, name)):
            raise AssertionError("shift-conjugated GEN changed binding")
        return current

    def ui(self, body, name):
        if not new.scoped(body, 1) or not new.integer(name):
            raise ValueError("bad UI body or target")
        moved = new.rename(body, lambda x: x - name)
        current = self.emit({"op": "ui_zero", "body": moved},
                            new.Imp(new.All(moved), new.open_body(moved, 0)))
        current = self.shift(current, name)
        if self.formulas[current] != new.Imp(new.All(body), new.open_body(body, name)):
            raise AssertionError("shift-conjugated UI changed binding")
        return current

    def substitute(self, line, mapping):
        original = self.formulas[line]
        live = sorted(new.free_names(original))
        if any(x not in mapping or not new.integer(mapping[x]) for x in live):
            raise ValueError("substitution must specify an integer image of every free name")
        if all(mapping[x] == x for x in live):
            return line
        current = line
        for name in live:
            current = self.generalize(current, name)
        if new.free_names(self.formulas[current]):
            raise AssertionError("universal closure left an original free name")
        for name in reversed(live):
            quantified = self.formulas[current]
            if quantified[0] != "all":
                raise AssertionError("missing universal closure binder")
            instance = self.ui(quantified[1], mapping[name])
            opened = self.formulas[instance][2]
            current = self.emit({"op": "mp", "implication": instance, "antecedent": current}, opened)
        if self.formulas[current] != new.rename(original, mapping.__getitem__):
            raise AssertionError("universal closure substitution was not simultaneous")
        return current

    def finish(self, line, theory):
        result = {"instructions": self.instructions[:line + 1]}
        if line >= 0:
            result["conclusion"] = self.formulas[line]
        checked = new.check_certificate(result, theory)
        if checked != self.formulas[:line + 1]:
            raise AssertionError("builder formulas did not match kernel reconstruction")
        return result


def substitute_certificate(certificate: dict, mapping: dict, *, line=None, theory=()):
    """Derive a simultaneous substitution of an already proved theorem.

    The map must cover all free names of the selected line; unused map keys
    are harmless. Returns a checked certificate and a small audit record.
    """
    theory = tuple(theory)
    formulas = new.check_certificate(certificate, theory)
    if line is None:
        line = len(formulas) - 1
    if not new.integer(line) or not 0 <= line < len(formulas):
        raise ValueError("select an existing theorem line")
    builder = _Builder(certificate["instructions"], formulas)
    target = builder.substitute(line, mapping)
    result = builder.finish(target, theory)
    return result, {"source_line": line, "source_free_names": sorted(new.free_names(formulas[line])),
                    "mapping": mapping, "old_lines": len(formulas),
                    "new_lines": len(result["instructions"]), "target_line": target}


def translate(certificate: dict, theory=(), *, source_kernel=None):
    """Sourcefour -> shift22; optionally pass the report's current24 kernel."""
    source = old if source_kernel is None else source_kernel
    theory = tuple(theory)
    original = source.check_certificate(certificate, theory)
    builder, line_map, trace = _Builder(), [], []
    for index, instruction in enumerate(certificate["instructions"]):
        op = instruction["op"]
        if op in source.RENAMINGS:
            source_line = instruction["line"]
            current = line_map[source_line]
            if op in new.RENAMINGS:
                current = builder.emit({"op": op, "line": current}, original[index])
            else:
                mapping = {x: source.name_step(op, x) for x in source.free_names(original[source_line])}
                current = builder.substitute(current, mapping)
            line_map.append(current)
            trace.append({"source_line": index, "source_op": op, "target_line": current})
        elif op == "gen":
            current = builder.generalize(line_map[instruction["line"]], instruction["name"])
            line_map.append(current)
        elif op == "fresh_ui":
            current = builder.ui(source.freeze(instruction["body"]), instruction["fresh"])
            line_map.append(current)
        else:
            copied = deepcopy(instruction)
            if op == "mp":
                copied["implication"] = line_map[copied["implication"]]
                copied["antecedent"] = line_map[copied["antecedent"]]
            line_map.append(builder.emit(copied, original[index]))
    expanded = new.check_certificate({"instructions": builder.instructions}, theory)
    if expanded != builder.formulas:
        raise AssertionError("expanded proof does not reconstruct predicted formulas")
    for i, j in enumerate(line_map):
        if original[i] != expanded[j]:
            raise AssertionError("forward exact line correspondence failed")
    target = line_map[-1] if line_map else -1
    result = builder.finish(target, theory)
    return result, {"old_lines": len(original), "expanded_lines": len(builder.instructions),
                    "new_lines": len(result["instructions"]), "line_map": line_map,
                    "line_map_scope": "full expanded proof, before final truncation",
                    "substitution_trace": trace}


def reverse_translate(certificate: dict, theory=()):
    """Shift22 -> originalsourcefour, deriving unrestricted UI with fresh UI."""
    theory = tuple(theory)
    original = new.check_certificate(certificate, theory)
    instructions, line_map = [], []
    for instruction in certificate["instructions"]:
        op = instruction["op"]
        if op == "ui_zero":
            macro = old.make_ui_certificate(new.freeze(instruction["body"]), 0)
            offset = len(instructions)
            for step in macro["instructions"]:
                copied = deepcopy(step)
                if "line" in copied:
                    copied["line"] += offset
                instructions.append(copied)
            line_map.append(len(instructions) - 1)
        else:
            copied = deepcopy(instruction)
            if op == "gen_zero":
                copied.update(op="gen", name=0)
                copied["line"] = line_map[copied["line"]]
            elif op in new.RENAMINGS:
                copied["line"] = line_map[copied["line"]]
            elif op == "mp":
                copied["implication"] = line_map[copied["implication"]]
                copied["antecedent"] = line_map[copied["antecedent"]]
            instructions.append(copied)
            line_map.append(len(instructions) - 1)
    result = {"instructions": instructions}
    if original:
        result["conclusion"] = original[-1]
    checked = old.check_certificate(result, theory)
    if any(original[i] != checked[j] for i, j in enumerate(line_map)):
        raise AssertionError("reverse exact line correspondence failed")
    return result


if __name__ == "__main__":
    import json

    original = old.make_ui_certificate(old.source19_body(), 0)
    converted, audit = translate(original)
    print(json.dumps({"source": original, "target": converted, "audit": audit}, indent=2))
