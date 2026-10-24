#!/usr/bin/env python3
"""Compile the direct C222 quartic using a shared binomial radix.

This retains the source calculus, CRT certificate and positive-power graph
of the authenticated upstream construction. The two transformations are:
  1. all binomial digit graphs use one common radix;
  2. optional: every signed congruence uses one common natural offset.

Every output coordinate ranges over the nonnegative integers.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
UPSTREAM = HERE / "upstream" / "direct"
sys.path.insert(0, str(UPSTREAM))
import build_equation as old

OriginalBuilder = old.Builder


class SharedBuilder(OriginalBuilder):
    shared_offset_enabled = False

    def __init__(self, positive_powers=False):
        super().__init__(positive_powers=positive_powers)
        self.deferred_binomials = []
        self.congruence_log = []
        self.shared_offset = None
        self.shared_radix_log = None

    def congruent(self, left, right, modulus, label, guard=None):
        if not self.shared_offset_enabled:
            return super().congruent(left, right, modulus, label, guard)
        if guard is not None:
            raise ValueError("only unconditional congruences are supported")
        if self.shared_offset is None:
            self.shared_offset = self.new("congruence.shared_offset")
        quotient = self.fresh(label + ".q")
        self.eq(self.add(left, self.mul(modulus, quotient)),
                self.add(right, self.mul(modulus, self.shared_offset)), label)
        self.congruence_log.append({"left": left, "right": right,
                                   "modulus": modulus, "label": label,
                                   "quotient": quotient,
                                   "common_offset": self.shared_offset})

    def binomial(self, n, k):
        key = (n, k)
        if key in self.binomials:
            return self.binomials[key]
        tag = f"choose{len(self.binomials)}"
        out = self.new(tag + ".output")
        self.binomials[key] = out
        self.deferred_binomials.append((n, k, out, tag))
        return out

    def finalize_binomials(self):
        # The upper arguments are positive at these actual call sites.
        # Their sum dominates each one. Only existence of a dominating
        # radix matters; no numerical evaluation of its enormous value is
        # performed by this compiler.
        exponent = self.sum(n for n, _, _, _ in self.deferred_binomials)
        common_radix = self.add(self.power(old.TWO, exponent), old.ONE)
        self.shared_radix_log = {
            "upper_arguments": [n for n, _, _, _ in self.deferred_binomials],
            "exponent": exponent, "radix": common_radix,
            "rule": "radix = 2^(sum(upper_arguments)) + 1",
        }
        for n, k, out, tag in self.deferred_binomials:
            numerator = self.power(self.add(common_radix, old.ONE), n)
            denominator = self.power(common_radix, k)
            h, r, rs, os = [self.new(tag + "." + s)
                           for s in ("high", "remainder", "rslack", "oslack")]
            quotient = self.add(self.mul(common_radix, h), out)
            self.eq(numerator,
                    self.add(self.mul(denominator, quotient), r),
                    tag + ".digit_division")
            self.eq(denominator, self.sum([r, rs, old.ONE]),
                    tag + ".remainder_bound")
            self.eq(common_radix, self.sum([out, os, old.ONE]),
                    tag + ".digit_bound")
            self.macro_log.append({"macro": "binomial", "output": out,
                                   "n": n, "k": k, "radix": common_radix})


class FrameBuilder(SharedBuilder):
    """Defer power graphs and emit one uniform Pell certificate frame."""

    def __init__(self, positive_powers=False):
        if not positive_powers:
            raise ValueError("the shared frame requires positive powers")
        super().__init__(positive_powers=True)
        self.power_calls = []
        self.shared_frame_log = None

    def power(self, n, k):
        key = (n, k)
        if key in self.powers:
            return self.powers[key]
        tag = f"pow{len(self.powers)}"
        out = self.new(tag + ".output")
        self.powers[key] = out
        self.power_calls.append((n, k, out, tag))
        return out

    def finalize_powers(self):
        # Including the proposed outputs in W makes every strict output
        # bound follow from the single last Pell norm. There are no local
        # output-bound slack witnesses in this frame.
        W = self.sum([old.ONE] + [atom for n, k, m, _ in self.power_calls
                                 for atom in (n, k, m)])
        a0 = self.new("frame.A_minus_two")
        A = self.add(a0, old.TWO)
        Z = self.new("frame.Z")
        U = self.new("frame.U")
        groups = {}
        for _, k, _, _ in self.power_calls:
            if k in groups:
                continue
            tag = f"index{len(groups)}"
            X = self.new(tag + ".X")
            yk = self.new(tag + ".Y_minus_index")
            Y = self.add(k, yk)
            S = self.new(tag + ".S")
            R = self.new(tag + ".R")
            groups[k] = {"tag": tag, "k": k, "X": X, "Y": Y,
                         "S": S, "R": R, "Y_slack": yk}

        P = self.product(g["Y"] for g in groups.values())
        d0 = self.new("frame.V_quotient_minus_one")
        V = self.mul(self.square(P), self.add(d0, old.ONE))
        bq0 = self.new("frame.B_quotient_minus_one")
        B = self.add(old.ONE,
                     self.product([old.FOUR, P, self.add(bq0, old.ONE)]))
        self.norm(A, U, V, "frame.auxiliary_norm")
        self.congruent(B, A, U, "frame.B_mod_U")
        self.norm(self.add(W, old.ONE), A, self.mul(W, Z),
                  "frame.last_norm")

        for k, g in groups.items():
            tag, X, Y, S, R = [g[s] for s in ("tag", "X", "Y", "S", "R")]
            self.norm(A, X, Y, tag + ".norm1")
            self.norm(B, S, R, tag + ".norm3")
            self.congruent(S, X, U, tag + ".S_mod_U")
            self.congruent(R, k, self.mul(old.FOUR, Y), tag + ".R_mod_4Y")

        for n, k, m, tag in self.power_calls:
            g = groups[k]
            X, Y = g["X"], g["Y"]
            T = self.new(tag + ".T")
            self.eq(self.product([old.TWO, A, n]),
                    self.sum([T, self.square(n), old.ONE]),
                    tag + ".T_definition")
            self.congruent(self.add(X, self.mul(Y, n)),
                           self.add(self.mul(Y, A), m), T,
                           tag + ".power_congruence")
            self.macro_log.append({"macro": "shared_power", "output": m,
                                   "base": n, "exponent": k,
                                   "group": g["tag"], "T": T})
        self.shared_frame_log = {
            "W": W, "A": A, "Z": Z, "U": U, "V": V, "B": B,
            "P": P, "A_slack": a0, "V_slack": d0, "B_slack": bq0,
            "index_groups": list(groups.values()),
            "W_rule": "1 + sum(base + exponent + output for every distinct power call)",
            "V_rule": "P^2 * (V_slack + 1)",
            "B_rule": "1 + 4 * P * (B_slack + 1)",
        }


def build(shared_offset=False, keep_linear_wires=False, shared_frame=False):
    source_path = UPSTREAM / "wire_eliminated_source.json"
    source_bytes = source_path.read_bytes()
    active_builder = FrameBuilder if shared_frame else SharedBuilder
    active_builder.shared_offset_enabled = shared_offset
    old.Builder = active_builder
    try:
        builder = old.construct(json.loads(source_bytes), "mixed13",
                                positive_powers=True, literal_calculus=True)
    finally:
        old.Builder = OriginalBuilder
    builder.finalize_binomials()
    if shared_frame:
        builder.finalize_powers()
    variant = "common_radix_and_offset" if shared_offset else "common_radix"
    if shared_frame:
        variant += "_shared_frame"
    equation, polynomial, metrics = builder.export(
        sha256(source_bytes).hexdigest(), variant,
        inline_affine=not keep_linear_wires)
    equation["construction"] = {
        "upstream_archive": "ConZFC_Shared_Certificates_2026-10-24.zip",
        "shared_radix": True,
        "shared_congruence_offset": shared_offset,
        "shared_power_frame": shared_frame,
    }
    audit = {
        "raw_variables": builder.variables,
        "raw_rows": builder.rows,
        "macro_log": builder.macro_log,
        "common_radix": builder.shared_radix_log,
        "congruences": builder.congruence_log,
        "raw_gate_map": {str(k): v for k, v in builder.gates.items()},
        "shared_frame": getattr(builder, "shared_frame_log", None),
    }
    return equation, polynomial, metrics, audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--shared-offset", action="store_true")
    parser.add_argument("--keep-linear-wires", action="store_true")
    parser.add_argument("--shared-frame", action="store_true")
    args = parser.parse_args()
    equation, polynomial, metrics, audit = build(
        args.shared_offset, args.keep_linear_wires, args.shared_frame)
    args.output.mkdir(parents=True, exist_ok=True)
    hashes = {name: old.write_json(args.output / name, obj)
              for name, obj in (("equation.json", equation),
                                ("expanded_polynomial.json", polynomial),
                                ("construction_trace.json", audit))}
    receipt = {
        "status": "PASS", "metrics": metrics, "sha256": hashes,
        "builder_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "upstream_builder_sha256": sha256((UPSTREAM / "build_equation.py").read_bytes()).hexdigest(),
        "scope": "finite materialization and exact expansion; unbounded proof is separate",
    }
    (args.output / "BUILD.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
