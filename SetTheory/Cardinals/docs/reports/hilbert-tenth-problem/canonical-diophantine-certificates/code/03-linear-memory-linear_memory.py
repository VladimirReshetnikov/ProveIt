#!/usr/bin/env python3
"""Linear-size canonical quartic memory checker over N (large-base backend).

This uses exact bounded-digit product equality, NOT a probabilistic hash.
It imports the shared sparse-polynomial representation from canonical_memory.
The mathematical proof is in article.tex; these Python functions are not
machine-checked proofs. Large witness integers are the deliberate tradeoff.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from canonical_memory import Event, Poly, System


def compile_linear_log(events: list[Event]) -> System:
    """Produce a quadratic residual system and its canonical candidate witness.

    For L events the system has 3L free parameters, 24L auxiliary variables,
    and 22L+1 residuals. Invalid reads are retained and fail the read checks.
    """
    length = len(events)
    s = System()
    s.padded_length = length  # This backend uses no padding and no comparators.
    parameters = []
    for t, event in enumerate(events):
        parameters.append(tuple(s.variable(f"event{t}.{name}", value, "parameter")
                                for name, value in zip(("a", "w", "v"),
                                                       (event.address, event.write, event.value))))
    if not events:
        s.eq("memory.empty", 0)
        return s

    records = []
    for t, (a, w, v) in enumerate(parameters):
        alpha = s.variable(f"event{t}.shifted_address", events[t].address + 1)
        key = s.variable(f"event{t}.key", (length+1)*(events[t].address+1)+t)
        s.eq(f"event{t}.address", alpha-a-1)
        s.eq(f"event{t}.key", key-(length+1)*alpha-t)
        s.eq(f"event{t}.write_bit", w*(w-1))
        records.append((alpha, key, w, v))

    prefix = Poly.coerce(0)
    for i, record in enumerate(records):
        new = s.variable(f"radix.prefix{i+1}", s.value(prefix)+sum(s.value(x) for x in record))
        s.eq(f"radix.prefix{i+1}", new-prefix-sum(record, Poly.coerce(0)))
        prefix = new
    radix = s.variable("radix.D", s.value(prefix)+2)
    s.eq("radix.definition", radix-prefix-2)
    dv = s.value(radix)

    # This sort generates the candidate witness. Its correctness is certified by
    # product equality plus adjacent key gaps, NOT by assuming Python's sort.
    actual = sorted(records, key=lambda record: s.value(record[1]))
    outputs = []
    for i, record in enumerate(actual):
        out = tuple(s.variable(f"sorted{i}.{name}", s.value(value))
                    for name, value in zip(("alpha", "key", "w", "v"), record))
        outputs.append(out)
        for j, value in enumerate(out):
            slack = s.variable(f"sorted{i}.bound{j}", dv-s.value(value)-1)
            s.eq(f"sorted{i}.bound{j}", value+slack+1-radix)
    s.sorted_records = outputs

    def pack(record: tuple[Poly, ...], name: str) -> Poly:
        alpha, key, w, v = record
        current = v
        for stage, digit in enumerate((w, key, alpha)):
            new = s.variable(f"{name}.stage{stage}", s.value(current)*dv+s.value(digit))
            s.eq(f"{name}.stage{stage}", new-current*radix-digit)
            current = new
        return current

    left_codes = [pack(record, f"pack.input{i}") for i, record in enumerate(records)]
    right_codes = [pack(record, f"pack.output{i}") for i, record in enumerate(outputs)]
    d2 = s.variable("radix.D2", dv*dv)
    d4 = s.variable("radix.C", dv**4)
    s.eq("radix.D2", d2-radix*radix)
    s.eq("radix.C", d4-d2*d2)
    power = Poly.coerce(1)
    for i in range(1, length+1):
        new = s.variable(f"power{i}", s.value(power)*s.value(d4))
        s.eq(f"power{i}", new-power*d4)
        power = new
    beta = s.variable("radix.beta", s.value(power)+1)
    s.eq("radix.beta", beta-power-1)

    products = []
    for side, codes in (("input", left_codes), ("output", right_codes)):
        previous = Poly.coerce(1)
        for i, code in enumerate(codes):
            new = s.variable(f"product.{side}{i}", s.value(previous)*(s.value(beta)+s.value(code)))
            s.eq(f"product.{side}{i}", new-previous*(beta+code))
            previous = new
        products.append(previous)
    s.eq("product.equality", products[0]-products[1])

    for i in range(1, length):
        gap = s.variable(f"order{i}.gap", s.value(outputs[i][1])-s.value(outputs[i-1][1]))
        s.eq(f"order{i}.gap", outputs[i][1]-outputs[i-1][1]-gap)

    s.eq("memory.first", (1-outputs[0][2])*outputs[0][3])
    for i in range(1, length):
        prev, current = outputs[i-1], outputs[i]
        delta = current[0]-prev[0]
        gap = s.value(delta)
        assert gap >= 0
        same = s.variable(f"memory{i}.same", int(gap == 0))
        h = s.variable(f"memory{i}.gap_minus_one", max(0, gap-1))
        u = s.variable(f"memory{i}.previous_value", s.value(prev[3]) if gap == 0 else 0)
        for suffix, residual in [
            ("boolean", same*(same-1)),
            ("signed_gap", delta+(2*same-1)*h+same-1),
            ("previous", u-same*prev[3]),
            ("read", (1-current[2])*(current[3]-u)),
        ]:
            s.eq(f"memory{i}.{suffix}", residual)
    return s


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON list of [address,write,value] triples")
    parser.add_argument("output", type=Path, help="directory for emitted certificate")
    parser.add_argument("--expanded", action="store_true", help="also expand the quartic")
    args = parser.parse_args()
    try:
        events = [Event(*row) for row in json.loads(args.input.read_text())]
        s = compile_linear_log(events)
        s.export(args.output, args.expanded)
        print(json.dumps(s.summary(), indent=2))
    except (ValueError, TypeError, OSError) as exc:
        parser.exit(2, f"Error: {exc}\n")


if __name__ == "__main__":
    main()
