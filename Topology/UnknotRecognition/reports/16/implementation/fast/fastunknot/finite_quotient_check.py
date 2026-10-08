"""Independent replay of finite_quotient.py permutation certificates.

No CSP table, union-find arc map, or orientation routine is imported from the
search code.  Diagram.from_pd is used only to validate and normalize the input.
"""
from __future__ import annotations

import hashlib
import json


def verify_certificate(pd, certificate):
    """Return {valid, reason}; malformed or invalid certificates return False."""
    from fastunknot.diagram import Diagram

    def fail(message):
        return {"valid": False, "reason": message}

    try:
        diagram = Diagram.from_pd(pd)
        rows = diagram.pd
        n = len(rows)
        if not isinstance(certificate, dict):
            return fail("certificate is not an object")
        if certificate.get("schema") != "fastunknot-a5-wirtinger-v1":
            return fail("unsupported schema")
        expected = hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest()
        if certificate.get("pd_sha256") != expected:
            return fail("certificate belongs to a different normalized PD diagram")
        images = certificate.get("edge_images")
        if not isinstance(images, list) or len(images) != 2 * n or n == 0:
            return fail("wrong edge-image count or crossing-free diagram")
        for p in images:
            if not isinstance(p, (list, tuple)) or len(p) != 5:
                return fail("an image is not a permutation of five points")
            if any(type(v) is not int for v in p) or sorted(p) != list(range(5)):
                return fail("an image is not a permutation of five points")
            if sum(p[i] > p[j] for i in range(5) for j in range(i + 1, 5)) % 2:
                return fail("an image is odd")

        # Orient the knot independently by following paired edges and opposite
        # crossing ports, starting by entering port zero of crossing zero.
        endpoints = {}
        for k, row in enumerate(rows):
            for port, label in enumerate(row):
                endpoints.setdefault(label, []).append((k, port))
        incoming = {}
        cursor = (0, 0)
        for _ in range(2 * n):
            k, port = cursor
            if (k, port % 2) in incoming:
                return fail("orientation revisited a strand early")
            incoming[k, port % 2] = port
            outgoing = (k, (port + 2) % 4)
            edge = rows[k][outgoing[1]]
            a, b = endpoints[edge]
            cursor = b if a == outgoing else a
        if cursor != (0, 0) or len(incoming) != 2 * n:
            return fail("orientation traversal did not close correctly")

        def multiply(p, q):
            return [p[q[x]] for x in range(5)]

        def inverse(p):
            return [p.index(x) for x in range(5)]

        for k, row in enumerate(rows):
            u_port, o_port = incoming[k, 0], incoming[k, 1]
            over = images[row[1]]
            if over != images[row[3]]:
                return fail("over-strand images disagree at crossing " + str(k))
            under_in = images[row[u_port]]
            under_out = images[row[(u_port + 2) % 4]]
            conjugator = over if (o_port - u_port) % 4 == 3 else inverse(over)
            if multiply(multiply(conjugator, under_in), inverse(conjugator)) != under_out:
                return fail("Wirtinger relation fails at crossing " + str(k))

        pair = certificate.get("noncommuting_edges")
        if not isinstance(pair, list) or len(pair) != 2:
            return fail("missing noncommuting pair")
        if any(type(i) is not int or not 0 <= i < 2 * n for i in pair):
            return fail("noncommuting edge index out of range")
        a, b = (images[i] for i in pair)
        if multiply(a, b) == multiply(b, a):
            return fail("the claimed noncommuting pair commutes")
        return {"valid": True, "reason": "all Wirtinger relations hold and the image is nonabelian"}
    except (ValueError, TypeError, KeyError, IndexError, AttributeError) as exc:
        return fail("malformed data: " + str(exc))


def main():
    import argparse
    from fastunknot import Diagram
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("diagram")
    parser.add_argument("certificate")
    args = parser.parse_args()
    with open(args.diagram, encoding="utf-8") as handle:
        diagram = Diagram.from_json(json.load(handle))
    with open(args.certificate, encoding="utf-8") as handle:
        payload = json.load(handle)
    if isinstance(payload, dict) and "certificate" in payload:
        payload = payload["certificate"]
    result = verify_certificate(diagram.pd, payload)
    print(json.dumps(result, indent=2))
    return 0 if result["valid"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
