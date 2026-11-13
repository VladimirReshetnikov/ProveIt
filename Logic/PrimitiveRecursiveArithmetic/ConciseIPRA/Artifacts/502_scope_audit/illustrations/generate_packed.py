#!/usr/bin/env python3
"""Build a fixed-data packed checker and verify its exact expanded payload.

Usage: python3 generate_packed.py EXPANDED.py PACKED.py
This is an untrusted build helper, not a dependency of the packed checker.
The measured checker includes its imports and its entire encoded program.
"""
import ast
import base64
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize
import zlib


def metric(source):
    normalized = ast.unparse(ast.parse(source)) + "\n"
    ignored = {
        tokenize.COMMENT, tokenize.INDENT, tokenize.DEDENT, tokenize.NEWLINE,
        tokenize.NL, tokenize.ENDMARKER, tokenize.ENCODING,
    }
    return {
        "significant_tokens": sum(t.type not in ignored for t in
                                  tokenize.generate_tokens(io.StringIO(normalized).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "normalized_bytes": len(normalized.encode("utf-8")),
    }


def build(expanded, destination):
    raw = expanded.read_bytes()
    payload = base64.b85encode(zlib.compress(raw, level=9)).decode("ascii")
    source = "import zlib, base64\nexec(zlib.decompress(base64.b85decode(" + repr(payload) + ")))\n"
    normalized = ast.unparse(ast.parse(source)) + "\n"
    parsed = ast.parse(normalized)
    actual_payload = parsed.body[1].value.args[0].args[0].args[0].value
    recovered = zlib.decompress(base64.b85decode(actual_payload))
    if recovered != raw:
        raise RuntimeError("Packed literal does not recover the complete source exactly")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(normalized, encoding="utf-8")
    if destination.read_bytes() != normalized.encode("utf-8"):
        raise RuntimeError("Output bytes changed while writing")
    return {
        "python_version": sys.version.split()[0],
        "zlib_version": zlib.ZLIB_VERSION,
        "zlib_runtime_version": zlib.ZLIB_RUNTIME_VERSION,
        "expanded_source": str(expanded),
        "expanded_source_sha256": hashlib.sha256(raw).hexdigest(),
        "expanded_source_bytes": len(raw),
        "expanded_metrics": metric(raw.decode("utf-8")),
        "packed_source": str(destination),
        "packed_source_sha256": hashlib.sha256(normalized.encode("utf-8")).hexdigest(),
        "packed_metrics": metric(normalized),
        "compressed_bytes": len(base64.b85decode(actual_payload)),
        "encoded_ascii_characters": len(actual_payload),
        "payload_is_exact_complete_source": recovered == raw,
        "generation_is_deterministic_for_this_python_and_zlib_runtime": True,
        "caveat": "Different zlib versions may choose different compressed bytes; payload identity is verified independently of those choices.",
    }


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("Usage: generate_packed.py EXPANDED.py PACKED.py")
    print(json.dumps(build(Path(sys.argv[1]), Path(sys.argv[2])), indent=2))
