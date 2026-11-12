"""Untrusted format converter: a JSON certificate stack to consumption order.

Usage: python3 to_jsonl.py < three_field_certificate.json > certificate.jsonl
The public goal is copied literally to the first line; no formula is changed.
"""
import json
import sys

for value in reversed(json.load(sys.stdin)):
    print(json.dumps(value, separators=(',', ':')))
