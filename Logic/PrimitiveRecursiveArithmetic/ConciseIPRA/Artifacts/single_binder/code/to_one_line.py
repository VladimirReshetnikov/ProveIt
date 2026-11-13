"""Serialize one finite JSON value on one physical line; no proof processing."""
import json
import sys

value = json.load(sys.stdin)
json.dump(value, sys.stdout, separators=(",", ":"), ensure_ascii=True, allow_nan=False)
sys.stdout.write("\n")
