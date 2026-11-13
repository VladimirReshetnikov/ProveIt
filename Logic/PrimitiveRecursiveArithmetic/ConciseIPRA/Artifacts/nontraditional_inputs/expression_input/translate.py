"""Untrusted JSON-to-expression converter; no checker imports this file.

The output is a canonical integer/list literal, hence also valid JSON.
The reader is a strict subset of Python expression syntax, not Python code
supplied with permissions. The complete measured checkers enforce their gate.
"""
import json
import sys


def convert(value):
    if type(value) is not list:
        raise ValueError("The certificate root must be a list")
    pending = [value]
    while pending:
        item = pending.pop()
        if type(item) is list:
            pending.extend(item)
        elif type(item) is not int:
            raise ValueError("Only exact integers and lists are allowed")
    return json.dumps(value, separators=(",", ":"))


if __name__ == "__main__":
    print(convert(json.load(sys.stdin)))
