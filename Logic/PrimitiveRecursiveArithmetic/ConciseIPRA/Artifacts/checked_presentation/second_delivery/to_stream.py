"""Convert a stack certificate to JSON Lines, in proof-read order.

The standalone stream checkers do not import this utility. The input is
one JSON array of finite exact-integer/list trees. Its last element is the
goal. Any unused prefix becomes an unused suffix of the output stream.
"""
import json
import sys


def integer_list_tree(value):
    return type(value) is int or (
        type(value) is list and all(integer_list_tree(x) for x in value)
    )


def main():
    data = json.load(sys.stdin)
    if type(data) is not list or not integer_list_tree(data):
        raise ValueError("Expected an array of exact-integer/list syntax trees")
    for item in reversed(data):
        sys.stdout.write(json.dumps(item, separators=(",", ":"),
                                   ensure_ascii=True, allow_nan=False) + "\n")


if __name__ == "__main__":
    main()
