"""A deliberately simple finite binary coding of lists and natural numbers.

This is a reference fair enumeration, not a state-minimized implementation.
Integers: 0 1^n 0. Lists: 1 1^length 0 followed by the encoded elements.
All finite binary strings are visited in length-lexicographic order.
"""
from __future__ import annotations
from typing import Any

def encode(value: Any) -> str:
    out: list[str] = []; todo = [value]
    while todo:
        x = todo.pop()
        if type(x) is int and x >= 0:
            out.append('0' + '1' * x + '0')
        elif type(x) is list:
            out.append('1' + '1' * len(x) + '0'); todo.extend(reversed(x))
        else: raise ValueError('Only lists and nonnegative non-Boolean integers are encodable.')
    return ''.join(out)

def decode(bits: str) -> Any:
    if type(bits) is not str or any(b not in '01' for b in bits): raise ValueError('Not a bit string.')
    pos = 0; stack: list[tuple[int, list]] = []
    while True:
        if pos >= len(bits): raise ValueError('Incomplete term.')
        tag = bits[pos]; pos += 1; amount = 0
        while pos < len(bits) and bits[pos] == '1': amount += 1; pos += 1
        if pos >= len(bits): raise ValueError('Unterminated unary count.')
        pos += 1
        if tag == '1' and amount:
            stack.append((amount, [])); continue
        value = amount if tag == '0' else []
        while stack:
            wanted, children = stack.pop(); children.append(value)
            if len(children) < wanted:
                stack.append((wanted, children)); break
            value = children
        else:
            if pos != len(bits): raise ValueError('Trailing data.')
            return value

def index(value: Any) -> int: return int('1' + encode(value), 2) - 1

def decode_index(n: int) -> Any:
    if type(n) is not int or n < 0: raise ValueError('Invalid candidate index.')
    return decode(bin(n + 1)[3:])
