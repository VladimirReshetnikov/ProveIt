#!/usr/bin/env python3
"""A 2-adic cons/uncons experiment on concrete RPN formulas, not a TM compiler.

Natural-register boundary: Nil=0, Cons(a,b)=2**a*(2*b+1). Its bit length is
exactly a+1+bit_length(b). Every positive code has a unique head and a strictly
smaller tail. An unframed LSB-first numeral is NOT a self-delimiting bitstream.
The fair binary comparison therefore retains kernel_metrics' mode+gamma-length
frame. Both experiments exclude the decoder program and the theory-list frame.
"""
from __future__ import annotations
from itertools import permutations
import json
from pathlib import Path

import kernel_metrics as k


TAGS = {'mem': 0, 'nand': 1, 'all': 2, 'eq': 3}
ARITY = {'mem': 2, 'nand': 0, 'all': 1, 'eq': 2}


def cons(head: int, tail: int) -> int:
    k.nat(head); k.nat(tail)
    return ((tail << 1) | 1) << head


def uncons(code: int) -> tuple[int, int]:
    k.nat(code)
    if not code: raise ValueError('Nil has no head or tail')
    head = (code & -code).bit_length() - 1
    return head, code >> (head + 1)


def encode_list(values: list[int]) -> int:
    if not isinstance(values, list): raise ValueError('natural field list required')
    code = 0
    for value in reversed(values): code = cons(value, code)
    return code


def decode_list(code: int) -> list[int]:
    k.nat(code)
    values = []
    while code:
        head, code = uncons(code)
        values.append(head)
    return values


def formula_fields(p: k.F) -> list[int]:
    """Token tag followed by its declared variable/binder payloads."""
    return [field for token in k.rpn(p) for field in [TAGS[token[0]], *token[1:]]]


def encode_formula(p: k.F) -> int:
    return encode_list(formula_fields(p))


def decode_formula(code: int, *, equality: bool = False) -> k.F:
    if type(equality) is not bool: raise ValueError('boolean equality mode required')
    fields = decode_list(code)
    inverse = {v: op for op, v in TAGS.items()}
    tokens = []
    pos = 0
    while pos < len(fields):
        tag = fields[pos]; pos += 1
        if tag not in inverse or (tag == TAGS['eq'] and not equality):
            raise ValueError('unknown or forbidden constructor tag')
        op = inverse[tag]
        arity = ARITY[op]
        if pos + arity > len(fields): raise ValueError('truncated constructor payload')
        tokens.append([op, *fields[pos:pos+arity]])
        pos += arity
    return k.from_rpn(tokens)


def serialize_frame(p: k.F) -> str:
    equality = any(t[0] == 'eq' for t in k.rpn(p))
    code = encode_formula(p)
    payload = bin(code)[2:][::-1]  # LSB first: successive unary head fields.
    return str(int(equality)) + k.gamma(len(payload) + 1) + payload


def deserialize_frame(bits: object) -> k.F:
    if not isinstance(bits, str) or not bits or set(bits) - {'0', '1'}:
        raise ValueError('nonempty binary frame required')
    equality = bits[0] == '1'
    pos = 1
    start = pos
    while pos < len(bits) and bits[pos] == '0': pos += 1
    if pos == len(bits): raise ValueError('truncated gamma prefix')
    zeros = pos - start
    if pos + zeros >= len(bits): raise ValueError('truncated gamma body')
    size = int(bits[pos:pos+zeros+1], 2) - 1
    pos += zeros + 1
    if pos + size != len(bits): raise ValueError('truncated payload or trailing bits')
    payload = bits[pos:]
    if not payload or payload[-1] != '1': raise ValueError('noncanonical positive natural numeral')
    code = int(payload[::-1], 2)
    result = decode_formula(code, equality=equality)
    if equality != any(token[0] == 'eq' for token in k.rpn(result)):
        raise ValueError('noncanonical equality mode')
    return result


def experiment() -> dict:
    formulas = k.templates(k.Mem(0, 1))
    rows = {}
    for name in ('CG_oneway', 'PSC_subset_subset'):
        p = k.to_nand(k.alpha_reuse(k.normalize(formulas[name])))
        tokens = k.rpn(p)
        fields = formula_fields(p)
        code = encode_list(fields)
        assert decode_formula(code) == p
        assert code.bit_length() == sum(x + 1 for x in fields)
        frame = serialize_frame(p)
        assert deserialize_frame(frame) == p
        variants = []
        for perm in permutations(range(3)):
            tags = dict(zip(('mem', 'nand', 'all'), perm))
            trial = [v for token in tokens for v in [tags[token[0]], *token[1:]]]
            variants.append({'tags': tags, 'natural_register_bits': sum(v + 1 for v in trial)})
        variants.sort(key=lambda item: item['natural_register_bits'])
        rows[name] = {
            'natural_fields': len(fields),
            'natural_register_input_bits': code.bit_length(),
            'framing_bits': len(frame) - code.bit_length(),
            'framed_binary_bits': len(frame),
            'reference_gamma_frame_bits': len(k.serialize(p)),
            'best_of_six_opcode_tag_permutations': variants[0],
            'lsb_first_payload': bin(code)[2:][::-1],
            'binary_frame': frame,
        }
    return {
        'scope': 'Concrete formula/list encoding experiment only, not a proof checker, formal codec proof, theory axiomatization, TM compiler, or state count.',
        'input': 'Same DN-normalized, alpha-reused NAND3 concrete Mem(0,1) instances as kernel_metrics.py; one instance does not replace the infinite schema.',
        'cons': 'Nil=0; Cons(a,b)=2^a*(2*b+1); Uncons(c)=(v2(c), c>>(v2(c)+1)) for c>0.',
        'mathematical_invariants': 'For c>0 the tail is strictly smaller than c; bit_length(Cons(a,b))=a+1+bit_length(b). Therefore list bit length is sum(a+1). Every natural codes one finite field list, but malformed formula field lists still fail the strict RPN parser.',
        'tags': TAGS,
        'natural_register_boundary': 'Unframed natural input assumes an existing natural-register representation and zero-test. Its bit height is not a self-delimiting binary tape format or a paid machine routine.',
        'binary_boundary': 'Same framing overhead as kernel_metrics: mode bit + gamma(payload_bit_length+1). Payload here is the LSB-first binary numeral of the 2-adic list. Complete frame length and canonical positive numeral are checked.',
        'enumeration_boundary': 'Every concrete supported formula has a finite positive natural code, so fair enumeration of naturals reaches its code. Sound checking still requires token arity, stack validity, logical rules, matrix freshness and all schema/certificate conditions. No such proof enumerator is implemented here.',
        'exclusions': 'Decoder/encoder code size, integer-zero/end-of-tape implementation, certificate validation, matrix generator, proof engine, theory-list container, initialization and TM backend.',
        'examples': rows,
        'totals': {
            'natural_register_input_bits': sum(r['natural_register_input_bits'] for r in rows.values()),
            'framed_binary_bits': sum(r['framed_binary_bits'] for r in rows.values()),
            'reference_gamma_frame_bits': sum(r['reference_gamma_frame_bits'] for r in rows.values()),
            'saved_framed_bits': sum(r['reference_gamma_frame_bits']-r['framed_binary_bits'] for r in rows.values()),
        },
    }


if __name__ == '__main__':
    result = experiment()
    path = Path(__file__).resolve().parent / 'results' / 'stream_encoding.json'
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result['totals'], indent=2))
    print(f'Wrote {path}')
