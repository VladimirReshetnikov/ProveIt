"""Untrusted codec on canonical proof trees with null unused payloads."""


def encode(proof, old=False):
    if not isinstance(proof, list) or not proof or not isinstance(proof[0], str):
        return proof
    tag = proof[0]
    if tag == 'u':
        return [proof[1], proof[2], encode(proof[3], old)]
    if tag == 'i':
        return [proof[1], proof[2], encode(proof[3], old)]
    if tag == 'e':
        return [[], encode(proof[1], old), [encode(proof[2], old), encode(proof[3], old)] if old else encode(proof[2], old)]
    raise ValueError('tagged proof')


def decode(packet, old=False):
    if not isinstance(packet, list) or len(packet) != 3:
        return packet
    code, arg, branch = packet
    if type(code) is int:
        return ['u', code, arg, decode(branch, old)]
    if code:
        return ['i', code, arg, decode(branch, old)]
    if old:
        equation, continuation = branch
        return ['e', decode(arg, old), decode(equation, old), decode(continuation, old)]
    return ['e', decode(arg, old), decode(branch, old)]
