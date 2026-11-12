"""Untrusted conversion of canonical old computation packets.

It preserves the number and order of instructions, hence all allocated labels.
Malformed legacy counter wrappers are outside this canonical translator.
No checker imports this module.
"""
from copy import deepcopy


def convert(packet):
    translated = deepcopy(packet)
    for instruction in translated[:-1]:
        major, source, old_target, motive = instruction
        if not major and not motive:
            counter, seed, body = source
            if counter:
                if not isinstance(counter, list) or len(counter) != 1:
                    raise ValueError('Noncanonical legacy successor wrapper')
                predecessor, = counter
                instruction[1] = [predecessor, seed, body]
                instruction[2] = 1
            else:
                instruction[1] = [0, seed, body]
                instruction[2] = 0
    return translated
