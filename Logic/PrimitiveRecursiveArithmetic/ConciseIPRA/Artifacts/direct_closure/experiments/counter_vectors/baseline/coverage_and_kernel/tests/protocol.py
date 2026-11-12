"""Untrusted conversion of inherited certificates to the array-truth protocol.

The inherited producer is kept byte-for-byte with attribution. The checker
imports neither this module nor that producer. Canonical major proofs keep
their global eigenparameter numbering: the neutral [] proof consumes no
packet and allocates no fresh name.
"""
import copy


def translate(packet):
    result = copy.deepcopy(packet)
    for command in result[:-1]:
        if isinstance(command, list) and len(command) == 4:
            major, source, target, template = command
            if not major:
                command[0] = []
                if not target:
                    command[2] = major
    return result
