"""Untrusted certificate adapters; no proof checking or theorem search.

The native expressions and depth-first packet order are unchanged.
Only each consumed instruction's redundant elimination fields change.
"""
import copy
import json
import sys


def convert_instruction(instruction):
    if type(instruction) is not list or len(instruction) != 2:
        return None
    major, payload = instruction
    if type(major) is list:
        if len(major) == 1:
            return [major, 0, payload, major[0]]
        if len(major) == 2:
            return [major, major[0], major[1], payload]
    return [major, 0, 0, payload]


def convert_packet(packet):
    packet = copy.deepcopy(packet)
    if type(packet) is not list or not packet:
        return packet
    return [convert_instruction(x) for x in packet[:-1]] + packet[-1:]


def erase_instruction(instruction):
    """Partial inverse on canonical zero-source closures.

    This deliberately uses independent arity cases, not the candidate's
    tuple-membership dispatch. Falsy nonnumeric closure sources such as []
    are meaningful raw aliases in the new language, but translating their
    minor proofs may need equality transport, so this adapter declines them.
    Unused prefixes remain immaterial.
    """
    if type(instruction) is not list or len(instruction) != 4:
        return None
    major, source, target, motive = instruction
    if type(major) is list:
        if len(major) == 1:
            if bool(source) or motive != major[0]:
                return None
            if not isinstance(source, (int, float)) or source != 0:
                raise ValueError("Noncanonical closure source needs proof conversion")
            return [major, target]
        if len(major) == 2:
            if source != major[0] or target != major[1]:
                return None
            return [major, motive]
    return [major, motive]


def erase_packet(packet):
    packet = copy.deepcopy(packet)
    if type(packet) is not list or not packet:
        return packet
    return [erase_instruction(x) for x in packet[:-1]] + packet[-1:]


if __name__ == "__main__":
    operation = erase_packet if sys.argv[1:] == ["--erase"] else convert_packet
    json.dump(operation(json.load(sys.stdin)), sys.stdout)
    print()
