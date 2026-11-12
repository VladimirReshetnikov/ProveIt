"""Untrusted conversion for the pinned well-sorted local certificate producer.

Only four-field command majors are changed. Numerical terms, goals, witnesses,
templates and the optional falsy introduction-mode field are left untouched.
This is not an equivalence assertion for arbitrary malformed JSON.
"""
import copy
import json
import sys


def zero_neutral(packet):
    result = copy.deepcopy(packet)
    if isinstance(result, list):
        for command in result[:-1]:
            if isinstance(command, list) and len(command) == 4 and command[0] == []:
                command[0] = 0
    return result


def audit_positive(packet):
    """Check where the frozen producer uses empty lists in a positive packet.

    In this producer an empty list is administrative, never a number or a
    public formula: either a neutral command major, or the falsy mode field
    of an introduction command whose major and source are also falsy.
    """
    if not isinstance(packet, list) or not packet:
        raise ValueError('Missing packet or goal')
    majors = modes = 0
    for index, command in enumerate(packet[:-1]):
        if not isinstance(command, list) or len(command) != 4:
            raise ValueError('Positive command is not a four-field array')
        def scan(value, path):
            nonlocal majors, modes
            if not isinstance(value, list):
                return
            if not value:
                if path == (0,):
                    majors += 1
                elif path == (2,) and not command[0] and not command[1]:
                    modes += 1
                else:
                    raise ValueError(f'Unexpected empty list in command {index} at {path}')
            else:
                for child_index, child in enumerate(value):
                    scan(child, path + (child_index,))
        for field, value in enumerate(command):
            scan(value, (field,))
    def no_empty(value):
        return not isinstance(value, list) or bool(value) and all(map(no_empty, value))
    if not no_empty(packet[-1]):
        raise ValueError('Empty list in positive public or closure goal')
    return {'neutral_majors': majors, 'untouched_falsy_modes': modes}


if __name__ == '__main__':
    print(json.dumps(zero_neutral(json.load(sys.stdin)), separators=(',', ':')))
