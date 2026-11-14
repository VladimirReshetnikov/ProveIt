"""Finite-history bit cylinders for deterministic binary Turing machines.

The recurrence is the Entry Context packet's discovery abstraction:
start with every state and unrestricted tape; take exact one-step images
and re-inject the initial state with unrestricted tape at every iteration.
Subsumption changes only the representation of each union of cylinders.
"""
from pathlib import Path

def read_table(path):
    table = {}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        state, bit, write, direction, target = line.split()
        key = int(state), int(bit)
        if key in table or direction not in ('L', 'R'):
            raise ValueError('Duplicate or malformed transition')
        if int(bit) not in (0, 1) or int(write) not in (0, 1):
            raise ValueError('Nonbinary transition')
        table[key] = int(write), (1 if direction == 'R' else -1), int(target)
    states = {q for q, bit in table}
    if any((q, bit) not in table for q in states for bit in (0, 1)):
        raise ValueError('Incomplete working-state row')
    return table

def remove_subsumed(contexts):
    result = []
    for context in sorted(set(contexts), key=lambda c: (len(c), c)):
        cells = set(context)
        if not any(set(other) <= cells for other in result):
            result.append(context)
    return result

def history_contexts(table, depth, initial=0):
    states = {state for state, bit in table}
    if initial not in states or depth < 0:
        raise ValueError('Invalid initial state or history depth')
    contexts = {state: [()] for state in states}
    for _ in range(depth):
        successors = {state: [] for state in states}
        successors[initial] = [()]
        for (state, bit), (write, direction, target) in table.items():
            if target not in states:
                continue
            for context in contexts[state]:
                cells = dict(context)
                if 0 in cells and cells[0] != bit:
                    continue
                cells[0] = write
                successors[target].append(tuple(sorted(
                    (pos-direction, value) for pos, value in cells.items())))
        contexts = {state: remove_subsumed(items)
                    for state, items in successors.items()}
    return contexts
