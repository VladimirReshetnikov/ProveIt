"""Opt-in snapshot/commit bridge to ProveIt's mutable _Darts object.

Does not change the pipeline, defaults, budget counters, or verdicts. A caller
must explicitly allocate a local search budget and handle SearchExhausted.
The full production regression suite has NOT been run with this bridge.
"""
from __future__ import annotations
from dataclasses import dataclass
from dart_kernel import Darts, R3System
from verify_certificate import serialize, verify

@dataclass(frozen=True)
class Snapshot:
    diagram: Darts
    input_darts: tuple[int,...]
    alive: tuple[bool,...]

def snapshot(state):
    alive=tuple(state.alive)
    mapping=tuple(4*c+j for c,living in enumerate(alive) if living for j in range(4))
    local={d:i for i,d in enumerate(mapping)}
    try: result=Darts(tuple(local[state.alpha[d]] for d in mapping))
    except KeyError as exc: raise ValueError("live dart points to deleted crossing") from exc
    result.validate()
    return Snapshot(result,mapping,alive)

def commit_verified(state,original,witness,path,*,check=None):
    """Validate in isolation, check for a stale input, then commit atomically.

    Returns original-label darts of the terminal RI/II face. Does not perform
    the crossing deletion. Restores both pairing and path on any exception.
    """
    if snapshot(state)!=original: raise ValueError("stale production snapshot")
    if check: check()
    # Reconstruct both state and cyclic face identities from verified keys.
    # Action.payload and the caller-supplied final_state are not trusted.
    verify(serialize(original.diagram,witness,witness.length))
    system=R3System(); expected=original.diagram; verified_faces=[]
    for layer in witness.layers:
        for action in layer:
            if check: check()
            face=system._checked_face(expected,action)
            verified_faces.append(face)
            expected=system.apply(expected,action)
    if expected!=witness.final_state:
        raise ValueError("witness final state does not match replay")
    old=[(d,state.alpha[d]) for d in original.input_darts]; old_length=len(path)
    try:
        for i,d in enumerate(original.input_darts):
            if check: check()
            state.alpha[d]=original.input_darts[expected.alpha[i]]
        for face in verified_faces:
            if check: check()
            path.append(tuple(original.input_darts[d] for d in face))
    except BaseException:
        for d,p in old: state.alpha[d]=p
        del path[old_length:]
        raise
    return tuple(original.input_darts[d] for d in witness.terminal[1])
