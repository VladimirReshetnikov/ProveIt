#!/usr/bin/env python3
"""The only two free-name pass controls: upward and downward unit shift.

The source28 binary codec and exact transition implementation are retained.
Reachable inventories are 11 states per mode, not Turing-machine states.
"""
from __future__ import annotations

import stream_four as source

MODES = {"u": "s", "d": "S"}
encode = source.encode
decode = source.decode


def transition(mode, state, bit):
    if mode not in MODES:
        raise ValueError("only u and d shift modes are available")
    return source.transition(MODES[mode], state, bit)


def transduce(mode, bits):
    if mode not in MODES:
        raise ValueError("only u and d shift modes are available")
    return source.transduce(MODES[mode], bits)


def table(mode):
    if mode not in MODES:
        raise ValueError("only u and d shift modes are available")
    result = source.table(MODES[mode])
    result["mode"] = mode
    return result
