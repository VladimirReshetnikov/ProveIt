#!/usr/bin/env python3
"""Exact symbolic embedding for ultimately periodic blocks below omega^2.

A Word has finitely many blocks prefix + cycle^omega, followed by a finite
suffix. The algorithm operates at the omega-block level, not on truncations.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Tuple
from atoms import FinitePoset


@dataclass(frozen=True)
class Block:
    prefix: Tuple[int, ...]
    cycle: Tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.cycle:
            raise ValueError("An omega-block must have a nonempty cycle.")


@dataclass(frozen=True)
class Word:
    blocks: Tuple[Block, ...] = ()
    tail: Tuple[int, ...] = ()

    def __add__(self, other: Word) -> Word:
        if not isinstance(other, Word):
            return NotImplemented
        if not other.blocks:
            return Word(self.blocks, self.tail + other.tail)
        first = other.blocks[0]
        merged = Block(self.tail + first.prefix, first.cycle)
        return Word(self.blocks + (merged,) + other.blocks[1:], other.tail)

    @property
    def omega_ended(self) -> bool:
        return bool(self.blocks) and not self.tail


def period(*letters: int) -> Word:
    return Word((Block((), tuple(letters)),))


def embeds(source: Word, target: Word, alphabet: FinitePoset) -> bool:
    """Decide the actual transfinite subsequence relation for these words."""
    rel = alphabet.relation
    n = len(rel)
    for w in (source, target):
        for b in w.blocks:
            if any(x < 0 or x >= n for x in b.prefix + b.cycle):
                raise ValueError("Letter outside the alphabet.")
        if any(x < 0 or x >= n for x in w.tail):
            raise ValueError("Letter outside the alphabet.")
    block_index = 0
    offset = 0  # finite offset in prefix + periodic tail (or finite final suffix)

    def consume_letter(a: int) -> bool:
        nonlocal block_index, offset
        while block_index < len(target.blocks):
            b = target.blocks[block_index]
            while offset < len(b.prefix):
                t = b.prefix[offset]
                offset += 1
                if rel[a][t]:
                    return True
            phase = (offset - len(b.prefix)) % len(b.cycle)
            for delta in range(len(b.cycle)):
                if rel[a][b.cycle[(phase + delta) % len(b.cycle)]]:
                    offset += delta + 1
                    return True
            block_index += 1
            offset = 0
        while offset < len(target.tail):
            t = target.tail[offset]
            offset += 1
            if rel[a][t]:
                return True
        return False

    for b in source.blocks:
        if not all(consume_letter(a) for a in b.prefix):
            return False
        found = False
        while block_index < len(target.blocks):
            t = target.blocks[block_index]
            if all(any(rel[a][z] for z in t.cycle) for a in b.cycle):
                found = True
                block_index += 1
                offset = 0
                break
            block_index += 1
            offset = 0
        if not found:
            return False
    return all(consume_letter(a) for a in source.tail)


def separated(parts: Tuple[Word, ...], separator: Word) -> Word:
    if not parts:
        raise ValueError("At least one part is required.")
    result = parts[0]
    for part in parts[1:]:
        result = result + separator + part
    return result
