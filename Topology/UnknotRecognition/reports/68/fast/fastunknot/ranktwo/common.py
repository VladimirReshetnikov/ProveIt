from __future__ import annotations
from collections.abc import Iterable
from hashlib import sha256


def validate_word(strands: int, word: Iterable[int]) -> tuple[int, ...]:
    if type(strands) is not int or strands < 1:
        raise ValueError('strands must be a positive integer')
    try:
        result = tuple(word)
    except TypeError as exc:
        raise ValueError('word must be an iterable of signed integers') from exc
    if any(type(g) is not int or not 1 <= abs(g) < strands for g in result):
        raise ValueError('each Artin generator must satisfy 1 <= abs(g) < strands')
    return result


def input_digest(strands: int, word: tuple[int, ...]) -> str:
    # Hex encoding avoids Python's decimal integer-to-string length limit.
    digest = sha256()
    digest.update(f'{strands:x}|'.encode('ascii'))
    for g in word:
        digest.update(f'{g:x},'.encode('ascii'))
    return digest.hexdigest()


def component_count(strands: int, word: Iterable[int]) -> int:
    word = validate_word(strands, word)
    p = list(range(strands))
    for g in word:
        j = abs(g) - 1
        p[j], p[j + 1] = p[j + 1], p[j]
    seen = [False] * strands
    answer = 0
    for i in range(strands):
        if not seen[i]:
            answer += 1
            while not seen[i]:
                seen[i] = True
                i = p[i]
    return answer
