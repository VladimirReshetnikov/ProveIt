"""Source-derived baseline, not a run of the complete upstream recognizer.

Functions below reproduce the endpoint helper from ProveIt commit
8388b53680366eed81f8bc23d8db8cfbf2cd956e, path
Topology/UnknotRecognition/fast/fastunknot/braid_reduction.py,
blob 974d42c8c722018fad7678b2000758155ffe5162 (MIT-0).
The omitted verifier is not needed for this stage-only timing baseline.
"""
from collections import deque

def _validate(strands, word):
    if type(strands) is not int or strands < 1:
        raise ValueError('strands must be a positive integer')
    word = tuple(word)
    if any(type(g) is not int or not 1 <= abs(g) < strands for g in word):
        raise ValueError('invalid Artin generator')
    return word

def _free_cyclic(word, check):
    stack = []
    for index, generator in enumerate(word):
        if index & 255 == 0:
            check()
        if stack and stack[-1] == -generator:
            stack.pop()
        else:
            stack.append(generator)
    ends = deque(stack)
    while len(ends) > 1 and ends[0] == -ends[-1]:
        ends.popleft()
        ends.pop()
        if len(ends) & 255 == 0:
            check()
    return tuple(ends)

def _delete_endpoint(strands, word, side, position):
    endpoint = strands - 1 if side == 'right' else 1
    if side not in ('left', 'right') or not 0 <= position < len(word):
        raise ValueError('invalid endpoint step')
    if abs(word[position]) != endpoint:
        raise ValueError('step points to the wrong generator')
    if sum(abs(g) == endpoint for g in word) != 1:
        raise ValueError('endpoint generator is not a singleton')
    remaining = word[position + 1:] + word[:position]
    if side == 'left':
        remaining = tuple(g - 1 if g > 0 else g + 1 for g in remaining)
    return remaining

def singleton_reduce(strands, word, check=lambda: None):
    word = _validate(strands, word)
    original_strands, original_length = strands, len(word)
    steps = []
    while True:
        check()
        word = _free_cyclic(word, check)
        if strands <= 3:
            break
        right = [i for i, g in enumerate(word) if abs(g) == strands - 1]
        left = [i for i, g in enumerate(word) if abs(g) == 1]
        if len(right) == 1:
            side, position = 'right', right[0]
        elif len(left) == 1:
            side, position = 'left', left[0]
        else:
            break
        steps.append({'strands': strands, 'length': len(word), 'side': side,
                      'position': position, 'generator': word[position]})
        word = _delete_endpoint(strands, word, side, position)
        strands -= 1
    certificate = {'kind': 'singleton-markov-descent-v1',
                   'input_strands': original_strands, 'input_length': original_length,
                   'steps': steps, 'final_strands': strands, 'final_word': list(word)}
    return strands, word, certificate
