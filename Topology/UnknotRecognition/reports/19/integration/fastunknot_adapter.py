"""Opt-in raw-braid gateway adapter for the inspected fastunknot API.

This adapter does not modify a repository and does not guess its PD constructor.
On INCONCLUSIVE, send reduced_input to the existing pipeline after replay.
The real upstream integration smoke test is provided separately and was not run
in the artifact-building environment; local contract tests use a fake gateway.
"""
from __future__ import annotations
from collections.abc import Callable, Iterable
from ranktwo import compress, verify
from ranktwo.common import validate_word


def braid_gateway_with_ranktwo(strands: int, word: Iterable[int], *,
                               gateway: Callable | None = None,
                               check: Callable[[], None] | None = None,
                               max_passes: int | None = 1,
                               dictionary: str = 'avl') -> dict:
    """Retain upstream decisions; retry its gateway after verified shortening.

    A budget exception is intentionally propagated to the pipeline's existing
    resource handler. It must not become an UNKNOT or KNOTTED verdict.
    """
    word = validate_word(strands, word)
    if gateway is None:
        from fastunknot.braid import braid_certificate
        gateway = braid_certificate
    before = gateway(strands, word, check=check)
    if before.get('status') in ('UNKNOT', 'KNOTTED'):
        return {'status': before['status'], 'gateway': before,
                'method': 'existing-braid-gateway',
                'reduced_input': {'strands': strands, 'word': list(word)}}
    result = compress(strands, word, max_passes=max_passes,
                      dictionary=dictionary, check=check)
    reduced, replay = verify(strands, word, result['certificate'], check=check)
    after = gateway(strands, reduced, check=check) if reduced != word else before
    return {'status': after.get('status', 'INCONCLUSIVE'), 'gateway': after,
            'method': 'ranktwo-verified-braid-gateway',
            'before_gateway': before,
            'ranktwo_certificate': result['certificate'],
            'ranktwo_statistics': result['stats'], 'ranktwo_verification': replay,
            'reduced_input': {'strands': strands, 'word': list(reduced)}}
