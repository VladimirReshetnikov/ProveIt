"""Opt-in run-encoded braid research frontend.

Usage: python -m fastunknot.twist.continuation input.json

Input is {"strands": b, "runs": [[generator, signed_exponent], ...]}.
An explicit "word" array may replace "runs". Integer fields also accept
signed hexadecimal strings; large outputs use exact hexadecimal transport.
The default is recognition with structural certificates first and the tail
backend after an inconclusive certificate. Homology mode always computes the
selected exact homology, even if a cheaper certificate would decide the knot.
Profile mode returns only the original braid's structural certificate.
Existing production entrypoints and their defaults are unchanged.
"""
from __future__ import annotations

import argparse
from dataclasses import replace
import json
from pathlib import Path
import sys
from time import monotonic
from typing import Iterable

from ..braid_profile import structural_runs_certificate
from ..integer_codec import encoded_integer, json_safe
from . import core, streaming
from .core import Budget, ResourceLimit, Run, components, runs_from_word, validate_runs
from .streaming import StreamBudget
from .tail import tail_homology, tail_recognize


def load_runs(value: dict) -> tuple[int, tuple[Run, ...]]:
    """Validate runs or an explicit word, without expanding any exponent."""
    if not isinstance(value, dict):
        raise ValueError('input must be a JSON object')
    data = value.get('braid', value)
    if not isinstance(data, dict) or 'strands' not in data:
        raise ValueError('expected strands; PD and grid inputs are not supported')
    if ('word' in data) == ('runs' in data):
        raise ValueError('provide exactly one of word or runs')
    strands = encoded_integer(data['strands'])
    if 'word' in data:
        if not isinstance(data['word'], list):
            raise ValueError('word must be a list of signed generators')
        return strands, runs_from_word(strands, (encoded_integer(x) for x in data['word']))
    pairs = data['runs']
    if not isinstance(pairs, list) or any(
        not isinstance(pair, list) or len(pair) != 2 for pair in pairs
    ):
        raise ValueError('runs must be [positive_generator, nonzero_signed_exponent] pairs')
    return strands, validate_runs(strands, (
        Run(encoded_integer(g), encoded_integer(e)) for g, e in pairs))


def compute(strands: int, runs: Iterable[Run], *, mode: str = 'recognize',
            method: str = 'tail', budget: Budget | StreamBudget | None = None,
            run_index: int | None = None, check_d2: bool = False) -> dict:
    """Run one exact workflow, with UNKNOWN reserved for resource exhaustion.

    ``budget`` is Budget for tail/macro or StreamBudget for streaming. The
    seconds ceiling covers the structural check and the chosen backend.
    Recognition permits streamed early rejection once finalized homology
    dimensions sum to more than one. Its returned homology then explicitly
    reports a lower bound and ``homology_complete=False``.
    """
    if mode not in {'recognize', 'homology', 'profile'}:
        raise ValueError('mode must be recognize, homology, or profile')
    if method not in {'tail', 'streaming', 'macro'}:
        raise ValueError('method must be tail, streaming, or macro')
    runs = validate_runs(strands, runs)
    if run_index is not None:
        if method != 'tail':
            raise ValueError('run_index is only used by the tail backend')
        if type(run_index) is not int or not 0 <= run_index < len(runs):
            raise ValueError('run_index must index one of the supplied runs')
    budget_class = StreamBudget if method == 'streaming' else Budget
    if budget is not None and not isinstance(budget, budget_class):
        raise ValueError(f'{method} requires {budget_class.__name__}')
    cap = budget_class() if budget is None else replace(budget)
    start = monotonic()
    deadline = None if cap.seconds is None else start + cap.seconds

    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ResourceLimit('time budget exhausted')

    certificate = None
    try:
        check()
        if mode != 'homology':
            if components(strands, runs) != 1:
                raise ValueError('recognition and structural profiles require a one-component closure')
            certificate = structural_runs_certificate(
                strands, ((r.generator, r.exponent) for r in runs), check=check)
            check()
            if mode == 'profile':
                return {
                    'mode': 'profile', 'status': certificate['status'],
                    'certificate': certificate, 'seconds': monotonic()-start,
                }
            if certificate['status'] in {'UNKNOT', 'KNOTTED'}:
                return {
                    'status': certificate['status'], 'method': 'structural-braid',
                    'requested_backend': method, 'certificate': certificate,
                    'seconds': monotonic()-start,
                    'unrestricted_quasipolynomial_guarantee': False,
                }
        check()
        if deadline is not None:
            cap = replace(cap, seconds=max(0.0, deadline-monotonic()))
        if mode == 'homology':
            if method == 'tail':
                result = tail_homology(strands, runs, run_index=run_index,
                                       budget=cap, check_d2=check_d2)
            elif method == 'streaming':
                result = streaming.homology(strands, runs, budget=cap,
                                             check_d2=check_d2)
            else:
                result = core.homology(strands, runs, budget=cap,
                                       check_d2=check_d2)
            check()
            return {
                'status': 'COMPUTED', 'mode': 'homology', 'method': method,
                'homology_complete': True, 'homology': result,
                'seconds': monotonic()-start,
                'unrestricted_quasipolynomial_guarantee': False,
            }
        if method == 'tail':
            result = tail_recognize(strands, runs, run_index=run_index,
                                    budget=cap, check_d2=check_d2)
        elif method == 'streaming':
            result = streaming.recognize(strands, runs, budget=cap,
                                          check_d2=check_d2)
        else:
            result = core.recognize(strands, runs, budget=cap,
                                    check_d2=check_d2)
        check()
        result['certificate'] = certificate
        result['requested_backend'] = method
        result['seconds'] = monotonic()-start
        return result
    except (ResourceLimit, MemoryError) as exc:
        result = {
            'status': 'UNKNOWN', 'method': method, 'mode': mode,
            'reason': str(exc) or 'memory allocation failed',
            'seconds': monotonic()-start,
            'unrestricted_quasipolynomial_guarantee': False,
        }
        if certificate is not None:
            result['certificate'] = certificate
        return result


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', help='JSON file, or - to read standard input')
    parser.add_argument('--mode', choices=('recognize', 'homology', 'profile'),
                        default='recognize')
    parser.add_argument('--method', choices=('tail', 'streaming', 'macro'),
                        default='tail')
    parser.add_argument('--run-index', type=int,
                        help='zero-based selected tail run; default chooses the largest')
    parser.add_argument('--check-d2', action='store_true',
                        help='check d squared; tail checks its finite reference complex')
    parser.add_argument('--seconds', type=float,
                        help='cooperative wall-clock ceiling including structural checking')
    for flag, default in (('max-states', 250_000), ('max-basis', 1_000_000),
                          ('max-xors', 20_000_000)):
        parser.add_argument('--'+flag, type=int, default=default)
    parser.add_argument('--max-matrix-bits', type=int, default=1_000_000_000,
                        help='assembled-matrix envelope for tail/macro only')
    for flag, default in (('max-live-matrix-bits', 1_000_000_000),
                          ('max-live-states', 250_000),
                          ('max-layer-basis', 1_000_000),
                          ('max-live-columns', 2_000_000)):
        parser.add_argument('--'+flag, type=int, default=default,
                            help='streaming backend only')
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        raw = sys.stdin.read() if args.input == '-' else Path(args.input).read_text(encoding='utf-8')
        strands, runs = load_runs(json.loads(raw))
        common = dict(max_states=args.max_states, max_basis=args.max_basis,
                      max_xors=args.max_xors, seconds=args.seconds)
        if args.method == 'streaming':
            budget = StreamBudget(
                **common, max_live_matrix_bits=args.max_live_matrix_bits,
                max_live_states=args.max_live_states,
                max_layer_basis=args.max_layer_basis,
                max_live_columns=args.max_live_columns,
            )
        else:
            budget = Budget(**common, max_matrix_bits=args.max_matrix_bits)
        result = compute(strands, runs, mode=args.mode, method=args.method,
                         budget=budget, run_index=args.run_index,
                         check_d2=args.check_d2)
        encoded = json.dumps(json_safe(result), indent=2, sort_keys=True)
    except (OSError, ValueError, TypeError) as exc:
        print(json.dumps({'status': 'INVALID', 'reason': str(exc)}))
        return 2
    except (ResourceLimit, MemoryError) as exc:
        print(json.dumps({'status': 'UNKNOWN', 'reason': str(exc) or 'memory allocation failed'}))
        return 3
    print(encoded)
    return 3 if result.get('status') == 'UNKNOWN' else 0


if __name__ == '__main__':
    sys.exit(main())
