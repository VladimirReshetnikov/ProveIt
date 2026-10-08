"""Optional complete Regina recognition in a killable subprocess.

This is an external-engine verdict, not a proof-carrying native certificate.
Import, JSON conversion, process startup and native work share one allowance.
Timeout, missing dependency, worker failure or malformed output is inconclusive.
The parent never loads Regina's native module. Install the optional 'normal'
extra in the same interpreter used to run fastunknot.
"""
from hashlib import sha256
import json
from time import monotonic


def input_digest(pd):
    return sha256(json.dumps(pd, separators=(',', ':')).encode('ascii')).hexdigest()


def regina_pd(diagram):
    """Rotate each row to start at the incoming underpass; label arcs from 1.

    Our convention allows either underpass first. Rotation by 0 or 2
    preserves the planar crossing; a rotation by 1 would switch it.
    """
    return [[label + 1 for label in row[u:] + row[:u]]
            for row, (u, _) in zip(diagram.pd, diagram.incoming_slots())]


class NormalTimeout(RuntimeError):
    pass


class NormalWorkerError(RuntimeError):
    pass


def _invoke(command, payload, expires, check):
    """Communicate once while polling cooperatively, and join all owned work.

    The controlled worker must not leave descendants inheriting these pipes.
    Killing that worker then releases its communication thread on cancellation.
    """
    import subprocess
    from threading import Event, Thread
    completed, outcome, worker = Event(), {}, None

    check()
    if expires is not None and monotonic() >= expires:
        raise NormalTimeout('normal-surface local time allowance exhausted')
    try:
        child = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True)
    except OSError as exc:
        raise NormalWorkerError(str(exc)) from exc
    try:
        def communicate_once():
            try:
                outcome['value'] = child.communicate(payload)
            except BaseException as exc:
                outcome['error'] = exc
            finally:
                completed.set()

        # Retrying communicate(None) after a timeout can strand unsent stdin
        # on supported Python runtimes. Exactly one call owns all three pipes.
        worker = Thread(target=communicate_once,
                        name=f'fastunknot-normal-pipes-{child.pid}', daemon=False)
        try:
            worker.start()
        except (RuntimeError, OSError) as exc:
            raise NormalWorkerError(str(exc)) from exc
        while True:
            check()
            left = None if expires is None else expires-monotonic()
            if left is not None and left <= 0:
                raise NormalTimeout('normal-surface local time allowance exhausted')
            if completed.wait(0.05 if left is None else min(0.05, left)):
                break
        check()
        if expires is not None and monotonic() >= expires:
            raise NormalTimeout('normal-surface local time allowance exhausted')
        if 'error' in outcome:
            exc = outcome['error']
            if isinstance(exc, OSError):
                raise NormalWorkerError(str(exc)) from exc
            raise exc
        output, errors = outcome['value']
        return child.returncode, output, errors
    finally:
        try:
            if child.poll() is None:
                child.kill()
            child.wait()
        finally:
            try:
                # ident remains set after termination, and is None if start
                # failed before launching a thread. No private thread API.
                if worker is not None and worker.ident is not None:
                    worker.join()
            finally:
                for stream in (child.stdin, child.stdout, child.stderr):
                    stream.close()


def regina_decide(diagram, *, seconds=2.0, check=lambda: None):
    """A complete query when uncapped; incomplete attempts return INCONCLUSIVE.

    ``check`` may propagate a global cancellation exception. A local timeout
    is inconclusive. The worker is killed and joined in either case.
    """
    start = monotonic()
    from math import isfinite
    if seconds is not None and (type(seconds) not in (float, int)
            or not isfinite(seconds) or seconds < 0):
        raise ValueError('Regina seconds must be finite and nonnegative, or None')
    expires = None if seconds is None else start+seconds
    check()
    import importlib.util
    import sys
    if importlib.util.find_spec('regina') is None:
        check()
        return dict(status='INCONCLUSIVE', reason='optional regina dependency is not installed',
                    seconds=monotonic()-start)
    digest = input_digest(diagram.pd)
    request = json.dumps(dict(pd=diagram.pd, input_digest=digest))
    try:
        code, output, errors = _invoke([sys.executable, '-B', '-m', 'fastunknot._regina_worker'],
                                      request, expires, check)
    except (NormalTimeout, NormalWorkerError) as exc:
        check()
        return dict(status='INCONCLUSIVE', reason=str(exc), seconds=monotonic()-start)
    check()
    try:
        result = json.loads(output)
        if (code != 0 or type(result) is not dict
                or type(result.get('version')) is not int or result['version'] != 1
                or result.get('engine') != 'regina'
                or type(result.get('engine_version')) is not str
                or type(result.get('distribution_version')) is not str
                or result.get('input_digest') != digest
                or type(result.get('input_crossings')) is not int
                or result['input_crossings'] != diagram.crossings
                or result.get('status') not in ('UNKNOT', 'KNOTTED')
                or type(result.get('simplified_crossings')) is not int
                or not 0 <= result['simplified_crossings'] <= diagram.crossings
                or type(result.get('tetrahedra')) is not int or result['tetrahedra'] <= 0
                or result.get('trust') != 'external-engine verdict; no independently checked normal-surface certificate'):
            raise ValueError('invalid external-engine response')
    except (ValueError, TypeError):
        check()
        return dict(status='INCONCLUSIVE', reason='Regina worker failed or returned invalid evidence',
                    worker_exit=code, seconds=monotonic()-start)
    check()
    if expires is not None and monotonic() >= expires:
        return dict(status='INCONCLUSIVE', reason='normal-surface local time allowance exhausted',
                    seconds=monotonic()-start)
    result['seconds'] = monotonic()-start
    return result
