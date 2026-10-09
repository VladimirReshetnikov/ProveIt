"""Additive adapter to the inspected ProveIt weighted-AHT API.

The native gate in integration/native_gate.py must pass in the target checkout
before integration. Core tests use a separately named bounded literal backend;
they are NOT a claim that the maintained suite has been executed.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from .profiles import Profiles, cuts_and_lengths, exact_int
from .packing import ProfileCodec


class Inconclusive(RuntimeError):
    pass


def compile_profiles(size, pairings, cuts, *, packing='binary', max_cycles=None,
                     check=None, record_certificate=False, backend=None):
    cuts, lengths = cuts_and_lengths(size, cuts)
    codec = ProfileCodec(lengths, packing)
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be Boolean')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be nonnegative or None')
    poll = check if check is not None else (lambda: None)
    poll()
    pairs = list(pairings)
    intervals = [(cuts[j], cuts[j+1], [codec.units[j]]) for j in range(len(lengths))]
    if backend is None:
        from fastunknot.weighted_orbits import weighted_orbit_histogram
        backend = weighted_orbit_histogram
    answer = backend(size, pairs, intervals, dimension=1, max_cycles=max_cycles,
                     check=poll, record_certificate=record_certificate)
    if answer.get('status') != 'COMPLETE':
        raise Inconclusive('weighted orbit computation did not complete')
    table = codec.table_from_native_histogram(answer['histogram'])
    if table.orbit_count != exact_int(answer['orbit_count']):
        raise ArithmeticError('orbit total differs from decoded census')
    poll()
    result = dict(profiles=table, stats=answer.get('stats', {}))
    if record_certificate:
        if 'certificate' not in answer:
            raise ValueError('the chosen backend did not provide a source certificate')
        result['certificate'] = dict(schema='compiled-port-profiles-v1', size=size,
            cuts=list(cuts), packing=packing, weighted=answer['certificate'])
    return result


def verify_native_certificate(size, pairings, expected_cuts, certificate, *, check=None):
    """Return a newly decoded trusted table, or raise ValueError.

    No separately supplied table is authenticated by a Boolean return value.
    The packing and decoding formulas below do not call ProfileCodec or the
    compilation function. Native weighted replay binds the original pairings.
    """
    poll = check if check is not None else (lambda: None)
    poll()
    cuts, lengths = cuts_and_lengths(size, expected_cuts)
    if (not isinstance(certificate, dict)
            or set(certificate) != {'schema', 'size', 'cuts', 'packing', 'weighted'}
            or certificate['schema'] != 'compiled-port-profiles-v1'
            or exact_int(certificate['size']) != size
            or tuple(exact_int(x) for x in certificate['cuts']) != cuts
            or certificate['packing'] not in ('binary', 'mixed')):
        raise ValueError('compiled certificate source differs')
    radices, intervals, place = [], [], 1
    for j, cap in enumerate(lengths):
        poll()
        if certificate['packing'] == 'mixed':
            radix = cap + 1
        else:
            radix = 2 ** cap.bit_length()
        radices.append(radix)
        intervals.append((cuts[j], cuts[j+1], [place]))
        place *= radix
    from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
    inner = certificate['weighted']
    if not verify_weighted_orbit_certificate(size, list(pairings), intervals, inner,
                                             dimension=1, check=poll):
        raise ValueError('native weighted orbit certificate failed replay')
    hist = {}
    for row in inner['histogram']:
        poll()
        value = exact_int(row['weight'][0])
        if value < 0:
            raise ValueError('negative packed source profile')
        counts = []
        for cap, radix in zip(lengths, radices):
            digit = value % radix
            value //= radix
            if digit > cap:
                raise ValueError('source capacity exceeded')
            counts.append(digit)
        if value or tuple(counts) in hist:
            raise ValueError('invalid or duplicate packed source profile')
        hist[tuple(counts)] = exact_int(row['orbits'])
    return Profiles.from_histogram(lengths, hist)
