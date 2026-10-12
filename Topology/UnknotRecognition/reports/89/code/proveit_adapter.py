"""Opt-in adapter for the inspected ProveIt weighted-orbit API.

Add Topology/UnknotRecognition/fast to PYTHONPATH. This adapter has contract
unit tests here, but was not executed against a full upstream checkout in
this delivery. No source triangulation -> boundary packet adapter is claimed.
"""
import re
from moment_kernel import Incomplete


def make_oracle(*, max_cycles=None, check=None, verify=None, certificates=None):
    from fastunknot.interval_orbits import IntervalPairing
    from fastunknot.weighted_orbits import weighted_orbit_histogram
    if verify is None:
        from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
        def verify(size,pairs,weights,dimension,proof):
            return verify_weighted_orbit_certificate(size,pairs,weights,proof,dimension=dimension,check=check)
    def oracle(size,pairs,weights,dimension):
        native=[IntervalPairing(p.a,p.b,p.c,p.d,p.reverse) for p in pairs]
        answer=weighted_orbit_histogram(size,native,list(weights),dimension=dimension,
                    max_cycles=max_cycles,check=check,record_certificate=True)
        if answer.get('status')!='COMPLETE':raise Incomplete('upstream weighted census incomplete')
        proof=answer.get('certificate')
        if proof is None:raise ValueError('upstream omitted requested certificate')
        # Return only the histogram bound by the independently checked proof.
        if not verify(size,native,list(weights),dimension,proof):
            raise ValueError('upstream weighted proof failed independent replay')
        if certificates is not None:certificates.append(proof)
        def integer(x):
            if type(x) is int:return x
            if type(x) is str and re.fullmatch(r'[+-]?0[xX][0-9a-fA-F]+',x):return int(x,16)
            raise ValueError('unsupported integer encoding')
        return [(tuple(integer(x) for x in row['weight']),integer(row['orbits']))
                for row in proof['histogram']]
    return oracle
