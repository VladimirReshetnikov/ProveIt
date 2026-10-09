"""Verify saved source-bound examples without running a count producer."""
from bootstrap import bootstrap
ROOT=bootstrap()
from fastunknot.interval_orbits import IntervalPairing, SignedPairing
from fastunknot.integer_codec import encoded_integer
from fastunknot.sparse_incidence_verify import (
    verify_sparse_port_incidence_certificate as verify,
    verify_sparse_signed_incidence_certificate as signed_verify)
import json,sys,time
from pathlib import Path


def pairing(row):
    a,b,c,d,sign=map(encoded_integer,row)
    if sign not in (-1,1):raise ValueError('invalid pairing sign')
    return IntervalPairing(a,b,c,d,sign==-1)


def main():
    paths=[Path(p) for p in sys.argv[1:]] or sorted((ROOT/'examples').glob('*.json'))
    receipt=[]
    for path in paths:
        item=json.loads(path.read_text())
        n=encoded_integer(item['size']);ports=item['ports'];cert=item['certificate']
        start=time.perf_counter()
        if 'signed_pairings' in item:
            pairs=[SignedPairing(pairing(s['pairing']),encoded_integer(s['parity'])) for s in item['signed_pairings']]
            ok=signed_verify(n,pairs,ports,cert)
        else:
            pairs=[pairing(r) for r in item['pairings']]
            ok=verify(n,pairs,ports,cert)
        receipt.append(dict(file=path.name,accepted=ok,seconds=time.perf_counter()-start))
        print(path.name, 'ACCEPTED' if ok else 'REJECTED')
    (ROOT/'results/examples_replay.json').write_text(json.dumps(receipt,indent=2))
    if not paths or not all(r['accepted'] for r in receipt):raise SystemExit(1)
if __name__=='__main__':main()
