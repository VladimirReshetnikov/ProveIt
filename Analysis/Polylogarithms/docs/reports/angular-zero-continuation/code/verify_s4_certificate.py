"""Deterministically verify the S4 identity certificate over the rationals.

No numerical period evaluations, modular arithmetic, prime choices, rank
assumptions, external algebra packages, or stored matrix rows are trusted.
Only the generating relation labels and rational coefficients are read.
Every row, including the target, is rebuilt from the word definitions.
"""
import json
from pathlib import Path
from collections import Counter
from fractions import Fraction
from octet import ds,octa,imag,target,coords,add

ROOT=Path(__file__).resolve().parent.parent/'data'

def verify(path=ROOT/'s4_exact_certificate.json'):
    cert=json.loads(Path(path).read_text())
    assert [tuple(w) for w in cert['coordinates']]==list(coords(5))
    total=Counter();counts=Counter();maxlen=0
    for item in cert['rows']:
        label=item['label'];kind=label[0]
        if kind=='ds':
            assert len(label[1])+len(label[2])==5
            row=ds(tuple(label[1]),tuple(label[2]))
        elif kind=='octa':
            assert len(label[1])==5
            row=octa(tuple(label[1]))
        else:raise AssertionError('Unrecognized relation generator')
        row=imag(row);c=Fraction(item['coefficient'])
        for w,a in row.items():add(total,w,c*a)
        counts[kind]+=1;maxlen=max(maxlen,len(row))
    assert dict(total)==dict(target()), 'The exact rational word identity failed.'
    print('PASS: exact S4 word certificate')
    print('Coordinate count:',len(coords(5)))
    print('Nonzero generating rows:',dict(counts))
    print('Largest row support:',maxlen)
    print('Arithmetic: Python integers and fractions.Fraction only')
    return dict(counts)

if __name__=='__main__':verify()
