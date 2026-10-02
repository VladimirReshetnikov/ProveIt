#!/usr/bin/env python3
"""Finite high-precision sign/coefficient corroboration, not a proof or distance computation."""
import json
import mpmath as mp

# ed. (2026-10-01): the receipt printed below is also written to
# <output-dir>/integer-base-verification.json, by default rerun/ beside this program, with LF line
# endings (as delivered it went only to standard output, and a shell
# redirection on Windows writes CRLF). Pass --output-dir with this program's
# own directory, on a copy, to regenerate the recorded receipt.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))


mp.mp.dps=100
rows=[]
checks=0
for B in (2,3,4,5,6,7):
    for j in range(1,7):
        T=B**j
        q0=mp.mpf(1)/B
        sinc=lambda x: mp.sin(mp.pi*x)/(mp.pi*x) if x else mp.mpf(1)
        P=mp.fprod(sinc(mp.mpf(B)**(-l)) for l in range(1,180))
        sign=-1 if B%2==0 else (-1)**(j+1)
        coefficient=sign*mp.factorial(j)*P
        errors=[]
        for direction in (-1,1):
            delta=direction*mp.mpf('1e-25')
            q=q0+delta
            defect=mp.mpf((-1)**T)/T*mp.fprod(sinc(T*q**i) for i in range(1,j+180))
            ratio=defect/delta**j
            error=abs(ratio/coefficient-1)
            assert error < mp.mpf('1e-15'), (B,j,direction,error)
            assert mp.sign(ratio)==sign
            errors.append(float(error));checks+=1
        rows.append({'base':B,'depth':j,'signed_coefficient':mp.nstr(coefficient,30),'max_relative_error':max(errors)})
result={'status':'PASS','checks':checks,'precision_decimal_digits':100,'bases':[2,3,4,5,6,7],'depths':[1,2,3,4,5,6],'delta_magnitude':'1e-25','tail_product_range':'l=1,...,179; defect factors i=1,...,j+179','scope':'Finite Fourier product sign/coefficient corroboration only; no distance computed and no formal proof.', 'rows':rows}
# ed. (2026-10-01): the receipt is also written by _ed_write (see above).
_ed_text=json.dumps(result,indent=2)
_ed_write('integer-base-verification.json', _ed_text+'\n')
print(_ed_text)
