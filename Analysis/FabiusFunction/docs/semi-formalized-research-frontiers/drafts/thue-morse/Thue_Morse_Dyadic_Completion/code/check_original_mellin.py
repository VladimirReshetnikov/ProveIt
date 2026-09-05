#!/usr/bin/env python3
"""Cross-check a stored zero against the ORIGINAL Mellin numerator.

Unlike the root solver in verify.py, this integrand contains neither Phi
nor the Fourier profile. The input root is rounded in the JSON file, so
its residual reflects both that rounding and numerical quadrature error.
This script does not provide a rigorous interval enclosure.
"""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp
from verify import Completion

def main():
    root_dir=Path(__file__).resolve().parents[1]
    data=json.loads((root_dir/'data/verification_60dps.json').read_text())
    model=Completion(70)
    entry=data['Dirichlet_zeros'][0]
    z=mp.mpc(entry['zero_real'],entry['zero_imag'])
    m=entry['m'];s=z+m
    results={}
    for a in [mp.mpf('0.5'),mp.mpf(1)]:
        def integrand(v):
            t=mp.exp(v)
            return mp.exp(z*v-a*t+model.log_p(t))
        numerator=mp.quad(integrand,[-24,-12,-8,-4,0,4,8,16])
        normalized=mp.power(2,-m*(m-1)/2+m*s)*numerator
        results[str(a)]={
            'direct_M_residual':mp.nstr(abs(numerator),12),
            'direct_normalized_residual':mp.nstr(abs(normalized),12),
            'D_residual':mp.nstr(abs(numerator/mp.gamma(z)),12),
        }
    target=root_dir/'data/direct_original_mellin_check.json'
    target.write_text(json.dumps(results,indent=2)+'\n')
    print(target.read_text())

if __name__=='__main__':main()
