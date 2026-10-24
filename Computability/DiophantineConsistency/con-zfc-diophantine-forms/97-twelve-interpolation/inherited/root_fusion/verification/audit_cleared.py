#!/usr/bin/env python3
"""Exact generic comparison with the independently audited F32 coefficients."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
import hashlib,json,time
from five_square_norm import cleared_norm5,cleared_norm5_scaled
from exact_polynomial import Ring

ROOT=Path(__file__).resolve().parent
def main():
    start=time.monotonic()
    ring=Ring(['x','a','b','c','d','cn','delta'])
    variables=[ring.var(s) for s in ring.names]
    actual=cleared_norm5(*variables)
    original=json.loads((ROOT/'five_square_norm_expanded.json').read_text())
    expected={}
    for m,coefficient in original['terms']:
        exponents=tuple(m[:5]+[m[5],16-m[5]])
        if exponents[-1]<0:raise ValueError('uncleared denominator')
        expected[exponents]=coefficient
    if actual.terms!=expected:raise ValueError('cleared F32 identity failed')
    alternate=cleared_norm5_scaled(*variables)
    if alternate.terms!=expected:raise ValueError('alternative denominator scaling failed')
    if actual.terms.get((0,0,0,0,0,16,0))!=1:raise ValueError('cn^16 coefficient')
    if actual.terms.get((32,0,0,0,0,0,16))!=1:raise ValueError('x^32 delta^16 coefficient')
    encoded=json.dumps([[list(m),c] for m,c in sorted(expected.items())],separators=(',',':'))
    receipt={'identity':'cleared_norm5(x,a,b,c,d,cn,delta) = delta^16 F32(x;a,b,c,d,cn/delta)',
      'method':'Both cleared norm implementations expand exactly to the transformed independently audited full F32 coefficient dictionary.',
      'monomials':len(expected),'coefficient_sha256':hashlib.sha256(encoded.encode()).hexdigest(),
      'cn16_coefficient':1,'x32_delta16_coefficient':1,'seconds':round(time.monotonic()-start,3)}
    (ROOT/'CLEARED_EXACT_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
