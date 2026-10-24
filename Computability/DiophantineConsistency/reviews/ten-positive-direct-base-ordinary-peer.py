#!/usr/bin/env python3
"""Independent free-ring carrier cuts and ordinary-proof pins.

Imports no direct-base producer, probe or checker. The unbounded proof
review is in the adjacent Markdown; finite algebra checks transcription.
"""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/ten-positive-short-projection'
PROOF=ROOT/'candidates/ten-positive-direct-base/PROOF.md'
PROOF_SHA='9d1f148551e925e79834039599e0be317c2c1b59eb08b50eaf704fbfa70b9af3'

def need(ok,message):
    if not ok:raise ValueError(message)

def sha(path):return sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    need(sha(PROOF)==PROOF_SHA,'exact ordinary proof reviewed')
    helper=PARENT/'source/independent_norm_oracle.py'
    need(sha(helper)=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83','frozen independent polynomial collector')
    spec=importlib.util.spec_from_file_location('free_carrier_polynomials',helper)
    o=importlib.util.module_from_spec(spec);spec.loader.exec_module(o)
    o.ZERO=(0,)*14
    def var(j):return o.Poly({tuple(int(i==j)for i in range(14)):1})
    q,H,mu,n,V,K,Y,Wo,Wn,B,e,t,u,X=[var(j)for j in range(14)]
    Po=q**3*(q-1);Pn=q*Po;dw=Wn-Wo
    Zo=Po*mu**2*(H*(n+V)+K)+H*(mu**2*((q-1)*Y-q**3*Wo*B)-Po*e)
    Zn=Pn*mu**2*(H*(n+dw*t+u+V)+K)+H*(mu**2*(q*(q-1)*Y-q**4*Wn*B-(q-1)*X)-Pn*e)
    cut=H*mu**2*(q**4*dw*((q-1)*t-B)+(q-1)*(q**4*u-X))
    need(not(Zn-q*Zo-cut).t,'entire14-free-variable center identity with two explicit quotient licenses')
    numerator=q*(q-1)*Y-q**3*Wn*B-(q-1)*X
    need(not(numerator-X-q*((q-1)*Y-q**2*Wn*B-X)).t,'modq remainder isX only after removingHdenominator')
    need(not((q*K+q*X)*Y-q*V-q*((K+X)*Y-V)).t,'clearednative transportB=q*Bt whenXold=q*w')
    # Free weighted norm homogeneity, not a modular sample of a whole output.
    o.ZERO=(0,)*6
    def v6(j):return o.Poly({tuple(int(i==j)for i in range(6)):1})
    s,a,b,c,z,_=[v6(j)for j in range(6)]
    tail=json.loads((PARENT/'equation.json').read_bytes())['source'][-13:]
    old=o.evaluate(tail,dict(fs=s,fa=9*a,fb=b,fc=c))['N']
    scaled=o.evaluate(tail,dict(fs=z*z*s,fa=9*z*z*a,fb=z*z*b,fc=z*z*c))['N']
    need(not(scaled-z**8*old).t,'fullweightednormoutputscalesbyq8')
    need(all(5*r-30>4*r+4 for r in range(35,1000)),'heightthresholddiagnostics')
    need(all(4*k<=2**k for k in range(4,100)),'powerthresholddiagnostics')
    files=[PROOF,PARENT/'PROOF.md',helper,Path(__file__)]
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),
        complete_free_center_cut_variables=14,exact_quotient_license_conditions=['(q-1)*t=Bt','q^4*u=X'],
        independent_modq_carrier_remainder=True,independent_cleared_transport_identity=True,
        complete_weightednorm_homogeneity=True,whole_product_height_threshold_r=35,
        actual_r_lower_bound=48,source_pins={str(f.relative_to(ROOT)):sha(f)for f in files},
        scope='Independent ordinary review plus universal carrier/norm algebra. Full literal107-row cuts, payloads/count and exactdegree340 remain separate materialized-packet checks; finite threshold controls do not replace the unbounded inequalities.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n';args.output.write_text(text);print(text,end='')

if __name__=='__main__':main()
