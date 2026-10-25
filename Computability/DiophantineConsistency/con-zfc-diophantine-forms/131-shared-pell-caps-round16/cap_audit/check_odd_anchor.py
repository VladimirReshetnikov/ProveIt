#!/usr/bin/env python3
"""Finite controls of odd scale and signed comparison centers."""
from pathlib import Path
import json
from check_signed_cap import pell,need

def main():
    counts={'odd_scale_congruence':0,'odd_anchor_comparison':0,'negative_comparison_base':0}
    for W in range(1,50):
        for j in range(60):
            need((pell(W+1,j)[1]-j)%(2*W)==0,'odd scale congruence')
            counts['odd_scale_congruence']+=1
    for A in range(2,6):
        for W in range(2,4):
            U,Y=pell(A,W);H,J=pell(A,2*W*Y)
            need(J%(Y*Y)==0 and H%2==1,'common pair construction')
            M=8*J;r=1+4*J;B=r+M*((A-r)*pow(M,-1,H)%H)
            for shift in [-1,0,1]:
                BB=B+shift*M*H;S,R=pell(BB,W)
                need(abs(BB)>=3 and (BB-1)%(4*J)==0 and ((BB-1)//(4*J))%2==1,'odd comparison base')
                need((BB-A)%H==0 and (S-U)%H==0 and (R-W)%(4*Y)==0,'comparison residue correctness')
                counts['odd_anchor_comparison']+=1;counts['negative_comparison_base']+=BB<0
    return {'status':'passed','counts':counts,'scope':'Finite odd-frame and signed comparison-base checks; unbounded proof in FINAL_AUDIT.md.'}
if __name__=='__main__':
    out=main();Path(__file__).with_name('ODD_ANCHOR_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
