#!/usr/bin/env python3
"""Rebuild the three recorded209-variable polynomial profiles."""
from pathlib import Path
import argparse,copy,hashlib,json
from build209 import P,terms,add,scale,canonical,save,build,SOURCE

ROOT=Path(__file__).resolve().parent.parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'rebuilt');a=ap.parse_args()
    build(SOURCE,a.output,64)
    eq,_=build(SOURCE,a.output,128)
    carrier=next(i for i,r in enumerate(eq['residuals']) if r['label']=='cap.pooled_index_residue')
    cp=P(eq['residuals'][carrier]['terms']);lead=cp[(2,2)]
    out=copy.deepcopy(eq);edits=[]
    for j,r in enumerate(eq['residuals']):
        if j==carrier:continue
        p=P(r['terms']);c=p.get((2,2),0)
        if not c:continue
        if c%lead:raise ValueError('Nonintegral row operation')
        k=-c//lead;q=add(p,scale(cp,k))
        if q.get((2,2),0):raise ValueError('Square not removed')
        out['residuals'][j]['terms']=terms(q)
        edits.append({'target_row':j,'source_row':carrier,'source_multiplier':k})
    out['variant']=eq['variant']+':single_F_square_carrier'
    cert={'schema':'unimodular-residual-row-certificate-v1','input_sha256':hashlib.sha256(canonical(eq)).hexdigest(),'source_row_unchanged':carrier,'edits':edits,'inverse':'Subtract the same multiple of the unchanged carrier row.','output_sha256':hashlib.sha256(canonical(out)).hexdigest()}
    save(a.output/'affine209_F128_basis',out,cert)

if __name__=='__main__':main()
