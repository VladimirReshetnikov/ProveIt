#!/usr/bin/env python3
"""Audit the recorded affine physical durations and the stated witness bound.

The frame-resource induction is written in relative_proof.tex. This file
checks its finite coefficient premises and polynomial arithmetic; it does
not replace that argument or claim a proof-assistant theorem.
"""
from pathlib import Path
import argparse,hashlib,json

ROOT=Path(__file__).resolve().parent
EXPECTED_MAXIMA=[534,8,4,4,4,4,4,4,2,4,4,2,2]

def require(ok,message):
    if not ok:raise ValueError(message)

def audit(path):
    data=path.read_bytes();records=json.loads(data)
    receipt=json.loads(path.with_name('receipt.json').read_text())
    require(receipt['status']=='PASS','Literal audit did not pass')
    require(hashlib.sha256(data).hexdigest()==receipt['contracts_sha256'],'Contract hash mismatch')
    require(len(records)==4778,'Wrong number of source outcomes')
    require(all(len(r['duration'])==13 for r in records),'Wrong duration-vector shape')
    require(all(isinstance(x,int)and x>=0 for r in records for x in r['duration']),'Negative or nonintegral coefficient')
    maxima=[max(r['duration'][i]for r in records)for i in range(13)]
    require(maxima==EXPECTED_MAXIMA,'Unexpected coefficient maximum')
    minimum=min(r['duration'][0]for r in records)
    require(minimum==3,'Unexpected progress constant')
    return {'file':str(path),'outcomes':len(records),'column_maxima':maxima,
            'minimum_positive_duration_constant':minimum,
            'contracts_sha256':hashlib.sha256(data).hexdigest()}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('contracts',type=Path,nargs='*')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    paths=a.contracts or[ROOT/('AX11QH'+v)/'independent/contracts.json'for v in('4L','4R')]
    audits=[audit(path)for path in paths]
    # L0 = active-value sum + first-spare value + remaining spare width.
    initial_resource=2+1+25*3
    require(initial_resource==78,'Seed arithmetic failed')
    # Maximal increment effects: active+1, appended B(1) width3, overflow+1.
    resource_increment=1+3+1
    require(resource_increment==5,'Resource arithmetic failed')
    constant=534+8*initial_resource
    slope=8*resource_increment
    require((constant,slope)==(1158,40),'Per-instruction bound failed')
    # A(k+1)-A(k) =1158+40k for A(k)=58088+1138k+20k^2.
    polynomial=[58088,1138,20]
    require([polynomial[1]+polynomial[2],2*polynomial[2]]==[constant,slope],
            'Summed-clock polynomial identity failed')
    rounded=[60000,1200,20]
    require(all(x>=y for x,y in zip(rounded,polynomial)),'Rounded bound is too small')
    result={'status':'PASS','audits':audits,'initial_resource':initial_resource,
            'maximum_resource_increase_per_source_instruction':resource_increment,
            'source_segment_duration_bound':[constant,slope],
            'literal_clock_bound_coefficients':polynomial,
            'rounded_witness_bound_coefficients':rounded,
            'source_instruction_count_includes_final_halt_instruction':True,
            'scope':'Finite coefficient and polynomial checks supporting the written resource induction and relative iPRA witness transfer.'}
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True)
        a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
