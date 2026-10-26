#!/usr/bin/env python3
"""Exact source transformations of frozen ProveIt package142 equations."""
from pathlib import Path
from collections import Counter
import json,hashlib

ROOT=Path(__file__).resolve().parent

def transformed(parent_name,mode,degree):
    path=ROOT/'fixed_parents'/parent_name
    parent=json.loads(path.read_text())
    rows=[]
    # General rational carrier uses t=n+(k-R-1)/E, cleared by E^2.
    # The residue carrier instead scales i by E and takes t=En-k+R.
    for name,op,l,r in parent['source']:
        if name in {'hE','index_partial','Nk'}:
            if name=='hE':
                if mode in {'residue','residue_q4'}:
                    if mode=='residue_q4':rows.append(['carrier_q4','*','q2','q2'])
                    modulus='E' if mode=='residue' else 'carrier_q4'
                    rows += [['carrier_En','*',modulus,'n'],
                             ['carrier_En_minus_k','-','carrier_En','k'],
                             ['t','+','carrier_En_minus_k','R']]
                elif mode=='rational':
                    rows += [['carrier_e0','-','k','R'],
                             ['carrier_e','-','carrier_e0',1],
                             ['carrier_En','*','E','n'],
                             ['t','+','carrier_En','carrier_e']]
                else:raise ValueError('Unknown chart')
            continue
        if mode in {'residue','residue_q4'} and name in {'I','iA','base_plus2'}:
            # First consumer of old i may occur under different schedules.
            pass
        if mode in {'residue','residue_q4'} and (l=='i' or r=='i') and not any(x[0]=='carrier_i' for x in rows):
            multiplier='E' if mode=='residue' else 'q2'
            rows.append(['carrier_i','*',multiplier,'i'])
        if mode in {'residue','residue_q4'}:
            l='carrier_i' if l=='i' else l
            r='carrier_i' if r=='i' else r
        if mode=='rational' and name=='GV2':
            root=l
            if root not in {'A','G'}:raise ValueError('Unexpected root product')
            rows += [['carrier_E2','*','E','E'],
                     ['carrier_G','*','carrier_E2',root]]
            l='carrier_G'
        if mode=='rational' and name=='Eprod':
            if op!='+' or r not in {'A','G'}:raise ValueError('Unexpected residual')
            r='carrier_G'
        if name=='prod0':
            if [op,l,r]!=['*','N1','Nk']:raise ValueError('Unexpected product boundary')
            continue
        if name=='prod1':
            if [op,l,r]!=['*','prod0','Nt']:raise ValueError('Unexpected product boundary')
            l='N1'
        rows.append([name,op,l,r])
    witnesses=['n' if x=='h' else x for x in parent['witnesses'] if x!='t']
    binding=json.loads((ROOT/'fixed_parents/parents/COEFFICIENT_BINDING.json').read_text())
    binding['path']='coefficients/'
    binding['recipe']='rebuild_fixed_coefficients.py'
    binding['ordinary_proof']='FIXED_CARRIER_PROOF.md'
    # Compression framing is irrelevant to the integer leaves. Original
    # gzip digests remain in the frozen parent; current byte digests are
    # supplied in COEFFICIENTS.json after materialization.
    for port in binding['ports'].values():port.pop('gzip_sha256',None)
    output={
        'name':f'fixed_{len(witnesses)}_{mode}_{len(rows)}_degree{degree}',
        'domain':'strictly positive integers','witnesses':witnesses,
        'fixed_numerals':parent['fixed_numerals'],
        'coefficient_binding':binding,
        'source':rows,'output':parent['output'],
        'operations':len(rows),'operation_counts':dict(Counter(r[1] for r in rows)),
        'exact_degree':degree,'parent':str(path.relative_to(ROOT)),
        'parent_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'transformation':mode,
        'proof':'FIXED_CARRIER_PROOF.md',
        'proof_status':'Ordinary unbounded proof relative to the retained package142/P66 calibration; no newly checked end-to-end Lean/Rocq or encoded object-ZFC proof.',
    }
    return output

def main():
    profiles=[('equation_14_raw.json','residue',206,70),
              ('equation_14_reduced.json','residue',162,71),
              ('equation_14_reduced.json','residue_q4',154,72),
              ('equation_13_anchored.json','rational',438,74)]
    out=[]
    for filename,mode,degree,ops in profiles:
        packet=transformed(filename,mode,degree)
        if packet['operations']!=ops:raise ValueError((filename,packet['operations'],ops))
        name=packet['name']+'.json'
        (ROOT/name).write_text(json.dumps(packet,indent=2)+'\n')
        out.append({'file':name,'variables':len(packet['witnesses']),
                    'operations':ops,'degree':degree,
                    'counts':packet['operation_counts']})
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
