#!/usr/bin/env python3
"""Generate and audit the 41-integer quartic; standard Python only."""
from pathlib import Path
import hashlib
import json
import re
from build_verify44 import ROOT, Poly, require, digest, write_json, build_coefficients

def build():
    raw=(ROOT/'upstream/quartic45.json').read_bytes()
    source=json.loads(raw)
    discard={'q_half_root'}|{f'{a}_pos{i}' for a in ('eta','zeta') for i in range(1,4)}
    variables=[('w_scale' if x=='w' else x) for x in source['variables'] if x not in discard]
    variables += ['eta_zeta_pos1','eta_zeta_pos2','eta_zeta_pos3']
    residuals=[]
    for i,row in enumerate(source['residuals']):
        if i in (23,24,25): continue
        if i==22: row='X-2*u**2'
        residuals.append(re.sub(r'\bw\b','(4*w_scale)',row))
    residuals.append('eta*zeta-eta_zeta_pos1**2-eta_zeta_pos2**2-eta_zeta_pos3*(eta_zeta_pos3+1)-1')
    out=dict(name='quartic41_delayed_sign_and_large_scale',domain='unrestricted integers',
        variables=variables,variable_count=len(variables),equation_count=len(residuals),
        fixed_numerals=['beta','K0','MC','MF'],residuals=residuals,
        single_polynomial='sum of squares of the 26 listed residuals',exact_degree=4,
        coefficient_binding=dict(backend='mixed-parity-unrounded-1064921',
            inherited_manifest='upstream/PAYLOAD_BINDING.json',
            ports={'beta':'coefficients/beta.bin.gz','K0':'coefficients/K.bin.gz',
                   'MC':'coefficients/MC.bin.gz','MF':'coefficients/MF_source.bin.gz'},
            format='gzip of minimal unsigned little-endian integer bytes',
            mask_convention='MF is already shifted by beta'),
        parent_sha256=digest(raw),source_pin='beb0192cb8dc36f78c369c080f2adfbc1887a486',
        proof='PROOF41.md',status='Ordinary mathematical proof using named inherited compiler/Pell dependencies; not a new kernel certificate')
    require(out['variable_count']==41 and out['equation_count']==26,'new counts')
    write_json(ROOT/'quartic41.json',out)
    return out

def audit(out):
    variables=out['variables']; n=len(variables)
    algebra=Poly(variables+out['fixed_numerals'])
    rows=[algebra.parse(x) for x in out['residuals']]
    degrees=[max(sum(k[:n]) for k in r) for r in rows]
    require(degrees==[2]*26,'all residuals quadratic')
    live={variables[i] for r in rows for k in r for i in range(n) if k[i]}
    require(live==set(variables),'all 41 unknowns live')
    sos={}
    for row in rows: sos=algebra.add(sos,algebra.mul(row,row))
    require(max(sum(k[:n]) for k in sos)==4,'quartic total degree')
    key=list(algebra.zero);key[algebra.index['tau']]=4
    require(sos.get(tuple(key),0)==1,'tau^4 coefficient')
    q='(beta*J+1)'
    require(rows[2]==algebra.parse('X-4*w_scale*'+q),'global-scale identity')
    require(rows[22]==algebra.parse('X-2*u**2'),'twice-square identity')
    R=f'(({q}-1)*({q}-F)+alpha)*L+(MC+{q}*MF)*J'
    direct=algebra.parse('eta+zeta-1-h*E-('+R+')')
    relation=algebra.parse('N-'+q+'*(L+1)')
    require(algebra.add(rows[12],direct,-1)==algebra.mul(algebra.parse('F-'+q),relation),
        'literal index/packing identity')
    transport=algebra.parse('(K0+4*w_scale)*('+q+'-F-alpha)-z*('+q+'-1)-F')
    require(rows[13]==transport,'literal transport')
    # Independent exact affine substitution comparison against generated Q44.
    q44=json.loads((ROOT/'quartic44.json').read_text())
    transformed=[]
    for i,row in enumerate(q44['residuals']):
        if i in (23,24): continue
        transformed.append(algebra.parse(re.sub(r'\bw\b','(4*w_scale)',row)))
    require(rows[:-1]==transformed,'all retained Q44 rows under w=4 w_scale')
    require(rows[-1]==algebra.parse('eta*zeta-1-eta_zeta_pos1**2-eta_zeta_pos2**2-eta_zeta_pos3*(eta_zeta_pos3+1)'),
        'new product positivity guard')
    # Finite numerical illustrations of universal bounds, not proof by samples.
    sign_count=0
    for Q in range(16,81):
        upper=Q**4-2
        minimum_E=4*Q**4
        require(minimum_E>3*upper+1,'strict margin E>3R+1')
        for Rval in [Q*(Q*Q-1)+1,upper]:
            require(minimum_E-Rval-1>2*Rval,'negative-K index contradiction')
            sign_count+=1
    # Certificates are literal sparse integer polynomials in named variables/ports.
    expansion=[{'powers':{algebra.variables[i]:e for i,e in enumerate(k) if e},'coefficient':v}
               for k,v in sorted(sos.items())]
    write_json(ROOT/'certificates/QUARTIC41_EXPANSION.json',expansion)
    result=dict(variable_count=n,residual_count=len(rows),residual_degrees=degrees,
        exact_single_polynomial_degree=4,tau_fourth_coefficient=1,
        expanded_monomials_with_symbolic_ports=len(sos),all_variables_live=True,
        retained_rows_exact_affine_substitution=True,packing_identity=True,
        transport_identity=True,finite_sign_margin_cases=sign_count,
        semantic_proof='PROOF41.md + PROOF44.md and named inherited Pell/compiler results')
    write_json(ROOT/'certificates/QUARTIC41_CHECKS.json',result)
    return result

def main():
    for record in json.loads((ROOT/'SOURCE_PINS.json').read_text()):
        raw=(ROOT/record['file']).read_bytes()
        actual=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(actual==record['git_blob'],'source Git blob: '+record['file'])
    _,coefficients=build_coefficients()
    write_json(ROOT/'certificates/COEFFICIENT_CHECKS.json',coefficients)
    print(json.dumps(audit(build()),indent=2))

if __name__=='__main__': main()
