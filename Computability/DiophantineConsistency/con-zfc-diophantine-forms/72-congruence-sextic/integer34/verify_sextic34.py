#!/usr/bin/env python3
"""Verify the readable equation, exact coefficient recipe and source hashes."""
import gzip
import hashlib
import json
import shutil
import tempfile
from pathlib import Path
import build_sextic34 as build

HERE=Path(__file__).resolve().parent

def need(test,message):
    if not test: raise ValueError(message)

def main():
    pins=json.loads((HERE/'UPSTREAM_FILES.json').read_text())
    for record in pins['files']:
        raw=(HERE/record['local_path']).read_bytes()
        need(hashlib.sha256(raw).hexdigest()==record['sha256'],'Source hash '+record['local_path'])
        need(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==record['git_blob'],'Source blob '+record['local_path'])
    source=json.loads((HERE/'sextic34.json').read_text())
    syms=source['variables']+source['fixed_numerals']
    alg=build.mod.Poly(syms)
    aliases={'q':'(beta*J+1)','k':'(eta+zeta)','C':'(beta*J+1-F-alpha)','H':'(4*a+3)'}
    readable=[
      'L-q*q+1', '2*u*u-4*w_scale*q',
      'a-E-(2*v_scale+1)*q*(L+1)', 'E*(2*u*u+1)-2*u*u*a',
      'c-eta-(a-E)*k', 'tau*tau+(2*tau-k)*E*(c-eta)-1',
      'D-2*u*u-gamma*H', 'D*D+2*a*c*D-H*c*c-1',
      'k-1-h*E-(((q-1)*(q-F)+alpha)*L+(MC+q*MF)*J)',
      '(K0+4*w_scale)*C-F-z*(q-1)', 'F2-f*f',
      'f*o-c-j*c+k-1-h*E', 'g+F2*o*o-2*f*o*c+c*c-y*y',
      'I-(2*r+1)*c*c', 'I*I-(a*a+4*a+3)*(F2-1)',
      'y*y-I*I*g-1',
      'F*alpha-1-FA_pos1**2-FA_pos2**2-FA_pos3*(FA_pos3+1)',
      'F*C-1-FC_pos1**2-FC_pos2**2-FC_pos3*(FC_pos3+1)',
      'eta*zeta-1-eta_zeta_pos1**2-eta_zeta_pos2**2-eta_zeta_pos3*(eta_zeta_pos3+1)'
    ]
    for index,(a,b) in enumerate(zip(readable,source['residuals'])):
        need(alg.parse(build.substitute_text(a,aliases))==alg.parse(b),'Readable residual '+str(index+1))
    need(len(readable)==len(source['residuals'])==19,'Residual count')
    expanded={}
    for row in source['residuals']:
        p=alg.parse(row); expanded=alg.add(expanded,alg.mul(p,p))
    expansion={'symbols':syms,'coefficient_ports':source['fixed_numerals'],
       'fixed_binding':source['coefficient_binding'],
       'terms':[{'exponents':list(m),'coefficient':c} for m,c in sorted(expanded.items())]}
    (HERE/'sextic34_expanded.json').write_text(json.dumps(expansion,indent=2)+'\n')
    with tempfile.TemporaryDirectory(prefix='sextic34_coefficients_') as temp:
        tmp=Path(temp);(tmp/'upstream').mkdir();(tmp/'coefficients').mkdir()
        for name in ['wang943_tiles.json','PAYLOAD_BINDING.json']:
            shutil.copyfile(HERE/'upstream'/name,tmp/'upstream'/name)
        old=build.mod.ROOT;build.mod.ROOT=tmp
        try: _, facts=build.mod.build_coefficients()
        finally:build.mod.ROOT=old
        for name in ['beta','K','MC','MF_source']:
            original=gzip.decompress((HERE/'coefficients'/f'{name}.bin.gz').read_bytes())
            actual=gzip.decompress((tmp/'coefficients'/f'{name}.bin.gz').read_bytes())
            need(actual==original,'Exact reconstructed numeral '+name)
    receipt={'source_files_verified':len(pins['files']),
      'all_19_readable_formulas_match_exact_packet':True,
      'coefficient_recipe':facts,'expanded_symbolic_port_terms':len(expanded),
      'verification_scope':'Finite exact identities, source/file integrity and numeral regeneration; no unbounded proof search.'}
    (HERE/'SEXTIC34_VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
