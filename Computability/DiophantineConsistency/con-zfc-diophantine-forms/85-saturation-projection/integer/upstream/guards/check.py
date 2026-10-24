#!/usr/bin/env python3
"""Independent exact comparisons to the literal source70 packets and authentic bytes."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json
import sympy as s
ROOT=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok: raise ValueError(msg)

def main():
    receipt=json.loads((ROOT/'UPSTREAM_COPY_RECEIPT.json').read_text())
    for name,digest in receipt['sha256'].items():
        need(hashlib.sha256((ROOT/'upstream'/name).read_bytes()).hexdigest()==digest,'upstream source digest '+name)
    binding=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text());values={}
    for port,record in binding['payloads'].items():
        packed=(ROOT/record['path']).read_bytes();raw=gzip.decompress(packed)
        need(hashlib.sha256(packed).hexdigest()==record['gzip_sha256'],'gzip payload '+port)
        need(hashlib.sha256(raw).hexdigest()==record['raw_sha256'],'raw payload '+port)
        need(len(raw)==record['raw_bytes'] and raw[-1]!=0,'minimal raw payload '+port)
        values[port]=int.from_bytes(raw,'little')
        need(values[port].bit_length()==record['bits'],'payload bits '+port)
    native=json.loads((ROOT/'upstream/residue/dependencies/PAYLOAD_BINDING.json').read_text())
    for port,source in {'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}.items():
        need(binding['payloads'][port]['raw_sha256']==native['payloads'][source]['sha256'],'entire inherited tuple identity '+port)
    need(values['beta']==2**1064921-1 and values['beta']%3==1,'Mersenne parity')
    need(values['cone_A']==2**1113 and values['cone_B']==2**666104,'determinant fixed scales')
    T=values['K0']-values['beta']*2**121+1
    need(values['Walpha']==2*T*2**398816 and values['WC']==T*values['beta'],'cone fixed scales')
    out=[]
    for kind in ('determinant','cone'):
      for suffix,oldname,dimensions in [('37_quartic_direct','quartic40_direct.json',(37,24,4)),('37_quartic_affine','quartic40.json',(37,24,4)),('31_sextic','sextic34.json',(31,18,6)),('26_octic','octic29.json',(26,13,8))]:
        name=kind+suffix;d=json.loads((ROOT/(name+'.json')).read_text());old=json.loads((ROOT/'upstream/residue'/oldname).read_text())
        sy={k:s.Symbol(k) for k in set(d['variables']+d['fixed_numerals']+old['variables']+old['fixed_numerals'])}
        ps=lambda e:s.sympify(e,locals=sy)
        vr=[sy[x] for x in d['variables']];rr=[s.expand(ps(e)) for e in d['residuals']]
        oldrows=[s.expand(ps(e)) for e in old['residuals']]
        private={sy[x] for x in old['variables'] if x.startswith('FA_pos') or x.startswith('FC_pos')}
        expected=[e for e in oldrows if not (e.free_symbols & private)]
        J=sy['J'] if 'J' in d['variables'] else 3*sy['J3']+1
        q=sy['beta']*J+1;C=q-sy['F']-sy['alpha'];pos=ps('1+cone1**2+cone2**2+cone3*(cone3+1)')
        if kind=='determinant':
            U=sy['cone_A']*sy['F'];V=sy['cone_B']*C;guard=U*V-(q-U-V)**2-pos
        else:
            x=sy['beta']*sy['F'];y=sy['Walpha']*sy['alpha'];z=sy['WC']*C
            guard=2*(x*y+x*z+y*z)-x*x-y*y-z*z-pos
        expected.append(s.expand(guard))
        need(Counter(rr)==Counter(expected),name+' independent source70 row replacement')
        need((len(vr),len(rr),d['exact_degree'])==dimensions,name+' dimensions')
        need(len(set(vr))==len(vr),name+' distinct unknowns')
        need(set.union(*(e.free_symbols for e in rr))==set(vr+[sy[x] for x in d['fixed_numerals']]),name+' all and only declared symbols')
        need(all(s.Poly(e,*vr).total_degree()<=dimensions[2]//2 for e in rr),name+' degree upper bound')
        poly=s.Poly(sum(e*e for e in rr),*vr)
        witness=ps(d['degree_witness']['monomial'])
        need(poly.total_degree()==dimensions[2] and poly.coeff_monomial(witness)==d['degree_witness']['coefficient'],name+' noncancelling exact degree')
        for port,rel in d['coefficient_binding']['ports'].items():
            need(rel==binding['payloads'][port]['path'],name+' actual coefficient path '+port)
        if 'full_parent_restoration' in d:
            parent=json.loads((ROOT/d['parent']).read_text())
            for x in parent['variables']:sy.setdefault(x,s.Symbol(x))
            repl={sy[k]:ps(v) for k,v in d['full_parent_restoration'].items()}
            restored=[s.expand(ps(e).subs(repl,simultaneous=True)) for e in parent['residuals']]
            need(Counter(e for e in restored if e!=0)==Counter(rr),name+' all parent residual restorations')
            need(all(not (e.free_symbols & (set(repl)-{sy.get('tau')})) for e in repl.values()),name+' only retained restoration inputs')
        # This mutation must not pass the literal composition comparison.
        mutated=list(rr);mutated[-1]+=1
        need(Counter(mutated)!=Counter(expected),name+' changed-guard negative control')
        out.append({'name':name,'status':'PASS','variables':len(vr),'rows':len(rr),'degree':dimensions[2],'independent_source70_comparison':True,'exact_parent_restoration':'full_parent_restoration' in d,'sha256':hashlib.sha256((ROOT/(name+'.json')).read_bytes()).hexdigest()})
    # Universal positive-coefficient certificate used by signed rank recovery.
    u,z=s.symbols('u z');U,Z=s.symbols('U Z')
    gap=(2*(U-1)*Z-5)**2-(U-3)*(4*U*Z**2+2)
    pg=s.Poly(s.expand(gap.subs({U:u+64,Z:z+6})),u,z)
    need(all(c>0 for c in pg.coeffs()),'unbounded signed Pell ratio polynomial certificate')
    # Universal factor-two box bound via separate concavity: eight exact vertices.
    vertices=[2*(x*y+x*z+y*z)-x*x-y*y-z*z for x in (1,2) for y in (1,2) for z in (1,2)]
    need(min(vertices)==3,'cone factor-two vertices')
    result={'status':'PASS','packets':out,'universal_signed_ratio_gap':str(pg.as_expr()),'cone_box_vertices':vertices,'coefficient_reconstruction':'run build_coefficients.py separately; check verifies all actual byte bindings and scale recipes','scope':'Exact finite identities, authenticated sources, and elementary polynomial certificates. Unbounded native/Pell/calibration conclusions require the separate mathematical proofs; not kernel checked.'}
    (ROOT/'CHECK.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
