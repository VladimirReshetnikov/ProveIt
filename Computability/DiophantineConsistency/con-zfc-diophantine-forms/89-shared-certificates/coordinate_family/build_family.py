#!/usr/bin/env python3
"""Build and verify the residue/determinant/pair-guard family, offline.

No symbolic-algebra package is required. Fixed coefficient ports are kept
symbolic for exact ring identities, then independently bound to integer bytes.
All acceptance conditions use explicit exceptions (also active under python -O).
"""
from pathlib import Path
import gzip
import hashlib
import importlib.util
import json
from math import isqrt
from polynomial import Poly, parse, require

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'equations'
PORTS = ['beta','K0','MC','MF','cone_A','cone_B']


def verify_source_pins():
    ledger=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for spec in ledger['files']:
        data=(ROOT/spec['local_path']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(blob==spec['git_blob'],'pinned source changed: '+spec['local_path'])
    return len(ledger['files'])


def verify_coefficients():
    binding = json.loads((ROOT/'NEW_BINDING.json').read_text())
    values = {}
    for port in ['beta','K0','MC','MF']:
        raw = gzip.decompress((ROOT/'coefficients'/f'{port}.bin.gz').read_bytes())
        spec = binding['payloads'][port]
        require(len(raw) == spec['raw_bytes'], port+' byte count')
        require(hashlib.sha256(raw).hexdigest() == spec['raw_sha256'], port+' raw digest')
        val = int.from_bytes(raw,'little')
        require(val.bit_length() == spec['bits'], port+' bit count')
        values[port] = val
    for port, exponent in [('cone_A',1113),('cone_B',666104)]:
        val = 1 << exponent
        raw = val.to_bytes((val.bit_length()+7)//8,'little')
        spec = binding['payloads'][port]
        require(hashlib.sha256(raw).hexdigest() == spec['raw_sha256'], port+' recipe digest')
        (ROOT/'coefficients'/f'{port}.bin.gz').write_bytes(gzip.compress(raw,mtime=0))
        values[port] = val
    require(values['beta'] == (1 << 1064921)-1, 'beta literal')
    require(values['beta'] % 3 == 1, 'beta residue')
    require(0 < values['MC'] < values['beta'] < values['MF'] < 2*values['beta'], 'native mask bounds')
    # Replay the authentic finite coefficient constructor after verifying its
    # Git blob. This reads only the packaged literal 943-tile JSON file.
    p = ROOT/'upstream/source34/build_coefficients.py'
    b = p.read_bytes()
    require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest() ==
            'b85e416b8a8b823c01c8ecacd85eebef7f5c69b5','source34 builder identity')
    spec = importlib.util.spec_from_file_location('authentic_source34',p)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    native, audit = mod.construct()
    for port, name in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]:
        require(values[port] == native[name], port+' exact reconstruction')
    return {'raw_bytes':binding['raw_bytes'], 'native_basis_checks':audit['basis_convolution_checks'],
            'all_six_ports_bound':True, 'MF_is_already_shifted':True}


def packet(name, variables, rows, degree, certificate, transformations):
    require(len(set(variables)) == len(variables), name+' duplicate variables')
    allowed = set(variables+PORTS)
    live = set().union(*(p.symbols() for _,p in rows))
    require(live <= allowed, name+' unbound symbols '+str(live-allowed))
    require(set(variables) <= live, name+' dead quantified variables')
    degrees = [p.degree(variables) for _,p in rows]
    require(max(degrees)*2 == degree, name+' maximal residual degree')
    total = sum((p*p for _,p in rows), Poly.integer(0))
    monomial, coefficient = certificate
    require(total.coefficient(monomial,variables) == coefficient, name+' exact degree certificate')
    result = {'name':name, 'domain':'unrestricted integers',
              'variable_count':len(variables), 'variables':variables,
              'fixed_ports':PORTS,'coefficient_binding':'../COEFFICIENT_BINDING.json',
              'residual_count':len(rows),'residual_labels':[i for i,_ in rows],
              'residuals':[p.expression() for _,p in rows],
              'residual_degrees':degrees,'single_polynomial':'sum of squares of all listed residuals',
              'exact_degree':degree,'degree_certificate':{'monomial':monomial,'coefficient':coefficient},
              'symbolic_expansion_terms':len(total.terms),
              'transformations':transformations,
              'status':'ordinary mathematical proof via specified inherited theorems; no new end-to-end formal certificate'}
    (OUT/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    return result


def eliminate(base_rows, base_variables, definitions, defining_rows, tau_shift=False):
    substitutions = {k:parse(v) for k,v in definitions.items()}
    if tau_shift:
        substitutions['tau'] = parse('tau_gap+E*(c-eta)')
    rows=[]
    for i,p in base_rows:
        image=p.substitute(substitutions)
        if i in defining_rows:
            require(image==0,'defining row '+str(i)+' does not vanish')
        else:
            rows.append((i,image))
    variables=[v for v in base_variables if v not in definitions]
    if tau_shift:
        variables=[('tau_gap' if v=='tau' else v) for v in variables]
    return variables,rows


def combine_guards(variables,rows):
    guards=['cone_pos1','cone_pos2','cone_pos3','eta_zeta_pos1','eta_zeta_pos2','eta_zeta_pos3']
    core=[]
    values={}
    for i,p in rows:
        if i in [23,24]:
            prefix='cone_pos' if i==23 else 'eta_zeta_pos'
            pos=parse(f'1+{prefix}1**2+{prefix}2**2+{prefix}3*({prefix}3+1)')
            values[i]=p+pos
        else: core.append((i,p))
    require(len(values)==2,'both old guard quantities must be found')
    g,z=values[23],values[24]
    t=Poly.symbol('pair_root')
    pos=parse('1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)')
    combined=g*z-(t*t-g-z+1)**2-pos
    core.append(('joint_guard',combined))
    variables=[v for v in variables if v not in guards]+['pair_root','pair_pos1','pair_pos2','pair_pos3']
    return variables,core,{'determinant':g.expression(),'eta_zeta':z.expression()}


def diagnostic_pair_lemma():
    # Finite controls supplement, and never replace, the universal proof.
    positive=negative=0
    for x in range(1,151):
        for y in range(1,151):
            n=x+y-1; m=isqrt(n)
            t=m if n-m*m<=m else m+1
            require(x*y-(t*t-x-y+1)**2>0,'nearest-square positive control')
            positive+=1
    for x in range(-30,31):
        for y in range(-30,31):
            for t in range(-10,11):
                g=x*y-(t*t-x-y+1)**2
                require(g<=0 or (x>0 and y>0),'signed false positive')
                negative+=1
    return {'positive_pairs':positive,'signed_triples':negative}


def main():
    OUT.mkdir(exist_ok=True)
    source_count=verify_source_pins()
    coeff=verify_coefficients()
    source=json.loads((ROOT/'quartic38.json').read_text())
    original=[parse(r) for r in source['residuals']]
    q='(beta*(3*J3+1)+1)'; w='(4*(3*w3+1))'; k='(eta+zeta)'
    substitutions={'J':parse('3*J3+1'),'w_scale':parse('3*w3+1')}
    base_rows=[(i,p.substitute(substitutions)) for i,p in enumerate(original) if i!=22]
    variables=[{'J':'J3','w_scale':'w3'}.get(v,v) for v in source['variables'] if v!='u']
    # Literal checks identify the determinant and eta*zeta rows before editing.
    aliases={'q':parse(q),'C':parse(q+'-F-alpha')}
    determinant=parse('cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)**2',aliases)
    require(base_rows[-2][1] == determinant-parse('1+cone_pos1**2+cone_pos2**2+cone_pos3*(cone_pos3+1)'), 'determinant row binding')
    require(base_rows[-1][1] == parse('eta*zeta-1-eta_zeta_pos1**2-eta_zeta_pos2**2-eta_zeta_pos3*(eta_zeta_pos3+1)'), 'eta-zeta guard binding')
    require(original[22]==parse('X-2*u**2'),'removed source square guard')
    products=[]
    products.append(packet('quartic37',variables,base_rows,4,({'tau':4},1),
        {'source':'quartic38.json','affine_substitution':{'J':'3*J3+1','w_scale':'3*w3+1'},
         'deleted_row_zero_based':22,'deleted_variable':'u','proof':'PROOF.md'}))
    definitions={'N':q+'*(L+1)','X':w+'*'+q,'C2':'c**2','F2':'f**2','g':'y**2-V**2','P':k+'+E*(c-eta)'}
    v,r=eliminate(base_rows,variables,definitions,{1,2,6,10,14,17},True)
    products.append(packet('sextic31',v,r,6,({'r':2,'c':4},4),
        {'source':'quartic37','integer_polynomial_restoration':definitions,'tau_old':'tau_gap+E*(c-eta)'}))
    octdefs={'L':q+'**2-1','N':q+'**3','X':w+'*'+q,'C2':'c**2','F2':'f**2','g':'y**2-V**2',
        'Baux':'I**2','D':w+'*'+q+'+a*c+gamma*(4*a+3)','Delta':'a**2+4*a+3','P':k+'+E*(c-eta)'}
    v,r=eliminate(base_rows,variables,octdefs,{0,1,2,6,8,9,10,14,17,19})
    v,r,g=combine_guards(v,r)
    products.append(packet('octic25',v,r,8,({'pair_root':8},1),
        {'source':'quartic37','integer_polynomial_restoration':octdefs,'joint_guard_quantities':g,
         'joint_guard':'g*z-(pair_root**2-g-z+1)**2=Pos(pair_pos1,pair_pos2,pair_pos3)'}))
    # A separately written compact human-readable specification is compared
    # with all 13 expanded rows, so the article does not rely on transcription.
    compact_defs=[('J0','3*J3+1'),('W','4*(3*w3+1)'),('q','beta*J0+1'),
        ('C','q-F-alpha'),('k','eta+zeta'),('X','W*q'),('Delta','a**2+4*a+3'),
        ('D','X+a*c+gamma*(4*a+3)'),('P','k+E*(c-eta)'),
        ('R','(q-F)*(q**3-q)-C*(q**2-1)+(MC+q*MF)*J0'),
        ('G','cone_A*F*cone_B*C-(q-cone_A*F-cone_B*C)**2'),('Z','eta*zeta')]
    aliases={}
    for name,expression in compact_defs:
        aliases[name]=parse(expression,aliases)
    compact_rows=['a-E-(2*v_scale+1)*q**3','E+(E-a)*X','c-eta+(E-a)*k',
        'tau**2-P**2+P*k-1','D**2-Delta*c**2-1','k-1-h*E-R',
        '(K0+W)*C-z*(q-1)-F','V+c-f*o','V-j*c+k-1-h*E',
        'I-(2*r+1)*c**2','I**2-Delta*(f**2-1)',
        'y**2-1-I**2*(y**2-V**2)',
        'G*Z-(pair_root**2-G-Z+1)**2-1-pair_pos1**2-pair_pos2**2-pair_pos3*(pair_pos3+1)']
    require(len(r)==len(compact_rows),'compact row count')
    for (label,p),text in zip(r,compact_rows):
        require(p==parse(text,aliases),'compact row transcription '+str(label))
    (OUT/'compact_octic25.json').write_text(json.dumps({'definitions':dict(compact_defs),
        'residuals':compact_rows,'variables':v,'coefficient_binding':'../COEFFICIENT_BINDING.json',
        'single_polynomial':'sum of squares of the listed residuals'},indent=2)+'\n')
    k2='(1-V+j*c+h*E)'
    octdefs2=dict(octdefs, zeta=k2+'-eta',P=k2+'+E*(c-eta)')
    v,r=eliminate(base_rows,variables,octdefs2,{0,1,2,6,8,9,10,14,16,17,19})
    products.append(packet('octic26_unmerged',v,r,8,({'a':4,'f':4},1),
        {'source':'quartic37','integer_polynomial_restoration':octdefs2}))
    v,r,g=combine_guards(v,r)
    products.append(packet('dodecic24',v,r,12,({'eta':4,'h':4,'E':4},1),
        {'source':'quartic37','integer_polynomial_restoration':octdefs2,'joint_guard_quantities':g,
         'joint_guard':'g*z-(pair_root**2-g-z+1)**2=Pos(pair_pos1,pair_pos2,pair_pos3)'}))
    substitutions={'I':parse('(2*r+1)*c**2')}
    r16=[]
    for i,p in r:
        p=p.substitute(substitutions)
        if i==18:
            require(p==0,'strong multiple definition for degree16 projection')
        else:
            r16.append((i,p))
    products.append(packet('degree16_23',[x for x in v if x!='I'],r16,16,
        ({'r':4,'c':8,'V':4},16),
        {'source':'dodecic24','integer_polynomial_restoration':{'I':'(2*r+1)*c**2'}}))
    binding=json.loads((ROOT/'NEW_BINDING.json').read_text())
    for name,spec in binding['payloads'].items():
        spec['path']='coefficients/'+name+'.bin.gz'
        packed=(ROOT/spec['path']).read_bytes()
        spec['gzip_bytes']=len(packed)
        spec['gzip_sha256']=hashlib.sha256(packed).hexdigest()
    binding['retrieval_commit']='08200eb10fde2db408c69dffd840d6920a569b1f'
    (ROOT/'COEFFICIENT_BINDING.json').write_text(json.dumps(binding,indent=2)+'\n')
    summary={'status':'PASS','pinned_sources_checked':source_count,'compact_article_rows_checked':13,
        'coefficients':coeff,'diagnostics':diagnostic_pair_lemma(),
        'equations':[{k:p[k] for k in ['name','variable_count','residual_count','exact_degree','degree_certificate','symbolic_expansion_terms']} for p in products],
        'scope':'exact finite construction, ring identities, and diagnostics; universal semantic proof is in PROOF.md and inherited sources'}
    (ROOT/'VERIFICATION.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
