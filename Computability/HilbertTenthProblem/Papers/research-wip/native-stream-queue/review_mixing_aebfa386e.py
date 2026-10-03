#!/usr/bin/env python3
"""Portable pinned review of the finite positive Markov polynomial compiler."""
import argparse
from collections import Counter
from contextlib import contextmanager
from fractions import Fraction as Q
import hashlib
import importlib.util
from itertools import product
import json
from math import factorial
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

ARCHIVE_SHA = '8c3543f514df39f26f5668d5434ddaa50580aab0303ef84dc6c286731c50c1ca'
MEMBERS = {'Mixing_Does_Not_Remove_Arithmetic/README.md': 'eabef737fcc2cbc0b08138a272d3dafecded6aa5412e6927429e93a061c6ac05', 'Mixing_Does_Not_Remove_Arithmetic/SHA256SUMS.txt': '9b1418aafc48486cb3708c63d9a378bce0e8e3505b22489c3229a558a8f4978b', 'Mixing_Does_Not_Remove_Arithmetic/article.pdf': '41b3a7a7839e1ba994ea3c9e27dc94b8e9568b7c03ec631f327e787d5db8e5bc', 'Mixing_Does_Not_Remove_Arithmetic/article.tex': '4f2103d41346afd691f17ca89bb81e06e2a1e60ced0e0a5a84736dfb8a156213', 'Mixing_Does_Not_Remove_Arithmetic/code/build_examples.py': '1d9733990f344fca05a816802d688165ed47d1966317e73ed6b8ca18f027f0bd', 'Mixing_Does_Not_Remove_Arithmetic/code/mixing_compiler.py': 'd569894f1e5c738d0c89afa35d97e01e8ca1eab098d68fd4e5f2b9f3ebc48313', 'Mixing_Does_Not_Remove_Arithmetic/code/verify_exports.py': '2b191180b6356327b6aa2a44d43963196cf5544c00cbad6a562515086bc0165d', 'Mixing_Does_Not_Remove_Arithmetic/examples/difference_square.json': '04af48307c0e4cdb1c6e46b9f1d3313923ce8332c8b1dd89e08057e03901e721', 'Mixing_Does_Not_Remove_Arithmetic/examples/factor_family_0.json': '4295f0ea8dfb32d9196b3347bd69950f4c45f418afe5e612726bb490709ef101', 'Mixing_Does_Not_Remove_Arithmetic/examples/factor_family_1.json': 'e07e913dff293ad108645dade4d4e6438b349c465ca500e26ad301e18455959b', 'Mixing_Does_Not_Remove_Arithmetic/examples/factor_family_11.json': '1a0c70ce26321824bc81675448d11fad48a3055139560b9a39275d777b7fa70d', 'Mixing_Does_Not_Remove_Arithmetic/examples/factor_family_2.json': '02bdafc9085115828f4bd84bb98c6b2607f2aa12a67daf2a75fe8c2c6214b4c0', 'Mixing_Does_Not_Remove_Arithmetic/examples/factor_family_6.json': '4b26928b07b42799645c4bc95982a7242a88acd709f2c674ceb97d95cd9715b8', 'Mixing_Does_Not_Remove_Arithmetic/examples/factor_line_0.json': '9c27c7a5d2399c38be42862b603d7cc36859fe60598e956e9287abc031bb33c4', 'Mixing_Does_Not_Remove_Arithmetic/examples/factor_line_1.json': 'fab133965015a337f9c485f00647d763c094d1e2abd667be7bd1ba8541bbb480', 'Mixing_Does_Not_Remove_Arithmetic/examples/factor_line_11.json': '6c1cd90cc2c2356e0e823800a4c3b5ed7bc89c0f1981971e500cfe47ab7da57c', 'Mixing_Does_Not_Remove_Arithmetic/examples/factor_line_2.json': '99a2a28d4d843b16f184728e8697ceed91dae565ba53c61c7c94a265e24fad57', 'Mixing_Does_Not_Remove_Arithmetic/examples/factor_line_6.json': '8755ca97ffcb67c0777075f6915a729aa5c81b0f5ddb71f8fe528f457b4f2a29', 'Mixing_Does_Not_Remove_Arithmetic/examples/fast_mixing.json': 'edd3da18bcc85a5a1e21188e337f5a14e885eaac1afe566b2ada862b3369a64c', 'Mixing_Does_Not_Remove_Arithmetic/examples/product_graph.json': '8c38f8ea810c6dc189c3ebbd67e9b71b915300284ce0ff84a898d68eb27409b5', 'Mixing_Does_Not_Remove_Arithmetic/examples/radial_quartic.json': '6a460f80164016baabe3b236dd2978767ccfec86a251d99d167b5a7f2db4ce13', 'Mixing_Does_Not_Remove_Arithmetic/provenance.json': '5b97db823bad519f1ef2649bf63e496c2182c6ac8de13088c8a9897732bc3bd1', 'Mixing_Does_Not_Remove_Arithmetic/reproduce.sh': '43b0a8324dbdc9b137075c4513725c90373de53a148f38226eff4d866e51325c', 'Mixing_Does_Not_Remove_Arithmetic/requirements.txt': '25f9f1fb1988b230147a1d3092d34e09c069eb7a6c6d6df46b3973b9f2d36efc', 'Mixing_Does_Not_Remove_Arithmetic/verification/compiler_report.json': '046314c3533d16d40cd91c0c1c306434dc7daa89b08b2f5343837f04b2f36ddf', 'Mixing_Does_Not_Remove_Arithmetic/verification/document_qa.json': '7a4b0c078ce42f1018006bf3ca8603618abc5f6c9beef2444718ccb43a2aaaac', 'Mixing_Does_Not_Remove_Arithmetic/verification/independent_report.json': 'accf1f004ad948ea205caf7a895fe90cd49b2a800e0e80b1cb8f1bcefa9c7005'}
PREFIX = 'Mixing_Does_Not_Remove_Arithmetic/'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def mat(rows): return tuple(tuple(Q(v) for v in row) for row in rows)
def rowmul(row,M): return tuple(sum((a*M[i][j] for i,a in enumerate(row)),Q(0)) for j in range(len(M[0])))
def polyadd(p,q):
    out=dict(p)
    for a,c in q.items(): out[a]=out.get(a,Q(0))+c
    return {a:c for a,c in out.items() if c}
def polymul(p,q):
    out={}
    for a,c in p.items():
        for b,d in q.items():
            ab=tuple(x+y for x,y in zip(a,b));out[ab]=out.get(ab,Q(0))+c*d
    return {a:c for a,c in out.items() if c}
def degree_indices(k,d): return tuple(a for a in product(range(d+1),repeat=k) if sum(a)<=d)
def canonical_poly(p): return [{'exponents':list(a),'coefficient':str(c)} for a,c in sorted(p.items()) if c]

def reverse_polynomial(data):
    """Independent Fraction expansion of the actual matrix binomial series."""
    s,k,d=data['states'],len(data['variables']),data['degree'];q=Q(data['q'])
    zero=(0,)*k;R=[]
    for MM in data['transitions']:
        M=mat(MM)
        R.append(tuple(tuple((M[i][j]-Q(1,s))/q-(int(i==j)-Q(1,s)) for j in range(s)) for i in range(s)))
    initial=tuple(Q(x)-Q(1,s) for x in data['initial']);answer={};rows={zero:initial}
    for alpha in sorted(degree_indices(k,d+1),key=lambda a:(sum(a),a)):
        if any(alpha):
            i=next(i for i,a in enumerate(alpha) if a)
            prev=tuple(a-int(j==i) for j,a in enumerate(alpha))
            rows[alpha]=rowmul(rows[prev],R[i])
        if sum(alpha)==d+1:
            need(all(v==0 for v in rows[alpha]),'Normalized row fails total nilpotence')
            continue
        coeff=rows[alpha][0]
        factor={zero:Q(1)}
        for i,a in enumerate(alpha):
            for j in range(a):
                e=tuple(int(i==h) for h in range(k))
                factor=polymul(factor,{e:Q(1),zero:Q(-j)})
            if a: factor={e:c/factorial(a) for e,c in factor.items()}
        answer=polyadd(answer,{a:coeff*c for a,c in factor.items()})
    expected={tuple(t['exponents']):Q(data['epsilon'])*Q(t['coefficient']) for t in data['polynomial_terms']}
    expected={a:c for a,c in expected.items() if c}
    need(answer==expected,'Actual normalized matrix polynomial differs from declared input')
    return dict(name=data['name'],states=s,rank=data['translation_rank'],degree=d,
                reverse_terms=canonical_poly(answer),degree_plus_one_row_products=sum(sum(a)==d+1 for a in rows))

@contextmanager
def module(root):
    name='mixing_compiler';present=name in sys.modules;old=sys.modules.pop(name,None);oldpath=list(sys.path)
    try:
        path=root/'code/mixing_compiler.py';spec=importlib.util.spec_from_file_location(name,path)
        m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m)
        yield m
    finally:
        sys.path[:]=oldpath;sys.modules.pop(name,None)
        if present: sys.modules[name]=old

def author(root,original):
    for rel in ('code/build_examples.py','code/verify_exports.py'):
        result=subprocess.run([sys.executable,str(root/rel)],cwd=root,capture_output=True,text=True,timeout=600)
        need(result.returncode==0,'Original author entry point failed '+rel+': '+result.stderr[-3000:])
    reports={}
    for name in ('compiler_report','independent_report'):
        actual=json.loads((root/'verification'/f'{name}.json').read_text())
        saved=json.loads(original[PREFIX+'verification/'+name+'.json'])
        if name=='compiler_report':actual.pop('sympy_version');saved.pop('sympy_version')
        need(exact(actual,saved),'Original report differs outside explicit version metadata: '+name)
        reports[name]=actual
    exports={}
    for name,data in original.items():
        if name.startswith(PREFIX+'examples/') and name.endswith('.json'):
            need((root/name[len(PREFIX):]).read_bytes()==data,'Author export changed '+name)
            exports[name[len(PREFIX):]]=hashlib.sha256(data).hexdigest()
    need(len(exports)==14,'Wrong complete export count')
    return dict(reports=reports,exports_byte_identical=exports,normalized_fields=['compiler_report.sympy_version'])

def focused(root):
    import sympy as sp
    counts=Counter();records=[];fixture_records=[]
    for path in sorted((root/'examples').glob('*.json')):
        records.append(reverse_polynomial(json.loads(path.read_text())));counts['full_export_polynomial_identities']+=1
    with module(root) as m:
        x,y=sp.symbols('x y')
        cases=[([sp.Rational(3,7)],(x,),[sp.Rational(3,7),sp.Integer(0)]),
               ([x],(x,),[x,sp.Integer(1)]),([x*x],(x,),[x*x,x+1]),
               ([x*x,y,sp.Integer(0)],(x,y),[x*x+y,sp.Integer(0)]),
               ([x*(x-1)/2-y],(x,y),[x*(x-1)/2-y]),
               ([x*y+sp.Rational(2,3)*x],(x,y),[x*y+sp.Rational(2,3)*x])]
        for family,vs,loads in cases:
            model=m.compile_family(family,vs,Q(2,7));r=model.rank;s=model.states
            # Translation-grid rank is independent of the compiler's derivative basis.
            deg=max(sp.Poly(f,*vs).total_degree() for f in family if f!=0)
            monos=degree_indices(len(vs),int(deg));shifted=[]
            for f in family:
                for shift in monos:
                    pol=sp.Poly(f.subs({v:v+n for v,n in zip(vs,shift)},simultaneous=True),*vs)
                    shifted.append([pol.coeff_monomial(a) for a in monos])
            rank=sp.Matrix(shifted).rank();need(rank==r and s==r+1,'Independent joint-translation rank mismatch');counts['independent_translation_ranks']+=1
            need(all(M.det()==model.q**r for M in model.transitions),'Actual determinant/spectrum mismatch');counts['exact_determinants']+=len(vs)
            immutable=[model.coefficient_matrix,model.pivot_inverse,model.E,model.F,*model.shifts,*model.transitions]
            for M in immutable:
                try:M[0,0]=0
                except TypeError:counts['immutable_matrices']+=1
                else:raise ValueError('Compiled public matrix mutable')
            for P in loads:
                p,eps=model.initial(P);need(min(p)>0 and sum(p)==1,'Fresh loading not positive');counts['fresh_loadings']+=1
                temp=root/'verification'/'review_extra.json';model.export(P,temp,'independent_fixture');data=json.loads(temp.read_text());reverse_polynomial(data);counts['fresh_polynomial_identities']+=1
                for cc in product(range(4),repeat=len(vs)):
                    row=tuple(Q(str(v)) for v in p)
                    for i,n in enumerate(cc):
                        for _ in range(n):row=rowmul(row,mat(model.transitions[i].tolist()))
                    expected=Q(1,s)+Q(str(eps))*Q(str(model.q))**sum(cc)*Q(str(P.subs(dict(zip(vs,cc)))))
                    need(row[0]==expected and sum(row)==1 and min(row)>0,'Independent actual rational distribution mismatch');counts['fresh_distribution_tuples']+=1
                    need(sum(abs(a-Q(1,s)) for a in row)/2<=Q(2,7)**sum(cc),'Fresh total variation bound');counts['fresh_contraction_tuples']+=1
                fixture_records.append(dict(family=list(map(str,family)),load=str(P),rank=r,states=s,q=str(model.q)))
        linear=m.compile_family([x],(x,));square=m.compile_family([x*x],(x,))
        need((linear.states,square.states)==(3,4),'Zero-equivalent rank fixture');counts['zero_set_not_series_rank_boundary']+=1
        for theta in (Q(1,2),Q(2,3),Q(99,100)):
            for H in (0,1,4,12):
                delta=theta**H
                need(m.separation_horizon(theta,delta)==H+1,'Strict separation boundary');counts['strict_separation_boundaries']+=1
        for f in ([x+1.0],[True],[sp.Float(1)],[x+y]):
            try:m.compile_family(f,(x,))
            except (TypeError,ValueError):counts['bad_calls']+=1
            else:raise ValueError('Inexact or undeclared polynomial accepted')
        for bad in (True,False,1.0,Q(1,2),-1):
            try:linear.acceptance(x,(bad,))
            except (TypeError,ValueError):counts['bad_calls']+=1
            else:raise ValueError('Invalid natural count accepted')
        for bad in (True,0.5,0,1,-1):
            try:m.compile_family([x],(x,),bad)
            except (TypeError,ValueError):counts['bad_calls']+=1
            else:raise ValueError('Invalid mixing parameter accepted')
        for expr in (y,x*x):
            try:linear.initial(expr)
            except (TypeError,ValueError):counts['bad_calls']+=1
            else:raise ValueError('Outside module accepted')
        original_rank=linear.rank;fam=[x];vv=[x];saved=m.compile_family(fam,vv);fam[0]=y;vv[0]=y
        need(saved.variables==(x,) and saved.rank==original_rank,'Input containers not snapshotted');counts['input_snapshot']+=1
        # Natural-domain filter: even an arbitrary positive error integer is excluded.
        for t,z,S in product(range(8),range(8),range(5)):
            Qv=(z-t)**2+S;Pv=t-z+(z+1)*S
            need((Qv==0)==(Pv==0)==(z==t and S==0),'Positive-error filter changes complete natural zero tuples');counts['natural_positive_filter_tuples']+=1
    return dict(counts=dict(counts),actual_export_reverse_polynomials=records,fresh_fixtures=fixture_records)

def verify(archive):
    archive=Path(archive);need(hashlib.sha256(archive.read_bytes()).hexdigest()==ARCHIVE_SHA,'Archive pin mismatch')
    with tempfile.TemporaryDirectory(prefix='mixing-polynomial-review-') as tmp:
        base=Path(tmp);original={}
        with zipfile.ZipFile(archive) as z:
            entries=z.infolist();need(len(entries)==len({e.filename for e in entries}),'Duplicate ZIP entry')
            for e in entries:
                p=Path(e.filename);need(not p.is_absolute() and '..' not in p.parts and '\\' not in e.filename and (e.external_attr>>16)&0o170000!=0o120000,'Unsafe ZIP entry')
                if e.is_dir():continue
                data=z.read(e);need(MEMBERS.get(e.filename)==hashlib.sha256(data).hexdigest(),'Member pin mismatch '+e.filename)
                original[e.filename]=data;dest=base/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
        need(set(original)==set(MEMBERS),'Archive inventory mismatch')
        root=base/PREFIX;replay=author(root,original);checks=focused(root)
    return dict(status='PASS_MIXING_REVIEW',archive_sha256=ARCHIVE_SHA,member_sha256=MEMBERS,author_replay=replay,independent=checks,scope='Complete article and all substantive modules read; original two executable verification entry points replayed, all14 JSON exports byte-identical. Exact numerical-series reconstruction and bounded independent domain fixtures. No instantiated universal compiler, arithmetic lower bound, or new universal operation record.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archive',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();out=verify(a.archive)
    if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Saved receipt mismatch')
    if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
