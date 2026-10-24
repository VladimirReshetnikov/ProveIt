#!/usr/bin/env python3
"""Independent row/cut certificates, natural restorations and full quartics."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
PIN='59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
BASE='ConZFC_407_888_Quartics/'
sys.path.insert(0,str(ROOT/'tools'))
from review_quartics407888 import raw_export,add_term,multiply
from review_synchronized_certificates import full_sos
from review_shared_pell608 import factorial_controls


def need(ok,text):
    if not ok:raise ValueError(text)


def digest(raw):return sha256(raw).hexdigest()


def load(name):return json.loads((HERE/name).read_text())


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);out=importlib.util.module_from_spec(spec);spec.loader.exec_module(out);return out


def add(a,b,scale=1):
    out=dict(a)
    for m,c in b.items():add_term(out,m,scale*c)
    return out


def constant(n):return{():n}if n else{}


def power(p,n):
    out=constant(1)
    for _ in range(n):out=multiply(out,p)
    return out


def total(items):
    out={}
    for p in items:out=add(out,p)
    return out


def scalar_audit(raw,audit_class):
    a=audit_class(raw);V=raw['variables'];pows={(tuple(p['base']),tuple(p['exponent'])):tuple(p['output'])for p in raw['powers']}
    bins={(tuple(p['n']),tuple(p['k'])):tuple(p['output'])for p in raw['binomials']}
    indices={tuple(r['exponent']):tuple(map(tuple,r['pair']))for r in raw['indices']}
    seeds={tuple(r['exponent']):tuple(map(tuple,r['pair']))for r in raw['seeds']}
    derived={tuple(r['target']):r for r in raw['derivations']}
    W,A,Z=map(tuple,raw['scale']);U,Vaux,Baux=map(tuple,raw['auxiliary'])
    B,q=map(tuple,[raw['radix']['radix_multiple'],raw['radix']['radix']])
    def sym(t):return constant(t[1])if t[0]=='c'else{(t[1],):1}
    stops={t for(n,k),m in pows.items()for t in(n,k,m)}|{t for(n,k),m in bins.items()for t in(n,k,m)}
    stops|={t for r in raw['factorials']for t in map(tuple,[r['input'],r['output']])}
    stops|={t for pair in indices.values()for t in pair}|{W,A,Z,U,Vaux,Baux,B,q}
    leaves={t[1]:sym(t)for t in stops if t[0]=='v'}
    def expand(t,remove=()):return a.expand(t,{i:p for i,p in leaves.items()if('v',i)not in remove})
    rows=0
    def check(label,p):
        nonlocal rows
        need(a.row_poly(label,leaves)==p,'exact actual local row '+label);rows+=1
    def named(s):
        found=[('v',i)for i,v in enumerate(V)if v['name']==s]
        need(len(found)==1,'one named coordinate '+s);return sym(found[0])
    w,aa,z,u,v,b=map(sym,[W,A,Z,U,Vaux,Baux]);D=add(power(aa,2),constant(1),-1)
    norm=lambda center,x,y:add(add(power(x,2),constant(1),-1),multiply(add(power(center,2),constant(1),-1),power(y,2)),-1)
    check('shared.last_norm',add(add(power(aa,2),constant(1),-1),multiply(multiply(power(w,3),add(w,constant(2))),power(z,2)),-1))
    atoms={t for(n,k),m in pows.items()for t in(n,k,m)}
    # Initial frame-sum prefixes can be hash-consed to an already requested
    # addition atom (e.g.2+t=t+2). Expand additions on BOTH sides so the
    # independent cut check uses its actual defining identity in that case.
    frame_leaves={i:p for i,p in leaves.items()if i not in a.gates or a.gates[i]['label']!='addition'}
    frame_expected=add(w,total([constant(2)]+[a.expand(t,frame_leaves)for t in atoms]),-1)
    need(a.row_poly('shared.frame_definition',frame_leaves)==frame_expected,'exact full frame atom sum');rows+=1
    need(a.positive(Z),'positive shared Pell ordinate')
    check('shared_index.norm',norm(aa,u,v))
    check('shared_index.B_mod_U',add(add(b,aa,-1),multiply(u,named('shared_index.Bquotient')),-1))
    expected=add(constant(1),multiply(constant(4),multiply(v,add(named('shared_index.q4minus1'),constant(1)))))
    need(expand(Baux,{Baux})==expected,'actual common B recipe')
    product=constant(1)
    for k,(X,Y)in seeds.items():
        pre=V[X[1]]['name'].removesuffix('.X');x,y=sym(X),sym(Y)
        S,R=named(pre+'.S'),named(pre+'.R')
        check(pre+'.index_at_most_Y',add(add(y,sym(k),-1),named(pre+'.YminusK'),-1))
        check(pre+'.norm1',norm(aa,x,y));check(pre+'.norm3',norm(b,S,R))
        check(pre+'.S_mod_U',add(add(S,x,-1),multiply(u,named(pre+'.Squotient')),-1))
        check(pre+'.R_mod_4Y',add(add(R,sym(k),-1),multiply(constant(4),multiply(y,named(pre+'.Rquotient'))),-1))
        product=multiply(product,power(y,2))
    check('shared_index.V_positive_product',add(v,multiply(product,add(named('shared_index.Vquotient_minus1'),constant(1))),-1))
    need(set(seeds).isdisjoint(derived)and set(seeds)|set(derived)==set(indices)=={k for n,k in pows},'full index partition')
    for target,r in derived.items():
        source=tuple(r['source']);shift=r['shift'];need(r['kind']=='shift'and shift in(1,2)and source[1]<target[1],'acyclic actual index addition')
        need(expand(target,{target})==add(sym(source),constant(shift)),'literal exponent addition')
        X,Y=indices[source];x,y=sym(X),sym(Y)
        smallX,smallY=(aa,constant(1))if shift==1 else(add(multiply(constant(2),D),constant(1)),multiply(constant(2),aa))
        xnext=add(multiply(x,smallX),multiply(D,multiply(y,smallY)))
        ynext=add(multiply(x,smallY),multiply(y,smallX))
        XP,YP=indices[target]
        need(a.expand(XP,{i:p for i,p in leaves.items()if i not in(XP[1],YP[1])},True)==xnext,'derived X pair')
        need(a.expand(YP,{i:p for i,p in leaves.items()if i not in(XP[1],YP[1])},True)==ynext,'derived Y pair')
    base_moduli={}
    for label in a.bylabel:
        if label.startswith('base')and label.endswith('.T_definition'):
            pre=label.removesuffix('.T_definition');T=named(pre+'.T')
            matches=[n for n,k in pows if a.row_poly(label,leaves)==add(add(multiply(constant(2),multiply(aa,sym(n))),T,-1),add(power(sym(n),2),constant(1)),-1)]
            need(len(set(matches))==1,'exact natural base modulus row');base_moduli[matches[0]]=T;rows+=1
    need(set(base_moduli)=={n for n,k in pows},'all requested bases have a nonzero-forcing T row')
    for j,((n,k),m)in enumerate(pows.items()):
        X,Y=map(sym,indices[k]);T=base_moduli[n]
        check('pow'+str(j)+'.power_congruence',add(add(add(X,multiply(sym(n),Y)),multiply(aa,Y),-1),add(sym(m),multiply(T,named('pow'+str(j)+'.quotient'))),-1))
    def find_power(base,exponent):
        hits=[m for(n,k),m in pows.items()if k==exponent and expand(n,{n})==base]
        need(len(hits)==1,'unique requested power with actual base recipe');return sym(hits[0])
    for j,((n,k),C)in enumerate(bins.items()):
        pre='choose'+str(j)+'.';P=find_power(add(sym(q),constant(1)),n);den=sym(pows[q,k])
        check(pre+'digit',add(add(P,multiply(den,add(multiply(sym(q),named(pre+'high')),sym(C))),-1),named(pre+'remainder'),-1))
        check(pre+'remainder_bound',add(den,total([named(pre+'remainder'),named(pre+'rslack'),constant(1)]),-1))
        check(pre+'digit_bound',add(sym(q),total([sym(C),named(pre+'oslack'),constant(1)]),-1))
    for j,(n,k,BB,label)in enumerate(raw['ranges']):
        n,k,BB=map(tuple,[n,k,BB]);need(BB==B,'same range modulus')
        pre='range'+str(j)+'.';P=find_power(add(sym(q),constant(1)),n);den=sym(pows[q,k])
        check(label+'.quotient_multiple',add(P,add(multiply(den,multiply(sym(B),named(pre+'quotient'))),named(pre+'remainder')),-1))
        check(label+'.remainder_bound',add(den,total([named(pre+'remainder'),named(pre+'slack'),constant(1)]),-1))
    new={tuple(d['input']):d for d in raw['new_factorial_data']}
    for j,fact in enumerate(raw['factorials']):
        n,f=tuple(fact['input']),tuple(fact['output']);pre='factorial'+str(j)+'.'
        if n in new:
            r=new[n];rho=tuple(r['radius']);P=sym(tuple(r['numerator']));C=sym(tuple(r['binomial']))
            need(expand(rho,{rho})==multiply(sym(f),power(sym(n),2)),'exact new candidate-output radius')
            wanted_upper=add(multiply(sym(f),power(sym(n),2)),sym(n))
            wanted_base=add(multiply(sym(f),power(sym(n),2)),constant(1))
        else:
            # The H-only sibling leaves this one entire old graph unchanged.
            candidates=[m for(base,k),m in pows.items()if base==k and expand(base,{base})==add(sym(n),constant(2))]
            need(len(candidates)==1,'old t-radius power');rho=candidates[0]
            wanted_upper=add(sym(rho),sym(n));wanted_base=add(sym(rho),constant(1))
            Cands=[m for(upper,k),m in bins.items()if k==n and expand(upper,{upper})==wanted_upper]
            need(len(Cands)==1,'old t-radius binomial');C=sym(Cands[0]);P=find_power(wanted_base,n)
        Cs=[m for(upper,k),m in bins.items()if k==n and expand(upper,{upper})==wanted_upper]
        need(len(Cs)==1 and sym(Cs[0])==C and find_power(wanted_base,n)==P,'actual factorial inner interfaces')
        check(pre+'ceiling',add(add(P,C),total([multiply(C,sym(f)),named(pre+'remainder'),constant(1)]),-1))
        check(pre+'remainder_bound',add(C,total([named(pre+'remainder'),named(pre+'slack'),constant(1)]),-1))
    numerators=[tuple(d['numerator'])for d in raw['new_factorial_data']]
    need(expand(q,{q})==multiply(sym(B),add(total([sym(p)for p in numerators]),constant(1))),'exact new reused radix')
    need([tuple(p)for p in raw['radix']['new_factorial_numerators']]==numerators,'radix numerator ledger')
    encoded=[sym(tuple(n))for n,k,B,label in raw['ranges']]
    check('crt.aggregate_representative_bound',add(multiply(constant(8),sym(B)),add(total(encoded),sym(tuple(raw['radix']['aggregate_slack']))),-1))
    T=sym(tuple(raw['factorials'][0]['output']))
    check('crt.canonical_index',add(add(constant(1),multiply(add(named('crt.encoded_index'),constant(1)),T)),sym(B),-1))
    need(all(a.positive(k)for n,k in pows),'unconditional positive power exponents')
    need(all(a.positive(n)and a.positive(k)for n,k in bins),'unconditional binomial inputs')
    need(all(a.positive(tuple(f['input']))for f in raw['factorials']),'unconditional factorial inputs')
    need(all(t[0]=='c'or t[1]<W[1]for(n,k),m in pows.items()for t in(n,k,m)),
         'all power arguments/results allocated before any private Pell coordinate')
    return dict(exact_local_rows=rows,powers=len(pows),exponent_groups=len(indices),seed_indices=len(seeds),
                derived_indices=len(derived),new_radius_calls=len(new),zero_t_factorial_candidate_not_assumed_away=True,
                private_pell_coordinates_excluded_from_arithmetic_arguments=True)


def new_bound_controls():
    from math import comb,factorial
    local=zero=estimates=0
    for H in range(2,10):
        for t in range(1,H+1):
            for T in range(1,5):
                rhoH=T*H*H;VH=(rhoH+1)**H
                need(max(comb(rhoH+H,j)for j in range(H+1))<=VH,'H low digits before T meaning')
                for J in range(7):
                    rhot=J*t*t;Vt=(rhot+1)**t;q=VH+Vt+1
                    need(max(comb(rhot+t,j)for j in range(t+1))<q,'all t low digits before J meaning')
                    if J==0:
                        need(2**t<VH,'zero candidate branch independently bounded');zero+=1
                    local+=1
    for R in range(4,101):
        for H in [R**4,R**4+1,R**4+11]:
            need(4*R*(R+2)<=H and R*(R+3)<=H,'strong H versus trace bounds')
            for t in [1,R//2,R]:
                for k in [1,R]:
                    need(2*k*(t+2)*(H+1)<H*H+4*H,'new squared-VH strict bound')
                    need(t*(t+3)<=H,'old Vt dominated in H-only sibling');estimates+=1
    for H in range(1,201):need(factorial(H)**2>=H**H,'paired factorial lower bound')
    return dict(pointwise_low_digit_cases=local,zero_second_factorial_candidate_cases=zero,
                exponent_inequality_cases=estimates,factorial_square_lower_bounds=200)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    pins=load('SOURCE_PINS.json');archive=REPO/pins['archive'];need(digest(archive.read_bytes())==PIN==pins['archive_sha256'],'whole reviewed archive')
    need(digest((HERE/'radius_builder.py').read_bytes())==pins['local_override_sha256'],'new override binding')
    need(digest((ROOT/pins['ordinary_parent_review']).read_bytes())==pins['ordinary_parent_review_sha256'],'parent ordinary review')
    for name,h in load('BUILD.json')['sha256'].items():need(digest((HERE/name).read_bytes())==h,'complete generated artifact '+name)
    metrics={};rawchecks={};scalar={};contractions={}
    with zipfile.ZipFile(archive)as z,tempfile.TemporaryDirectory(prefix='projected-radius-independent-')as tmp:
        p=Path(tmp)
        for name in ['code/audit_new.py','code/psd_contract/check.py']:
            f=p/Path(name).name;f.write_bytes(z.read(BASE+name))
        audit=module('pinned_independent_arithmetic',p/'audit_new.py')
        natural=module('pinned_independent_natural',p/'check.py')
        for name,h in pins['read_source_members'].items():need(digest(z.read(BASE+name))==h,'exact inherited member '+name)
        for prefix,children in [('both',['natural399','natural402','natural453']),('H_only',['natural403'])]:
            raw=load(prefix+'_source/raw_builder.json');source=load(prefix+'_source/equation.json');ledger=load(prefix+'_source/gate_ledger.json')
            for field in ['label_majorant','local_majorant']:
                need(raw[field]==json.loads(z.read(BASE+'equations/source690/'+field+'.json')),'unchanged actual '+field)
            rawchecks[prefix]=raw_export(raw,ledger,source);scalar[prefix]=scalar_audit(raw,audit.Audit)
            for name in [prefix+'_source']+children:
                eq=load(name+'/equation.json');metrics[name]=full_sos(eq,load(name+'/expanded_polynomial.json'))
                if name in children:
                    receipt,terms=natural.verify(source,eq,load(name+'/elimination_certificate.json'))
                    need(terms==load(name+'/expanded_polynomial.json')['terms'],'independent natural expansion');contractions[name]=receipt
        controls=[]
        for label,change in [('corrupt radius',lambda b:b['new_factorial_data'][0].update(radius=['c',0])),
                             ('omitted second radix numerator',lambda b:b['radix']['new_factorial_numerators'].pop())]:
            bad=load('both_source/raw_builder.json');change(bad)
            try:scalar_audit(bad,audit.Audit)
            except(ValueError,RuntimeError,KeyError):controls.append(label)
            else:raise ValueError('corruption accepted '+label)
        source=load('both_source/equation.json');target=load('natural399/equation.json');cert=load('natural399/elimination_certificate.json')
        square=next(s['nonnegative_certificate']['squares'][0]for s in cert['steps']if s['nonnegative_certificate']['squares'])
        square['weight'][0]=-abs(square['weight'][0])
        try:natural.verify(source,target,cert)
        except ValueError:controls.append('negative rational restoration weight')
        else:raise ValueError('negative restoration weight accepted')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),metrics=metrics,raw_exports=rawchecks,
        actual_scalar_interfaces=scalar,natural_contractions=contractions,factorial_controls=factorial_controls(),
        new_radix_controls=new_bound_controls(),rejected_corruptions=controls,
        external_independent_tools={name:digest((ROOT/'tools'/name).read_bytes())for name in
            ['review_quartics407888.py','review_synchronized_certificates.py','review_shared_pell608.py']},
        scope='Every local arithmetic interface, raw export, natural restoration and full coefficient list. Ordinary global proof in PROOF.md; no Lean/internal-ZFC theorem.')
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
