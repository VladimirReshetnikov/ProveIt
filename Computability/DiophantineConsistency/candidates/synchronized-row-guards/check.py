#!/usr/bin/env python3
"""Independent actual-row sign certificates and complete integer quartics.

Reconstructs each inference from the actual prefix coefficient row. Imports
no generator, closure algorithm, arithmetic compiler or delivered module.
The elementary inference follows the frozen shared-crt-row-guards checker.
"""
from collections import Counter,defaultdict
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
import zipfile

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
VARIANTS=['integer1224','integer1231','integer1298','integer1597']
ARCHIVE_SHA='ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf'


def need(ok,text):
    if not ok:raise RuntimeError(text)


def decode(terms):
    out={}
    for c,m in terms:
        key=tuple(m)
        need(type(c)is int and c and key==tuple(sorted(key))and key not in out,'canonical actual row')
        out[key]=c
    return out


def all_admissible_outputs(rows):
    outputs=set();count=0
    for row in rows:
        terms=decode(row['terms'])
        for mon,c in terms.items():
            if len(mon)!=1:continue
            v=mon[0];sg=1 if c>0 else-1
            rest=[(m,d)for m,d in terms.items()if m!=mon]
            if all(v not in m and -sg*d>=0 for m,d in rest):
                outputs.add(v);count+=1
    return outputs,count


def verify_derivation(rows,cert,n):
    seeds=cert['seed_variables']
    need(seeds==sorted(set(seeds))and all(type(v)is int and 0<=v<n for v in seeds),'distinct actual seeds')
    available,rule_count=all_admissible_outputs(rows)
    need(set(seeds)==set(range(n))-available,'all seeds are exactly coordinates without a conclusion rule')
    need(cert['available_elementary_rules']==rule_count and cert['available_rule_outputs']==sorted(available),'exhaustive elementary rule census')
    known=set(seeds);multipliers=Counter();even_terms=0
    for step in cert['derivation']:
        v,rid=step['variable'],step['row']
        need(type(v)is int and 0<=v<n and v not in known,'fresh conclusion coordinate')
        need(type(rid)is int and 0<=rid<len(rows),'actual prefix row reference')
        terms=decode(rows[rid]['terms'])
        need((v,)in terms,'nonzero linear conclusion coefficient')
        c=terms[(v,)];sg=1 if c>0 else-1
        for mon,a in terms.items():
            if mon==(v,):continue
            need(v not in mon and -sg*a>=0,'output-free nonnegative RHS')
            powers=Counter(mon)
            need(all(j in known for j,e in powers.items()if e%2),'already certified odd-power premises')
            if mon and all(e%2==0 for e in powers.values()):even_terms+=1
        known.add(v);multipliers[abs(c)]+=1
    need(known==set(range(n)),'every original coordinate certified over arbitrary integers')
    return dict(seed_count=len(seeds),steps=len(cert['derivation']),certified_coordinates=n,
                positive_multipliers=dict(sorted(multipliers.items())),
                domain_independent_even_monomials=even_terms,available_rules=rule_count,
                minimum_seeds_within_this_explicit_rule_class=len(seeds),global_minimum_claim=False)


def exact_sos(eq,poly):
    count=len(eq['variables']);collected=defaultdict(int);used=set()
    for row in eq['residuals']:
        terms=list(decode(row['terms']).items())
        for m,c in terms:
            need(len(m)<=2 and all(type(v)is int and 0<=v<count for v in m),'literal quadratic coefficient')
            used.update(m)
        for i,(m,c)in enumerate(terms):
            collected[tuple(sorted(m+m))]+=c*c
            for k,d in terms[:i]:collected[tuple(sorted(m+k))]+=2*c*d
    expected={m:c for m,c in collected.items()if c};actual=decode(poly['terms'])
    need(expected==actual,'whole integer polynomial equals exact squared-residual sum')
    need(poly['variables']==count and used==set(range(count)),'complete live variable list')
    need(max(map(len,actual))==4 and actual[(count-1,)*4]==1,'exact quartic fourth-power coefficient')
    m=eq['metrics']
    need(m['variables']==count and m['quadratic_rows']==len(eq['residuals'])and m['expanded_monomials']==len(actual)and m['max_abs_expanded_coefficient']==max(map(abs,actual.values())),'actual metrics')
    return dict(variables=count,residuals=len(eq['residuals']),degree=4,terms=len(actual),height=max(map(abs,actual.values())))


def check_variant(name,archive):
    p=HERE/name;load=lambda f:json.loads((p/f).read_text())
    pins=load('PARENT_PINS.json');raw=archive.read(pins['parent_member'])
    need(pins['archive_sha256']==ARCHIVE_SHA and sha256(raw).hexdigest()==pins['parent_sha256'],'actual archive parent binding')
    need(raw==(p/'natural_parent.json').read_bytes(),'complete unchanged natural parent copy')
    parent=json.loads(raw);eq=load('equation.json');poly=load('expanded_polynomial.json');cert=load('NONNEGATIVITY.json')
    n=len(parent['variables']);prefix=parent['residuals']
    need(eq['domain']==poly['domain']=='unrestricted integers','integer domain')
    need(eq['variables'][:n]==parent['variables']and eq['residuals'][:len(prefix)]==prefix,'complete natural row prefix unchanged')
    need(cert['parent_variables']==n and cert['parent_equation_sha256']==sha256(raw).hexdigest(),'sign certificate parent')
    signs=verify_derivation(prefix,cert,n)
    bindings=eq['seed_guards'];guards=eq['residuals'][len(prefix):]
    need([b['input']for b in bindings]==cert['seed_variables']and len(guards)==len(bindings),'exact guard coverage')
    fresh=set()
    for i,(binding,row)in enumerate(zip(bindings,guards)):
        a,b,c=binding['auxiliaries'];v=binding['input']
        need([a,b,c]==list(range(n+3*i,n+3*i+3))and not fresh&{a,b,c},'ordered fresh guard coordinates')
        fresh.update([a,b,c])
        need(decode(row['terms'])=={(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1},'exact universal Legendre guard')
    need(fresh==set(range(n,len(eq['variables'])))and len(eq['variables'])==n+3*len(bindings),'every added coordinate accounted for')
    need(len({v['name']for v in eq['variables']})==len(eq['variables']),'unique names')
    measurements=exact_sos(eq,poly)
    return dict(metrics=measurements,row_certificate=signs,
                equation_sha256=sha256((p/'equation.json').read_bytes()).hexdigest(),
                expanded_sha256=sha256((p/'expanded_polynomial.json').read_bytes()).hexdigest())


def corruption_controls(parent,cert):
    cases=[];n=len(parent['variables']);rows=parent['residuals']
    def rejected(label,bad_rows,bad_cert):
        try:verify_derivation(bad_rows,bad_cert,n)
        except RuntimeError as exc:cases.append(dict(control=label,rejected=True,reason=str(exc)))
        else:raise RuntimeError('accepted corrupted '+label)
    bad=deepcopy(cert);bad['derivation'][0]['variable']=bad['seed_variables'][0]
    rejected('already_known_conclusion',rows,bad)
    bad=deepcopy(cert);bad['derivation'][0]['row']=len(rows)
    rejected('out_of_range_row',rows,bad)
    bad=deepcopy(cert);bad['seed_variables']=bad['seed_variables'][1:]
    rejected('missing_forced_seed',rows,bad)
    bad_rows=deepcopy(rows);step=cert['derivation'][0];v=step['variable'];rid=step['row']
    terms=bad_rows[rid]['terms'];coef=next(c for c,m in terms if m==[v]);sg=1 if coef>0 else-1
    term=next(t for t in terms if t[1]!=[v]);term[0]=sg*abs(term[0])
    rejected('negative_rhs_coefficient',bad_rows,cert)
    return cases


def main():
    pins=json.loads((HERE/VARIANTS[0]/'PARENT_PINS.json').read_text());path=REPO/pins['archive']
    need(sha256(path.read_bytes()).hexdigest()==ARCHIVE_SHA,'whole synchronized archive')
    with zipfile.ZipFile(path)as archive:results={name:check_variant(name,archive)for name in VARIANTS}
    parent=json.loads((HERE/VARIANTS[0]/'natural_parent.json').read_text())
    cert=json.loads((HERE/VARIANTS[0]/'NONNEGATIVITY.json').read_text())
    represented={a*a+b*b+c*(c+1)for a in range(33)for b in range(33)for c in range(33)}
    need(set(range(1001))<=represented,'bounded controls of universal guard transcription')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),variants=results,
        corruption_controls=corruption_controls(parent,cert),bounded_guard_controls=1001,
        scope='Actual arbitrary-integer row certificates, exact source prefixes/fresh guards and every complete quartic. No variable-kind sign premise, arithmetic macro semantics or Lean/internal-ZFC proof is used for the sign derivation.')
    (HERE/('CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',metrics={v:r['metrics']for v,r in results.items()},corruptions_rejected=len(result['corruption_controls'])),indent=2))


if __name__=='__main__':main()
