#!/usr/bin/env python3
"""Independent inert-source and exact-algebra review; no delivered imports."""
import argparse
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
from math import comb,factorial,gcd,prod
from pathlib import Path,PurePosixPath
import subprocess
import sys
import zipfile

from review_synchronized_certificates import load_archive,full_sos,decode,add_term

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
ARCHIVE=REPO/'docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip'
SHA='59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
PREFIX='ConZFC_407_888_Quartics/'


def need(ok,text):
    if not ok:raise RuntimeError(text)


def digest(raw):return sha256(raw).hexdigest()


def multiply(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():add_term(out,tuple(sorted(m+n)),c*d)
    return out


def raw_export(raw,ledger,target):
    """Every ordinary gate is monotone; every signed gate is an exact square."""
    variables=raw['variables'];rows=raw['rows'];count=len(variables)
    identity=lambda x:json.dumps(x,sort_keys=True,separators=(',',':'))
    names={identity(v):i for i,v in enumerate(variables)}
    need(len(names)==count,'unique raw variable metadata')
    retained=[names[identity(v)]for v in target['variables']]
    need(retained==sorted(set(retained)),'retained raw subset')
    need(ledger['all_variables']==variables and ledger['all_rows']==rows,'whole raw gate ledger binding')
    def atom(a):return {():a[1]}if a[0]=='c'else{(a[1],):1}
    squares={}
    for item in ledger['square_difference_gates']:
        difference=atom(item['left'])
        for m,c in atom(item['right']).items():add_term(difference,m,-c)
        v=item['output'][1]
        need(v not in squares,'unique difference-square output')
        squares[v]=multiply(difference,difference)
    definitions={};seen_squares=set()
    for r in rows:
        if r.get('gate')is None:continue
        v=r['gate'];p=decode(r['terms'])
        need(v not in definitions and p.get((v,))==1,'monic gate')
        need(all(v not in m or m==(v,)for m in p),'gate independent of own output')
        recipe={m:-c for m,c in p.items()if m!=(v,)}
        need(all(j<v for m in recipe for j in m),'triangular gate')
        if v in squares:
            need(recipe==squares[v],'exact difference-square gate');seen_squares.add(v)
        else:need(all(c>0 for c in recipe.values()),'positive ordinary gate recipe')
        definitions[v]=recipe
    need(seen_squares==set(squares),'all square recipes have an actual defining row')
    kept=set(retained);rename={v:i for i,v in enumerate(retained)}
    restored=set()
    @lru_cache(None)
    def resolve(v):
        if v in kept:return{(v,):1}
        need(v in definitions,'omitted semantic input')
        recipe=definitions[v]
        need(all(len(m)<=1 and c>0 for m,c in recipe.items()),'omitted gate not nonnegative affine')
        out={}
        for m,c in recipe.items():
            if not m:add_term(out,(),c)
            else:
                for n,d in resolve(m[0]).items():add_term(out,n,c*d)
        need(len(out)<=4 and all(len(m)<=1 and c>0 for m,c in out.items()),'affine support bound')
        restored.add(v);return out
    images=[]
    for r in rows:
        if r.get('gate')is not None and r['gate']not in kept:continue
        image={}
        for m,c in decode(r['terms']).items():
            term={():c}
            for j in m:term=multiply(term,resolve(j))
            for n,d in term.items():add_term(image,n,d)
        need(all(len(m)<=2 for m in image),'export quadratic')
        if image:images.append(dict(label=r['label'],terms=[[c,[rename[v]for v in m]]for m,c in sorted(image.items())]))
    need(images==target['residuals'],'complete raw-to-source affine export')
    omitted_free=set(range(count))-kept-set(definitions)
    need(not omitted_free,'raw free inputs all retained')
    return dict(raw_variables=count,raw_rows=len(rows),raw_gate_definitions=len(definitions),
                exact_signed_difference_square_gates=len(squares),omitted_affine_gates=len(restored),
                retained_variables=len(retained),retained_rows=len(images),omitted_free_inputs=0)


def controls():
    digits=ceilings=exponents=crt=0
    # These cases intentionally include high coefficients >=q: only the low
    # coefficients need bounds, unlike the old all-digits radix theorem.
    high_overflow=0
    for n in range(21):
        for k in range(1,24):
            low=max(comb(n,j)if j<=n else 0 for j in range(k+1))
            for B in range(1,6):
                q=B*(low+1);quot=((q+1)**n)//q**k;C=comb(n,k)if k<=n else 0
                need(quot%q==C and(quot%B==0)==(C%B==0),'low-digit and fused divisibility')
                if any(comb(n,j)>=q for j in range(k+1,n+1)):high_overflow+=1
                digits+=1
    values=[]
    for n in range(26):
        rho=(n+2)**(n+2);V=(rho+1)**n;C=comb(rho+n,n)
        need(all(comb(rho+n,j)<=C<=V for j in range(n+1)),'factorial low-digit bound')
        need((V+C-1)//C==factorial(n),'actual old-radius factorial ceiling')
        values.append(V);ceilings+=1
    need(values==sorted(values),'factorial numerator monotonicity')
    for R in range(4,41):
        for H in [R**4,R**4+1,R**4+7]:
            for t in [1,R//2,R]:
                for k in [1,R]:
                    e=t*(H+1)
                    need(H+e+2<=(t+2)*(H+1),'raw product exponent bound')
                    need(k*(t+2)*(H+1)<=H*(H+1),'upper-digit exponent bound')
                    need(H*(H+1)<H*(H+2),'strict reused numerator bound')
                    exponents+=1
    for H in range(2,10):
        T=factorial(H)
        for t in range(1,H+1):
            ds=[1+(i+1)*T for i in range(t)];B=prod(ds)
            need(all(gcd(a,b)==1 for a,b in combinations(ds,2)),'CRT moduli coprime')
            C=(B-1)//T-1
            need(C>=0 and 1+(C+1)*T==B and all(C%d==i for i,d in enumerate(ds)),'canonical index')
            encoded=[]
            for column in range(8):
                ws=[(i+column)%H for i in range(t)]
                a=sum(w*(B//d)*pow(B//d,-1,d)for w,d in zip(ws,ds))%B
                a=a if a else B;encoded.append(a)
                need(1<=a<=B and all(a%d==w for w,d in zip(ws,ds)),'positive CRT representative')
                need(comb(a,H)%B==0,'cancelled range factorial')
            need(sum(encoded)<=8*B,'aggregate representative inequality');crt+=1
    return dict(low_digit_and_fused_cases=digits,cases_with_large_unused_high_coefficients=high_overflow,
                factorial_low_digit_and_ceiling_cases=ceilings,reused_radix_exponent_cases=exponents,
                canonical_index_and_eight_column_CRT_families=crt)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--replay-receipt',type=Path);args=ap.parse_args()
    files=load_archive(ARCHIVE,SHA);get=lambda name:files[PREFIX+name];obj=lambda name:json.loads(get(name))
    manifest=0
    for line in get('SHA256SUMS').decode().splitlines():
        h,name=line.split('  ',1);need(digest(get(name))==h,'manifest actual bytes');manifest+=1
    parent=load_archive(REPO/'docs/incoming/ConZFC_Synchronized_Certificates_2026-10-24.zip',
                        'ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf')
    inherited={}
    for name,h in obj('provenance/UPSTREAM_SHA256.json').items():
        raw=get('upstream/'+name);need(digest(raw)==h,'retained upstream digest')
        matches=[p for p,v in parent.items()if v==raw]
        need(matches,'unchanged immediate parent member');inherited[name]=matches
    pins=obj('upstream/provenance/upstream/calibration/CALIBRATION_PINS.json');git=[]
    for item in pins['files']:
        name='upstream/provenance/upstream/calibration/'+item['local_file']
        if PREFIX+name not in files:name='upstream/provenance/upstream/'+item['local_file']
        raw=get(name);source=subprocess.check_output(['git','show',pins['commit']+':'+item['repository_path']],cwd=REPO)
        need(raw==source and digest(raw)==item['sha256'],'actual logical calibration blob');git.append(item['repository_path'])
    metrics={name:full_sos(obj('equations/'+name+'/equation.json'),obj('equations/'+name+'/expanded_polynomial.json'))for name in
             ['source690','natural407','natural410','integer888','integer917']}
    raw=obj('provenance/projected_raw_audit_input.json')
    need(len(raw['powers'])==23 and len(raw['indices'])==18 and len(raw['seeds'])==15 and len(raw['derivations'])==3,'actual sharing census')
    rawcheck=raw_export(raw,obj('equations/source690/gate_ledger.json'),obj('equations/source690/equation.json'))
    replay=None
    if args.replay_receipt:
        replay=json.loads(args.replay_receipt.read_text())
        need(replay['status']=='PASS'and replay['python_optimized']==bool(sys.flags.optimize)and replay['complete_regeneration']=='PASS','fresh full replay')
        need(replay['upstream_files_authenticated']==51,'full retained-source checks')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),archive_sha256=SHA,
        manifest_files=manifest,unchanged_immediate_parent_members=inherited,actual_git_calibration_files=git,
        metrics=metrics,raw_affine_and_square_gate_check=rawcheck,independent_arithmetic_controls=controls(),
        full_delivery_replay=replay,scope='Complete source authentication, raw affine/square export and full SOS checks. Unbounded review in PROPOSAL_REVIEW_QUARTICS407888.md. No Lean/internal-ZFC proof.')
    target=ROOT/('PROPOSAL_REVIEW_QUARTICS407888_OPTIMIZED.json'if sys.flags.optimize else'PROPOSAL_REVIEW_QUARTICS407888.json')
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',metrics=metrics,raw_export=rawcheck,arithmetic_controls=result['independent_arithmetic_controls'],full_replay_attached=replay is not None),indent=2))


if __name__=='__main__':main()
