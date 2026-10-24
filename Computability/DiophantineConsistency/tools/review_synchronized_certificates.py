#!/usr/bin/env python3
"""Independent inert-source and finite-algebra review of synchronized quartics.

Reads authenticated archives and Git blobs; executes no delivered builder,
Lean, TeX, machine simulator, reference emitter, or network command.
The separately performed full delivery replays may be attached as receipts.
"""
import argparse
import ast
from collections import Counter,defaultdict
from hashlib import sha256
from itertools import product
import json
from math import comb,gcd,prod
from pathlib import Path,PurePosixPath
import stat
import subprocess
import sys
import zipfile

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
ARCHIVE=REPO/'docs/incoming/ConZFC_Synchronized_Certificates_2026-10-24.zip'
ARCHIVE_SHA='ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf'
IMMEDIATE=REPO/'docs/incoming/ConZFC_Shared_Certificates_2026-10-24.zip'
IMMEDIATE_SHA='61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1'
PREFIX='con_zfc_synchronized_certificates/'


def need(ok,text):
    if not ok:raise RuntimeError(text)


def digest(raw):return sha256(raw).hexdigest()


def load_archive(path,wanted):
    raw=path.read_bytes();need(digest(raw)==wanted,'actual complete archive SHA')
    with zipfile.ZipFile(path)as z:
        files={}
        for entry in z.infolist():
            p=PurePosixPath(entry.filename)
            need(not p.is_absolute()and '..'not in p.parts and '\\'not in entry.filename and not stat.S_ISLNK(entry.external_attr>>16),'safe ZIP member')
            if not entry.is_dir():files[entry.filename]=z.read(entry)
    return files


def decode(terms):
    out={}
    for c,m in terms:
        key=tuple(m)
        need(type(c)is int and c and key==tuple(sorted(key))and key not in out,'canonical sparse coefficient')
        out[key]=c
    return out


def encode(poly):return [[c,list(m)]for m,c in sorted(poly.items())if c]


def add_term(poly,mon,c):
    poly[mon]=poly.get(mon,0)+c
    if not poly[mon]:del poly[mon]


def full_sos(eq,pol):
    n=len(eq['variables']);used=set();out={}
    for row in eq['residuals']:
        terms=list(decode(row['terms']).items())
        for m,c in terms:
            need(len(m)<=2 and all(type(i)is int and 0<=i<n for i in m),'valid quadratic row')
            used.update(m)
        for i,(m,c)in enumerate(terms):
            add_term(out,tuple(sorted(m+m)),c*c)
            for k,d in terms[:i]:add_term(out,tuple(sorted(m+k)),2*c*d)
    need(out==decode(pol['terms']),'independent complete squared-residual expansion')
    need(used==set(range(n))and max(map(len,out))==4,'all coordinates live/exact quartic')
    metrics=eq['metrics']
    measured=dict(variables=n,quadratic_rows=len(eq['residuals']),exact_degree=4,
                  expanded_monomials=len(out),max_abs_expanded_coefficient=max(map(abs,out.values())))
    need(all(metrics[k]==v for k,v in measured.items()),'literal metrics')
    return measured


def contraction(source,target,cert):
    canon=lambda x:json.dumps(x,sort_keys=True,separators=(',',':')).encode()
    need(digest(canon(source))==cert['source_equation_sha256']and digest(canon(target))==cert['target_equation_sha256'],'canonical contraction bindings')
    rows={i:decode(r['terms'])for i,r in enumerate(source['residuals'])}
    live=set(range(len(source['variables'])))
    for step in cert['steps']:
        rid,v,sg=step['source_row_id'],step['variable_original_index'],step['pivot_sign']
        need(rid in rows and v in live and sg in [-1,1],'fresh monic pivot')
        need(encode(rows[rid])==step['row_before'],'exact current pivot row')
        rhs=decode(step['restoration'])
        need(all(c>0 and len(m)<=2 and v not in m and set(m)<=live for m,c in rhs.items()),'nonnegative restoring polynomial in remaining coordinates')
        expected={(v,):sg}
        for m,c in rhs.items():add_term(expected,m,-sg*c)
        need(expected==rows[rid],'exact pivot identity')
        del rows[rid]
        for i,row in list(rows.items()):
            result={}
            for mon,c in row.items():
                terms=[((),c)]
                for j in mon:
                    factor=rhs.items()if j==v else[((j,),1)]
                    terms=[(tuple(sorted(ma+mb)),a*b)for ma,a in terms for mb,b in factor]
                for m,c in terms:add_term(result,m,c)
            need(all(len(m)<=2 for m in result),'contraction preserves quadratic residuals')
            rows[i]=result
        live.remove(v)
    kept=cert['retained_original_indices_in_target_order'];unused=cert['unused_original_indices_restored_to_zero']
    need(len(set(kept))==len(kept)and set(kept).isdisjoint(unused)and set(kept)|set(unused)==live,'exact final coordinate partition')
    need({i for r in rows.values()for m in r for i in m}==set(kept),'unused coordinates genuinely absent')
    remap={v:i for i,v in enumerate(kept)}
    remaining=[i for i in sorted(rows)if rows[i]]
    actual=[dict(label=source['residuals'][i]['label'],terms=encode({tuple(remap[v]for v in m):c for m,c in rows[i].items()}))for i in remaining]
    need(actual==target['residuals']and target['variables']==[source['variables'][v]for v in kept],'full contracted equation and coordinate order')
    return dict(eliminations=len(cert['steps']),remaining_variables=len(kept),unused=len(unused),all_restorations_nonnegative=True)


def pell(a,k):
    x,y=1,0
    for _ in range(k):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y


def math_controls():
    frames=congruences=0
    for W in range(2,11):
        for multiple in range(1,4):
            A,ord=pell(W+1,multiple*W)
            need(ord>0 and ord%W==0 and A>W**W,'classified frame gives exponential bound')
            Z=ord//W
            need(A*A-1==W**3*(W+2)*Z*Z,'exact common frame norm')
            for n in range(1,W+1):
                T=2*A*n-n*n-1
                need(T>W,'proposed-output bound')
                for k in range(1,W+1):
                    X,Y=pell(A,k)
                    need(n**k<T,'true-power bound')
                    h=sum(n**(k-1-j)*pell(A,j)[1]for j in range(k))
                    need(h>=0 and X+n*Y==A*Y+n**k+T*h,'one-sided power quotient identity')
                    congruences+=1
            frames+=1
    # The weaker quadratic inequality alone is not the exponential argument.
    need(26>5*5 and 2*26*5-25-1<5**5,'quadratic-bound-alone negative control')
    families=[]
    for A in range(2,6):
        ks=[1,2];xy=[pell(A,k)for k in ks];K=prod(Y*Y for X,Y in xy);L=4*K
        u,v=1,0
        for period in range(1,L*L+1):
            u,v=(A*u+(A*A-1)*v)%L,(u+A*v)%L
            if(u,v)==(1,0):break
        else:raise RuntimeError('unit period control failed')
        U,V=pell(A,period)
        need(U%L==1 and V%L==0 and V>0 and gcd(U,4*V)==1,'simultaneous auxiliary compatibility')
        b=((1-A)*pow(U,-1,4*V))%(4*V)
        B=A+U*(b if b else 4*V)
        need(B>A and (B-1)%(4*V)==0,'positive common CRT base')
        for k,(X,Y)in zip(ks,xy):
            S,R=pell(B,k)
            need(S>=X and R>=k and (S-X)%U==0 and (R-k)%(4*Y)==0,'oriented common index quotients')
        families.append(dict(A=A,indices=ks,period=period))
    digits=0;q=2**sum(range(9))+1
    for n in range(9):
        for k in range(n+3):
            need(((q+1)**n//q**k)%q==(comb(n,k)if k<=n else 0),'common-radix digits including k>n and zero edges')
            digits+=1
    factoring=0
    for p,q,v,g in product(range(-2,3),repeat=4):
        for a,b,c in product(range(-1,2),repeat=3):
            C=p*p+q*q;D=(v-c)**2+g*g
            old=(C+v*v)*(C+(v-a)**2)*(C+(v-b)**2)*(C+D)
            new=C+(v*(v-a)*(v-b))**2*D
            need((old==0)==(new==0),'zero-set axiom factoring')
            factoring+=1
    return dict(classified_frames=frames,oriented_power_equalities=congruences,
                quadratic_bound_negative_control=True,common_auxiliary_families=families,
                common_radix_digit_controls=digits,axiom_factoring_controls=factoring)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--replay-receipt',type=Path);args=ap.parse_args()
    files=load_archive(ARCHIVE,ARCHIVE_SHA);old=load_archive(IMMEDIATE,IMMEDIATE_SHA)
    get=lambda name:files[PREFIX+name]
    obj=lambda name:json.loads(get(name))
    inherited={}
    for name,raw in files.items():
        if name.startswith(PREFIX+'provenance/upstream/'):
            candidates=[k for k,v in old.items()if PurePosixPath(k).name==PurePosixPath(name).name and v==raw]
            need(candidates,'complete unchanged immediate-source copy')
            inherited[name.removeprefix(PREFIX)]=candidates
    pin=obj('provenance/upstream/calibration/CALIBRATION_PINS.json');git=[]
    for item in pin['files']:
        name='provenance/upstream/calibration/'+item['local_file']
        if PREFIX+name not in files:name='provenance/upstream/'+item['local_file']
        raw=get(name);blob=subprocess.check_output(['git','show',pin['commit']+':'+item['repository_path']],cwd=REPO)
        need(blob==raw and digest(raw)==item['sha256'],'exact logical calibration Git blob')
        git.append(item['repository_path'])
    # Direct source changed only its two beta remainder rows before factoring.
    def function(raw):return next(n for n in ast.parse(raw).body if isinstance(n,ast.FunctionDef)and n.name=='source_pair_calculus')
    before=function(get('provenance/upstream/direct_calculus.py'));after=function(get('code/direct_source.py'));found=0
    for n in ast.walk(before):
        if isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='rows'and isinstance(n.value,ast.List)and len(n.value.elts)==4:
            n.value.elts=[n.value.elts[0],n.value.elts[2]];found+=1
    need(found==1 and ast.dump(before)==ast.dump(after),'exact two-row source projection')
    equation=lambda name:obj('equations/'+name+'/equation.json')
    source=equation('source895');metrics={};certificates={}
    for name in ['source895','natural596','natural529','natural522','integer2088']:
        metrics[name]=full_sos(equation(name),obj('equations/'+name+'/expanded_polynomial.json'))
        if name.startswith('natural'):certificates[name]=contraction(source,equation(name),obj('equations/'+name+'/elimination_certificate.json'))
    nat=equation('natural522');integer=equation('integer2088');n=len(nat['variables'])
    need(integer['residuals'][:len(nat['residuals'])]==nat['residuals']and integer['variables'][:n]==nat['variables'],'integer companion exact natural prefix')
    for i in range(n):
        a,b,c=n+3*i,n+3*i+1,n+3*i+2
        need(decode(integer['residuals'][len(nat['residuals'])+i]['terms'])=={():1,(i,):8,(a,a):-1,(b,b):-1,(c,c):-1},'exact integer three-square guard')
    replay=None
    if args.replay_receipt:
        replay=json.loads(args.replay_receipt.read_text())
        need(replay['status']=='PASS'and replay['optimized_python']==bool(sys.flags.optimize)and replay['exact_regenerated_files']==22,'matching independently performed full replay')
        need(all(c['rejected']for c in replay['corruption_controls']),'full replay rejected all mutations')
        for name,wanted in replay['equation_sha256'].items():need(digest(get('equations/'+name))==wanted,'full replay authentic equation bytes')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),archive_sha256=ARCHIVE_SHA,
        unchanged_immediate_source_files=inherited,exact_git_calibration_files=git,calibration_commit=pin['commit'],
        exact_beta_rows_deleted=2,metrics=metrics,contraction_certificates=certificates,
        independent_finite_math_controls=math_controls(),full_delivery_replay=replay,
        scope='Independent source authentication, complete SOS expansions, contraction/guard identities and finite controls. Ordinary unbounded review in PROPOSAL_REVIEW_SYNCHRONIZED_CERTIFICATES.md; no Lean/internal-ZFC proof.')
    target=ROOT/('PROPOSAL_REVIEW_SYNCHRONIZED_CERTIFICATES_OPTIMIZED.json'if sys.flags.optimize else'PROPOSAL_REVIEW_SYNCHRONIZED_CERTIFICATES.json')
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',metrics=metrics,finite_controls=result['independent_finite_math_controls'],full_delivery_replay_attached=replay is not None),indent=2))


if __name__=='__main__':main()
