#!/usr/bin/env python3
"""Independent literal sign/prefix peer plus fresh frozen full replay receipts.

No candidate builder/checker/optimizer is imported. Those programs are
separately replayed; this file verifies signs/restoration/partition afresh.
All finite Pell controls supplement the adjoining unbounded proof review.
"""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
import zipfile

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
FOUNDATION=ROOT/'candidates/projected-radius-mixed'
PROJECTIONS=ROOT/'candidates/projected-radius-mixed-projections'


def need(ok,message):
    if not ok:raise ValueError(message)


def digest(raw):return sha256(raw).hexdigest()
def load(p):return json.loads(p.read_text())
def poly(terms):return{tuple(m):c for c,m in terms if c}


def add(a,b,scale=1):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+scale*c
    return{m:c for m,c in out.items()if c}


def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return{m:c for m,c in out.items()if c}


def sign_steps(rows,known,steps):
    for step in steps:
        v,c=step['variable'],step['coefficient'];rhs=poly(step['rhs'])
        need(type(c)is int and c>0 and v not in known and all(v not in m for m in rhs),'fresh independent sign target')
        row=poly(rows[step['row']]['terms']);expected=add({(v,):c},rhs,-1)
        need(row==expected or row=={m:-a for m,a in expected.items()},'literal full sign row')
        if step['kind']=='affine_square':
            root=poly(step['square_root']);need(all(len(m)<=1 for m in root)and mul(root,root)==rhs,'independent square identity')
            dependencies=set()
        else:
            need(step['kind']=='positive_monomials'and all(c>0 for c in rhs.values()),'nonnegative sign polynomial')
            dependencies={i for m in rhs for i,p in Counter(m).items()if p%2}
        need(dependencies<=known and sorted(dependencies)==step['dependencies'],'earlier sign prerequisites')
        known.add(v)
    return known


def prefix_audit(parent,raw,sign,restoration,interface):
    seeds=set(sign['guards']);need(len(seeds)==109,'exact independent seed set')
    known=sign_steps(parent['residuals'],set(seeds),sign['proof_steps'])
    need(len(known)==533 and sorted(known)==sign['known_after_ordinary_steps'],'exact initial closure')
    late=sign_steps(parent['residuals'],known|set(sign['late_semantic_quotients']),sign['late_proof_steps'])
    need(len(late)==577,'exact late closure')
    retained=restoration['retained_raw_indices'];rename={v:i for i,v in enumerate(retained)}
    need(len(rename)==667 and retained==sorted(rename),'complete ordered injection')
    need([raw['variables'][i]for i in retained]==parent['variables'],'whole coordinate identity map')
    definitions={r['gate']:r for r in raw['rows']if r.get('gate')is not None}
    expected_records={r['raw_variable']:poly(r['terms'])for r in restoration['omitted']}
    need(set(expected_records)==set(range(1259))-set(retained),'every omitted coordinate represented')
    recipes={}
    for v in range(1259):
        if v in rename:recipes[v]={(rename[v],):1};continue
        row=poly(definitions[v]['terms']);need(row.pop((v,),None)==1,'monic omitted gate')
        recipe={}
        for m,c in row.items():
            need(c<0 and len(m)<=1 and all(i<v for i in m),'positive triangular affine definition')
            recipe=add(recipe,{():1}if not m else recipes[m[0]],-c)
        need(recipe==expected_records[v],'entire independently restored recipe')
        recipes[v]=recipe
    naturally_known={v for v,p in recipes.items()if all(c>0 and set(m)<=known for m,c in p.items())}
    need(set(range(643))<=naturally_known,'all semantic prefix natural before powers')
    groups=[interface[k]for k in ['semantic_non_gate_rows','private_non_gate_rows','all_gate_rows']]
    need(sorted(sum(groups,[]))==list(range(1177))and all(len(g)==len(set(g))for g in groups),'whole disjoint row partition')
    need(len(groups[0])==39 and len(groups[1])==109 and len(groups[2])==1029,'exact complete row roles')
    for j in groups[0]:need(all(i<643 for c,m in raw['rows'][j]['terms']for i in m),'no private coordinate in semantic constraint')
    for row in raw['rows']:
        if row.get('gate')is not None:
            v=row['gate']
            need(all(i<v for c,m in row['terms']if m!=[v]for i in m),'no private backward dependency')
    free=set(range(643,1259))-set(definitions)
    need(free==set(interface['private_free_variables'])and len(free)==142,'all private free roles')
    need(len(interface['powers'])==21 and len(interface['seeds'])==15 and len(interface['all_indices'])==16,'all power/index interfaces')
    for p in interface['powers']:
        for key in ['base','exponent','output']:need(p[key][0]=='v'and p[key][1]<643,'power argument/output strictly before private certificates')
    return dict(independent_initial_sign_steps=len(sign['proof_steps']),initial_natural_coordinates=len(known),
                late_natural_coordinates=len(late),omitted_affine_recipes=len(expected_records),
                all643_prefix_coordinates_natural=True,private_free_coordinates=len(free),
                semantic_rows=39,private_constraints=109,defining_rows=1029)


def pell(a,n):
    x,y=1,0
    for _ in range(n):x,y=a*x+(a*a-1)*y,x+a*y
    return x,y


def arithmetic_controls():
    bounds=signed=endpoint=0;signs=set()
    for W in range(2,8):
        A,Y=pell(W+1,W);need(Y%W==0 and A>W**W,'strict bootstrap and positive integral ordinate')
        for n in range(1,W):
            T=2*A*n-n*n-1
            need(T>=2*A-2>A,'strict modulus before power interpretation')
            for k in range(1,W):
                for m in range(W):
                    need(0<=m<T and 0<n**k<T,'candidate/true power strict bounds');bounds+=1
    for A in [2,3,4]:
        for i in [1,2]:
            X,Y=pell(A,i);n=2*i*Y;U,V=pell(A,n)
            need(V%(Y*Y)==0,'literal square-divisible shared auxiliary')
            t=((A-1)*pow(4*V,-1,U))%U
            if t==0:t=U
            B=1+4*V*t;need(B>=2 and(B-A)%U==0 and(B-1)%(4*Y)==0,'all common base hypotheses')
            xb,yb=1,0
            for h in range(4*n):
                for es in [-1,1]:
                    for er in [-1,1]:
                        S,R=es*xb,er*yb;k=R%(4*Y)
                        if(S-X)%U==0 and 1<=k<=Y:
                            need(k==i,'independent all-sign index recovery')
                            newB=B+4*V*U*(A+1);newS,newR=pell(newB,k)
                            need((newS-X)%U==0 and(newR-k)%(4*Y)==0 and newS>=X and newR>=k,'fresh nonnegative comparison lift')
                            need(newB==1+4*V*(t+U*(A+1))and newB==A+U*((B-A)//U+4*V*(A+1)),'both simultaneous base identities')
                            signed+=1;signs.add((es,er))
                xb,yb=B*xb+(B*B-1)*yb,xb+B*yb
    # Separate endpoint i=n,Y=1: all four independent signs are relevant.
    A=3;X,Y=pell(A,1);U,V=X,Y;B=9
    for h in range(4):
        S,R=pell(B,h)
        for es in [-1,1]:
            for er in [-1,1]:
                if(es*S-X)%U==0 and(er*R-1)%4==0:endpoint+=1
    need(len(signs)==4 and endpoint>0,'all signs and equality endpoint covered')
    return dict(strict_bootstrap_range_cases=bounds,all_sign_index_and_fresh_lift_cases=signed,
                all_four_sign_pairs=sorted(map(list,signs)),equal_index_Y_one_cases=endpoint)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--replay-prefix',type=Path,required=True);ap.add_argument('--output',type=Path);args=ap.parse_args()
    seals={}
    for folder in[FOUNDATION,PROJECTIONS]:
        manifest=load(folder/'MANIFEST.json')['files']
        need(set(manifest)=={str(p.relative_to(folder))for p in folder.rglob('*')if p.is_file()and p.name!='MANIFEST.json'},'closed frozen file set')
        for n,h in manifest.items():need(digest((folder/n).read_bytes())==h,'every frozen file '+n)
        seals[folder.name]=dict(files=len(manifest),manifest_sha256=digest((folder/'MANIFEST.json').read_bytes()))
    parent=load(FOUNDATION/'source/natural667.json');raw=load(FOUNDATION/'source/raw_builder.json')
    sign=load(FOUNDATION/'mixed_sign_certificate.json');restoration=load(FOUNDATION/'raw_restoration.json');interface=load(FOUNDATION/'arithmetic_interfaces.json')
    independent=prefix_audit(parent,raw,sign,restoration,interface)
    mutations=[]
    for label,target in [('changed original sign',0),('altered raw restoring recipe',1),('private use in semantic row',2)]:
        p,r,s,t=deepcopy(parent),deepcopy(raw),deepcopy(sign),deepcopy(restoration)
        if target==0:s['proof_steps'][0]['rhs'][0][0]+=1
        elif target==1:t['omitted'][0]['terms'][0][0]+=1
        else:r['rows'][interface['semantic_non_gate_rows'][0]]['terms'].append([1,[643]])
        try:prefix_audit(p,r,s,t,interface)
        except(ValueError,KeyError):mutations.append(label)
        else:raise ValueError('independent mutation accepted '+label)
    pins=load(FOUNDATION/'SOURCE_PINS.json');theorem=pins['signed_theorem_archive'];archive=REPO/theorem['repository_path']
    need(digest(archive.read_bytes())==theorem['sha256'],'whole signed theorem ZIP')
    with zipfile.ZipFile(archive)as z:
        primary=z.read('con_zfc_batched_pell/provenance/PellMatiyasevic.lean')
        need(digest(primary)=='5c5756cdf2fa70fb77af9daa9c7167c65749ac616bde8f5fdfeed2cb958b3ed5','exact primary Pell source')
        theorem_hash=digest(z.read(theorem['member']))
    replays={}
    for family in ['foundation','projections']:
        for operation in ['check','build']:
            for mode in ['normal','optimized']:
                path=Path(str(args.replay_prefix)+'-'+family+'-'+operation+'-'+mode+'.json');data=load(path)
                need(data['status']=='PASS','fresh complete replay status')
                if operation=='build':need(data['check']is True,'optimizer rerun is exact byte check')
                else:need(data['optimized_python']==(mode=='optimized'),'fresh check mode')
                replays[family+'_'+operation+'_'+mode]=dict(path=str(path),sha256=digest(path.read_bytes()),result=data)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),frozen_seals=seals,
                independent_literal_prefix_audit=independent,independent_rejected_mutations=mutations,
                supplementary_arithmetic_controls=arithmetic_controls(),
                signed_theorem_sha256=theorem_hash,primary_pell_source_sha256=digest(primary),
                complete_fresh_replays=replays,
                scope='Full ordinary proof/private-use review, independent original-row signs and raw prefix reconstruction, complete normal/O checker and generator--check replays. No Lean or new source/internalZFC calibration.')
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
