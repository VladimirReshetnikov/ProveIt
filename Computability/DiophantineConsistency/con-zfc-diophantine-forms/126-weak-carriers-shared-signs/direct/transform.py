#!/usr/bin/env python3
"""Dependency-ordered sign fusion for the exact round-14 signed sources."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import copy,json,hashlib,argparse
import terminal_elimination as E
from translate_coordinates import translate

ROOT=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok: raise ValueError(msg)

def hash_obj(obj): return hashlib.sha256(E.canonical_bytes(obj)).hexdigest()

def transform(old,frame=True,signed_comparison=True,joint_anchor=False):
    e=copy.deepcopy(old); e.pop('metrics',None); e.pop('elimination',None)
    names={v['name']:i for i,v in enumerate(e['variables'])}
    pair_names=[('fact0.remainder','fact0.slack'),('choose0.remainder','choose0.rslack'),('choose1.remainder','choose1.rslack'),('choose1.output','choose1.oslack')]
    k=0
    while f'range{k}.remainder' in names:
        pair_names.append((f'range{k}.remainder',f'range{k}.slack'));k+=1
    pairs=[(names[a],names[b])for a,b in pair_names]
    removed_guards={i for pair in pairs for i in pair}
    if frame: removed_guards|={names['shared.A'],names['shared.Zminus1']}
    if signed_comparison:removed_guards.add(names['shared_index.q4minus1'])
    if joint_anchor:
        need(frame and signed_comparison,'joint anchor uses signed frame and comparison')
        removed_guards.add(names['shared_index.Vquotient_minus1'])
    deleted_rows=[];deleted_variables=set();old_guard_rows={}
    for ri,row in enumerate(e['residuals']):
        if row['label'] in {f'nonnegative.{v}' for v in removed_guards}:
            v=int(row['label'].split('.')[1]); p=E.normalize(row['terms'])
            abc=[names[f'nonnegative.{v}.{s}']for s in 'abc']
            a,b,c=abc;expected={(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}
            need(p==expected,'unexpected scalar guard')
            old_guard_rows[v]=ri;deleted_rows.append(ri);deleted_variables.update(abc)
    need(set(old_guard_rows)==removed_guards,'all requested guards present')
    for ri,row in enumerate(e['residuals']):
        if ri not in deleted_rows:
            need(not any(v in deleted_variables for coef,m in row['terms']for v in m),'private guard escapes')
    # F>=1 makes the initial factorial-base power orient the t pair itself.
    f=names['fact0.output'];fi=next(i for i,r in enumerate(e['residuals'])if r['label']==f'nonnegative.{f}')
    old_f=copy.deepcopy(e['residuals'][fi]);p=E.normalize(old_f['terms']);p[()]=p.get((),0)-1;e['residuals'][fi]['terms']=E.as_terms(p)
    new_guards=[]
    for j,(a,b) in enumerate(pairs):
        ids=list(range(len(e['variables']),len(e['variables'])+3));u,v,w=ids
        e['variables'] += [{'name':f'product_guard.{j}.{s}','kind':'integer_guard'}for s in 'abc']
        row={'label':f'product_guard.{j}','terms':E.as_terms({tuple(sorted((a,b))):1,(u,u):-1,(v,v):-1,(w,w):-1,(w,):-1})}
        e['residuals'].append(row);new_guards.append({'pair':[a,b],'pair_names':list(pair_names[j]),'auxiliary':ids,'row':row})
    if joint_anchor:
        A=names['shared.A'];v=names['shared_index.Vquotient_minus1'];u=len(e['variables'])
        e['variables'].append({'name':'joint_anchor.quotient_square','kind':'gate'})
        square={'label':'joint_anchor.square','terms':E.as_terms({(u,):1,(v,v):-1,(v,):-2,():-1})}
        e['residuals'].append(square)
        ids=list(range(len(e['variables']),len(e['variables'])+3));a,b,c=ids
        e['variables'] += [{'name':f'joint_anchor.{s}','kind':'integer_guard'}for s in 'abc']
        row={'label':'joint_anchor.guard','terms':E.as_terms({tuple(sorted((A,u))):1,(u,):-1,():-1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})}
        e['residuals'].append(row);new_guards.append({'predicate':'(A-1)(v+1)^2 >= 1','A':A,'v':v,'square_variable':u,'square_row':square,'auxiliary':ids,'row':row})
    elif frame:
        t=names['base0.T']; ids=list(range(len(e['variables']),len(e['variables'])+3));u,v,w=ids
        e['variables'] += [{'name':f'frame_orientation.{s}','kind':'integer_guard'}for s in 'abc']
        row={'label':'frame_orientation','terms':E.as_terms({(t,):1,(u,u):-1,(v,v):-1,(w,w):-1,(w,):-1})}
        e['residuals'].append(row);new_guards.append({'predicate':'base0.T >= 0','coordinate':t,'auxiliary':ids,'row':row})
    # Reindex only the private, now unused scalar-guard witnesses.
    retained=[i for i in range(len(e['variables']))if i not in deleted_variables];mp={v:i for i,v in enumerate(retained)}
    e['variables']=[e['variables'][i]for i in retained]
    e['residuals']=[dict(r,terms=E.as_terms({tuple(sorted(mp[v]for v in m)):coef for m,coef in E.normalize(r['terms']).items()}))for i,r in enumerate(e['residuals'])if i not in deleted_rows]
    e['variant']+=':deferred_sign_fusion'
    cert={'schema':'deferred_sign_fusion_v1','source_sha256':hash_obj(old),'target_sha256':hash_obj(e),'old_guard_rows':old_guard_rows,'deleted_rows':deleted_rows,'deleted_private_witnesses':sorted(deleted_variables),'retained_before_reindex':retained,'factorial_guard':{'old_row':old_f,'new_row_after_reindex':e['residuals'][sum(i not in deleted_rows for i in range(fi))],'source_coordinate':f},'new_guards_before_reindex':new_guards,'signed_comparison_base':signed_comparison,'frame_orientation':frame,'joint_anchor':joint_anchor,'pair_count':len(pairs),'new_logical_content':'F>=1 orients the factorial power first; factorial pair via V>F; B/output slack via q-1>0; remaining pairs after powers; comparison base may be negative.'}
    return e,cert

def save(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(E.canonical_bytes(obj))

def typed_budget(e,domain,cert):
    """Use a certified nonnegative affine atom linearly, every other atom squared."""
    known=set(domain['guard_indices'])-set(int(v)for v in cert['old_guard_rows'])
    steps=[];progress=True
    frame=next(i for i,r in enumerate(e['residuals'])if r['label']=='shared.frame_definition')
    # All semantic body coordinates precede the removed private witnesses;
    # the transformation does not reindex them.
    while progress:
        progress=False
        for ri,row in enumerate(e['residuals']):
            if ri==frame or row['label'].startswith(('nonnegative.','product_guard.','frame_orientation')):continue
            p=E.normalize(row['terms'])
            for m,c in p.items():
                if len(m)!=1 or m[0]in known:continue
                v=m[0];rhs=E.candidate(p,v,False)
                if rhs is None or any(a<0 for a in rhs.values()):continue
                deps={z for mon in rhs for z in set(mon)if mon.count(z)%2}
                if deps<=known:
                    known.add(v);steps.append({'row':ri,'variable':v,'rhs':E.as_terms(rhs),'dependencies':sorted(deps)});progress=True
    terms={():2};atoms=[]
    for a in domain['square_budget']['atoms']:
        p=E.normalize(a['affine']);need(E.degree(p)<=1,'affine atom')
        natural=all(c>=0 for c in p.values())and {v for m in p for v in m}<=known
        q=p if natural else E.multiply(p,p)
        for m,c in q.items():terms[m]=terms.get(m,0)+c
        atoms.append({'atom':a,'nonnegative':natural,'contribution':E.as_terms(q)})
    W=domain['square_budget']['frame_variable'];terms={m:-c for m,c in terms.items()};terms[(W,)]=terms.get((W,),0)+1
    oldrow=copy.deepcopy(e['residuals'][frame]);e['residuals'][frame]['terms']=E.as_terms(terms)
    e['variant']+=':typed_budget'
    return {'schema':'typed_absolute_budget_v1','original_frame':oldrow,'new_frame':e['residuals'][frame],'frame_row':frame,'initial_nonnegative':sorted(set(domain['guard_indices'])-set(int(v)for v in cert['old_guard_rows'])),'proof_steps':steps,'atoms':atoms,'linear_atoms':sum(a['nonnegative']for a in atoms),'squared_atoms':sum(not a['nonnegative']for a in atoms),'lemma':'For every integer a, a^2 >= abs(a); for proved a>=0, a=abs(a). Thus W=2+sum(contribution)>abs(a) for every atom.'}

