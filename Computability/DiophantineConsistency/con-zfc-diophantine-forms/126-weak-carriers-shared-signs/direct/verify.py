#!/usr/bin/env python3
"""Independent exact checker. Imports no producer, optimizer, or theorem prover."""
import sys
sys.dont_write_bytecode=True
import argparse,copy,hashlib,itertools,json
from collections import defaultdict
from pathlib import Path

HERE=Path(__file__).resolve().parent
def need(ok,msg):
    if not ok:raise ValueError(msg)
def load(n):return json.loads((HERE/n).read_text())
def enc(x):return(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def sha(x):return hashlib.sha256(enc(x)).hexdigest()
def collect(terms):
    p=defaultdict(int)
    for c,m in terms:p[tuple(sorted(m))]+=c
    return{m:c for m,c in p.items()if c}
def terms(p):return[[c,list(m)]for m,c in sorted(p.items())if c]
def plus(*ps):
    p=defaultdict(int)
    for a in ps:
        for m,c in a.items():p[m]+=c
    return{m:c for m,c in p.items()if c}
def times(p,q):
    r=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():r[tuple(sorted(m+n))]+=c*d
    return{m:c for m,c in r.items()if c}
def subst(p,v,q):
    r={}
    for m,c in p.items():
        t={():c}
        for w in m:t=times(t,q if w==v else{(w,):1})
        r=plus(r,t)
    return r
def degree(p):return max(map(len,p),default=0)
def neg(p):return{m:-c for m,c in p.items()}
def variable(v):return{(v,):1}
def remap(p,mp):return collect([[c,[mp[v]for v in m]]for m,c in p.items()])
def scalar_guard(v,abc,offset=0):
    a,b,c=abc;p={(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}
    if offset:p[()]=-offset
    return p

def check_fusion():
    old=load('source/parent.json');fc=load('fusion_certificate.json');bc=load('budget_certificate.json');target=load('fused_source.json')
    need(sha(old)==fc['source_sha256'],'source hash')
    need(fc['joint_anchor']and fc['signed_comparison_base'],'selected logical variant')
    names={v['name']:i for i,v in enumerate(old['variables'])}
    pairs=[('fact0.remainder','fact0.slack'),('choose0.remainder','choose0.rslack'),('choose1.remainder','choose1.rslack'),('choose1.output','choose1.oslack')]
    pairs += [(f'range{k}.remainder',f'range{k}.slack')for k in range(10)]
    pair_indices=[(names[a],names[b])for a,b in pairs]
    removed={v for p in pair_indices for v in p}|{names['shared.A'],names['shared.Zminus1'],names['shared_index.q4minus1'],names['shared_index.Vquotient_minus1']}
    need(fc['pair_count']==14,'fourteen product pairs')
    need(set(map(int,fc['old_guard_rows']))==removed,'removed guard inventory')
    private=set();deleted_rows=set()
    for v in sorted(removed):
        rowid=fc['old_guard_rows'][str(v)];row=old['residuals'][rowid]
        abc=[names[f'nonnegative.{v}.{s}']for s in'abc']
        need(row['label']==f'nonnegative.{v}'and collect(row['terms'])==scalar_guard(v,abc),'old scalar row')
        private.update(abc);deleted_rows.add(rowid)
    need(sorted(private)==fc['deleted_private_witnesses'],'private variable inventory')
    need(sorted(deleted_rows)==sorted(fc['deleted_rows']),'deleted row inventory')
    for ri,row in enumerate(old['residuals']):
        if ri not in deleted_rows:need(not any(v in private for c,m in row['terms']for v in m),'private witness escapes')
    e=copy.deepcopy(old);e.pop('metrics',None);e.pop('elimination',None)
    f=names['fact0.output'];fid=next(i for i,r in enumerate(e['residuals'])if r['label']==f'nonnegative.{f}')
    need(e['residuals'][fid]==fc['factorial_guard']['old_row'],'factorial source guard')
    e['residuals'][fid]['terms']=terms(plus(collect(e['residuals'][fid]['terms']),{():-1}))
    for j,(a,b)in enumerate(pair_indices):
        ids=list(range(len(e['variables']),len(e['variables'])+3));u,v,w=ids
        e['variables'] += [{'name':f'product_guard.{j}.{s}','kind':'integer_guard'}for s in'abc']
        r={'label':f'product_guard.{j}','terms':terms({tuple(sorted((a,b))):1,(u,u):-1,(v,v):-1,(w,w):-1,(w,):-1})}
        e['residuals'].append(r)
        need(fc['new_guards_before_reindex'][j]=={'pair':[a,b],'pair_names':list(pairs[j]),'auxiliary':ids,'row':r},'literal product guard')
    A=names['shared.A'];v=names['shared_index.Vquotient_minus1'];u=len(e['variables'])
    e['variables'].append({'name':'joint_anchor.quotient_square','kind':'gate'})
    square={'label':'joint_anchor.square','terms':terms({(u,):1,(v,v):-1,(v,):-2,():-1})};e['residuals'].append(square)
    ids=list(range(len(e['variables']),len(e['variables'])+3));a,b,c=ids
    e['variables'] += [{'name':f'joint_anchor.{s}','kind':'integer_guard'}for s in'abc']
    r={'label':'joint_anchor.guard','terms':terms({tuple(sorted((A,u))):1,(u,):-1,():-1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})}
    e['residuals'].append(r)
    need(fc['new_guards_before_reindex'][14]=={'predicate':'(A-1)(v+1)^2 >= 1','A':A,'v':v,'square_variable':u,'square_row':square,'auxiliary':ids,'row':r},'literal joint anchor')
    retained=[i for i in range(len(e['variables']))if i not in private];mp={v:i for i,v in enumerate(retained)}
    need(retained==fc['retained_before_reindex'],'fusion variable map')
    e['variables']=[e['variables'][i]for i in retained]
    e['residuals']=[dict(r,terms=terms(remap(collect(r['terms']),mp)))for i,r in enumerate(e['residuals'])if i not in deleted_rows]
    e['variant']+=':deferred_sign_fusion'
    need(sha(e)==fc['pre_budget_target_sha256'],'complete pre-budget fused source')
    check_budget(e,bc,removed)
    need(e==target and sha(e)==fc['target_sha256'],'entire fused source after budget')
    # Audit the exact pair-sum rows used by the unbounded sign argument.
    pair_rows=[]
    for a,b in pair_indices:
        hits=[]
        for ri,row in enumerate(old['residuals']):
            p=collect(row['terms'])
            if p.get((a,))==-1 and p.get((b,))==-1 and degree(p)<=1:
                rest={m:c for m,c in p.items()if m not in((a,),(b,))}
                hits.append({'row':ri,'label':row['label'],'sum':terms(rest)})
        need(len(hits)==1,'unique exact pair-sum row')
        pair_rows.append({'pair_names':[old['variables'][a]['name'],old['variables'][b]['name']],**hits[0]})
    return target,{'pairs':14,'removed_scalar_predicates':len(removed),'deleted_private_witnesses':len(private),'raw_variables':len(target['variables']),'raw_rows':len(target['residuals']),'pair_sum_rows':pair_rows}

def check_budget(e,cert,removed):
    domain=load('source/domain.json');initial=set(domain['guard_indices'])-removed
    need(sorted(initial)==cert['initial_nonnegative'],'nonsemantic initial signs')
    names={v['name']:i for i,v in enumerate(e['variables'])}
    for v in initial:
        ids=[names[f'nonnegative.{v}.{s}']for s in'abc']
        row=next(r for r in e['residuals']if r['label']==f'nonnegative.{v}')
        need(collect(row['terms'])==scalar_guard(v,ids,1 if e['variables'][v]['name']=='fact0.output'else 0),'retained seed guard')
    frame=cert['frame_row'];need(e['residuals'][frame]['label']=='shared.frame_definition','frame row identity')
    known=set(initial)
    for step in cert['proof_steps']:
        v=step['variable'];ri=step['row'];p=collect(e['residuals'][ri]['terms']);rhs=collect(step['rhs'])
        need(ri!=frame and v not in known,'acyclic frame-free sign step')
        expected=plus(variable(v),neg(rhs))
        need(p==expected or p==neg(expected),'exact sign-defining row')
        need(all(c>=0 for c in rhs.values()),'nonnegative polynomial coefficients')
        deps={z for m in rhs for z in set(m)if m.count(z)%2}
        need(sorted(deps)==step['dependencies']and deps<=known,'known odd-power signs')
        known.add(v)
    original={():2};new={():2}
    need([a['atom']for a in cert['atoms']]==domain['square_budget']['atoms'],'source atom inventory')
    for item in cert['atoms']:
        p=collect(item['atom']['affine']);need(degree(p)<=1,'affine source port')
        original=plus(original,times(p,p))
        natural=all(c>=0 for c in p.values())and{v for m in p for v in m}<=known
        need(natural==item['nonnegative'],'correct linear/square choice')
        q=p if natural else times(p,p)
        need(terms(q)==item['contribution'],'exact atom contribution');new=plus(new,q)
    W=domain['square_budget']['frame_variable']
    need(e['residuals'][frame]==cert['original_frame'],'original frame literal')
    need(collect(cert['original_frame']['terms'])==plus(variable(W),neg(original)),'old square frame all coefficients')
    e['residuals'][frame]['terms']=terms(plus(variable(W),neg(new)));e['variant']+=':typed_budget'
    need(e['residuals'][frame]==cert['new_frame'],'new typed frame all coefficients')
    need(sum(i['nonnegative']for i in cert['atoms'])==cert['linear_atoms'],'linear atom count')
    need(len(cert['atoms'])-cert['linear_atoms']==cert['squared_atoms'],'square atom count')

def check_projection(source):
    out=load('uncentered_equation.json');cert=load('projection_certificate.json')
    need(sha(source)==cert['input_sha256']and sha(out)==cert['output_sha256'],'projection bindings')
    rows={i:collect(r['terms'])for i,r in enumerate(source['residuals'])};deleted=set()
    for s in cert['steps']:
        ri=s['row_id'];v=s['variable'];q=collect(s['restoration'])
        need(ri in rows and v not in deleted,'projection target is live')
        need(not any(v in m for m in q)and degree(q)<=2,'integral quadratic restoration')
        expected=plus(variable(v),neg(q));need(rows[ri]in(expected,neg(expected)),'monic defining row')
        new={}
        for i,p in rows.items():
            if i==ri:continue
            qq=subst(p,v,q);need(degree(qq)<=2,'residual remains quadratic')
            if qq:new[i]=qq
        rows=new;deleted.add(v)
    retained=sorted({v for p in rows.values()for m in p for v in m});mp={v:i for i,v in enumerate(retained)}
    need(retained==cert['retained_original_variables'],'retained coordinates')
    need(sorted(rows)==cert['retained_original_rows'],'retained rows')
    literal=[{'label':source['residuals'][i]['label'],'terms':terms(remap(p,mp))}for i,p in sorted(rows.items())]
    need(out['residuals']==literal and out['variables']==[source['variables'][i]for i in retained],'all projected rows and variables')
    unused=sorted(set(range(len(source['variables'])))-deleted-set(retained));need(unused==cert['unconstrained_removed'],'free coordinates identified exactly')
    return out,{'monic_restorations':len(deleted),'unconstrained_coordinates':unused}

def check_translation_and_expansion(old):
    cert=load('translation_certificate.json');out=load('equation.json');expanded=load('expanded_polynomial.json')
    need(sha(old)==cert['source_sha256']and sha(out)==cert['target_sha256'],'translation bindings')
    shifts=cert['shifts'];need(len({v for v,s in shifts})==len(shifts)and all(isinstance(s,int)for v,s in shifts),'integral bijective translation')
    target=copy.deepcopy(old);target.pop('metrics',None);target.pop('elimination',None)
    for row in target['residuals']:
        p=collect(row['terms'])
        for v,s in shifts:p=subst(p,v,{(v,):1,():s})
        row['terms']=terms(p)
    target['variant']+=':integral_translation';need(target==out,'all translated coefficients')
    total={}
    for r in out['residuals']:
        p=collect(r['terms']);need(degree(p)<=2,'quadratic final residual');total=plus(total,times(p,p))
    need(terms(total)==expanded['terms'],'complete collected quartic')
    need(expanded['variables']==len(out['variables']),'expansion variable count')
    need({v for m in total for v in m}==set(range(len(out['variables']))),'all final variables occur')
    metrics={'variables':len(out['variables']),'rows':len(out['residuals']),'degree':degree(total),'monomials':len(total),'height':max(map(abs,total.values())),'row_height':max(abs(c)for r in out['residuals']for c,m in r['terms'])}
    need(metrics==load('METRICS.json'),'all metric values')
    need(metrics=={'variables':478,'rows':305,'degree':4,'monomials':5484,'height':511326,'row_height':324},'selected published endpoint')
    return metrics

def arithmetic_controls():
    # Finite diagnostics accompany, and do not replace, the unbounded proofs.
    factorial_pairs=0
    for F in range(1,9):
        for r in range(-25,26):
            for s in range(-25,26):
                if r*s>=0 and F*r+(F-1)*s+F>F:
                    need(r>=0 and s>=0,'factorial sign control');factorial_pairs+=1
    anchors=0
    for A in range(-10,11):
        for v in range(-10,11):
            if (A-1)*(v+1)**2>=1:
                need(A>=2 and v+1!=0,'joint anchor control');anchors+=1
    for a in range(-100,101):need(a*a>=abs(a),'integer square majorant')
    for a,b in itertools.product(range(-20,21),repeat=2):
        if a*b>=0 and a+b>0:need(a>=0 and b>=0,'positive sum/product control')
    # Negative controls explain why strict premises cannot silently disappear.
    need((-1)*(-1)>=0 and (-1)+(-1)<0,'sum premise counterexample')
    need((1-1)*(0+1)**2==0,'strict anchor excludes A=1')
    need((10-1)*(-1+1)**2==0,'strict anchor excludes v=-1')
    return {'factorial_positive_cases':factorial_pairs,'joint_anchor_cases':anchors,'scope':'finite diagnostic controls only'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
    ledger=load('SOURCE_LEDGER.json')
    for f in ledger['files']:
        need(hashlib.sha256((HERE/f['local_path']).read_bytes()).hexdigest()==f['sha256'],'pinned source '+f['local_path'])
    source,fusion=check_fusion();projected,projection=check_projection(source)
    metrics=check_translation_and_expansion(projected);controls=arithmetic_controls()
    result={'status':'PASS','checker_imports':'Python standard library only; no producer or optimizer','optimized_python':not __debug__,'source_files_bound':len(ledger['files']),'fusion':fusion,'projection':projection,'metrics':metrics,'arithmetic_controls':controls,'scope':'Exact finite algebra and data verification; ordinary unbounded proof and inherited calibration remain separate.'}
    if args.output:args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='fusion'},indent=2))

if __name__=='__main__':main()
