#!/usr/bin/env python3
"""Independent finite verifier. Imports no producer or algebra helper.

This checks exact sparse integer coefficients, the complete local source
edit, all monic restorations, all coordinate translations, and the final
sum of squares. Unbounded arithmetic is proved in ../proof.md.
"""
from pathlib import Path
from collections import defaultdict
import argparse,copy,hashlib,json,subprocess,sys,tempfile

ROOT=Path(__file__).resolve().parents[1]
def require(ok,msg):
    if not ok:raise ValueError(msg)
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(x):return hashlib.sha256(canonical(x)).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def poly(ts):
    d=defaultdict(int)
    for c,m in ts:
        require(type(c) is int and all(type(v) is int and v>=0 for v in m),'integer terms')
        d[tuple(sorted(m))]+=c
    return {m:c for m,c in d.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def sum_p(*ps):
    q=defaultdict(int)
    for p in ps:
        for m,c in p.items():q[m]+=c
    return {m:c for m,c in q.items() if c}
def scale(p,k):return {m:k*c for m,c in p.items() if k*c}
def times(p,q):
    d=defaultdict(int)
    for m,c in p.items():
        for n,e in q.items():d[tuple(sorted(m+n))]+=c*e
    return {m:c for m,c in d.items() if c}
def substitute(p,v,q):
    result={}
    for mon,c in p.items():
        a={():c}
        for w in mon:a=times(a,q if w==v else {(w,):1})
        result=sum_p(result,a)
    return result
def rowset(eq):
    require(eq['domain']=='unrestricted integers','domain')
    rs=[];n=len(eq['variables'])
    for row in eq['residuals']:
        p=poly(row['terms']);require(terms(p)==row['terms'],'canonical row terms')
        require(all(len(m)<=2 and all(v<n for v in m) for m in p),'quadratic row/range')
        rs.append(p)
    return rs

def check_source(old,interfaces,source,certificate):
    ps=rowset(old);rowset(source)
    names={v['name']:i for i,v in enumerate(old['variables'])}
    W,A=names['shared.W'],names['shared.A'];anchor=interfaces['seed_data'][-1]
    X,Y=anchor['pair'];h=poly(anchor['exponent']);cv=interfaces['cap_variables']
    require(old['variables'][X]['name']=='index15.X' and old['variables'][Y]['name']=='index15.Y','anchor binding')
    require(anchor['calls']==[17] and h=={():1,(names['add.380'],):1},'actual label index')
    require(len(interfaces['seed_data'])==15,'all seed pairs')
    U0,C0=cv['U'],cv['Y'];H,B,eta=cv['H'],cv['B'],cv['e'];H2=len(old['variables'])
    a_guard=next(i for i,g in enumerate(interfaces['guards']) if g.get('coordinate')==A)
    e_guard=next(i for i,g in enumerate(interfaces['guards']) if g['kind']=='anchor_common_multiplier')
    cap_guard=next(i for i,g in enumerate(interfaces['guards']) if g['kind']=='shared_square_cap')
    removed={'cap.main_Ay','cap.main_norm','cap.comparison_constructor','cap.comparison_modulus',f'domain_guard.{a_guard}',f'domain_guard.{e_guard}'}
    expected=[];changes=[];seen=set()
    for r,p in zip(old['residuals'],ps):
        seen.add(r['label'])
        if r['label'] in removed:
            changes.append({'old':r,'new':None});continue
        q=substitute(substitute(p,U0,{(X,):1}),C0,{(Y,):1})
        if r['label']=='shared.frame_definition':q=sum_p(scale(q,2),{(W,):-1})
        if r['label']=='cap.index_residue':q=sum_p(q,{(W,):1},scale(h,-1))
        if r['label']=='cap.common_multiple':q=substitute(q,eta,{(eta,):2})
        if r['label']==f'domain_guard.{cap_guard}':q=sum_p(q,{(Y,):-1,(Y,Y):2,(W,):1,(W,W):-1})
        new=dict(r,terms=terms(q));expected.append(new)
        if p!=q:changes.append({'old':r,'new':new})
    require(removed<=seen,'all intended deletions located')
    added=[{'label':'new_center.H2','terms':terms({(H2,):1,(H,H):-1})},
           {'label':'new_center.definition','terms':terms({(B,):1,(A,):-1,tuple(sorted((A,H2))):1,(H2,):-1})}]
    require(source['residuals']==expected+added,'complete source transformation')
    require(source['variables']==old['variables']+[{'name':'new_center.H2','kind':'gate'}],'source coordinate boundary')
    require(certificate['changes']==changes and certificate['appended_rows']==added,'edit certificate')
    require(certificate['parent_sha256']==digest(old) and certificate['source_sha256']==digest(source),'source hashes')
    # The frame really is the doubled sum over every actual affine atom.
    W_rhs={():4}
    for atom in interfaces['square_budget']['atoms']:
        t=poly(atom['affine']);W_rhs=sum_p(W_rhs,scale(times(t,t),2))
    wr=next(poly(r['terms']) for r in source['residuals'] if r['label']=='shared.frame_definition')
    require(wr==sum_p({(W,):1},scale(W_rhs,-1)),'complete doubled frame atoms')
    pool=next(poly(r['terms']) for r in source['residuals'] if r['label']=='cap.pooled_index_residue')
    expected_pool={}
    for sd in interfaces['seed_data']:
        delta=sum_p({(sd['pair'][1],):1},scale(poly(sd['exponent']),-1))
        expected_pool=sum_p(expected_pool,times(delta,delta))
    q0=interfaces['pooled_quotient'];expected_pool=sum_p(expected_pool,{tuple(sorted((A,q0))):-1,(q0,):1})
    require(pool==expected_pool,'all fifteen actual pooled terms')
    return {'modified_or_deleted_rows':len(changes),'appended_rows':len(added),'seeds':15}

def check_projection(source,projected,c):
    require(digest(source)==c['input_sha256'] and digest(projected)==c['output_sha256'],'projection hashes')
    rows={i:p for i,p in enumerate(rowset(source))};live=set(range(len(source['variables'])))
    for index,s in enumerate(c['steps']):
        r,v=s['row_id'],s['variable'];q=poly(s['restoration'])
        require(r in rows and v in live,f'live restoration {index}')
        p=rows[r];k=p.get((v,),0)
        require(k in (-1,1) and all(v not in m for m in p if m!=(v,)),'monic row')
        need=scale({m:a for m,a in p.items() if m!=(v,)},-k)
        require(q==need and all(v not in m for m in q),'exact integer restoration')
        del rows[r]
        for rr in list(rows):
            if any(v in m for m in rows[rr]):
                pp=substitute(rows[rr],v,q)
                require(all(len(m)<=2 for m in pp),'preserved degree')
                if pp:rows[rr]=pp
                else:del rows[rr]
        live.remove(v)
    used=sorted({v for p in rows.values() for m in p for v in m})
    require(sorted(live-set(used))==c['unconstrained_removed'],'absent free coordinates')
    require(used==c['retained_original_variables'] and sorted(rows)==c['retained_original_rows'],'retained maps')
    inverse={v:i for i,v in enumerate(used)}
    expected=[{'label':source['residuals'][r]['label'],'terms':[[a,[inverse[v] for v in m]] for m,a in sorted(rows[r].items())]} for r in sorted(rows)]
    require(projected['residuals']==expected and projected['variables']==[source['variables'][v] for v in used],'complete projected equation')
    rowset(projected)
    return {'monic_restorations':len(c['steps']),'unconstrained_coordinates':len(c['unconstrained_removed'])}

def check_translation(projected,eq,c):
    require(digest(projected)==c['input_sha256'] and digest(eq)==c['output_sha256'],'translation hashes')
    require(eq['variables']==projected['variables'],'translated variable order')
    require(len(eq['residuals'])==len(projected['residuals']),'translated row count')
    shifts=dict(c['shifts']);require(len(shifts)==len(c['shifts']),'unique shifts')
    for before,after in zip(projected['residuals'],eq['residuals']):
        p=poly(before['terms'])
        for v,d in shifts.items():p=substitute(p,v,{(v,):1,():d})
        require(after['label']==before['label'] and after['terms']==terms(p),'exact integral translation')
    return {'translated_coordinates':len(shifts)}

def expand_and_measure(eq,expanded=None):
    ps=rowset(eq);full=sum_p(*(times(p,p) for p in ps))
    if expanded is not None:
        require(expanded['domain']=='unrestricted integers','expanded domain')
        require(expanded['terms']==terms(full),'every collected coefficient')
    return {'domain':'unrestricted integers','variables':len(eq['variables']),'residuals':len(ps),'degree':max(map(len,full)),'monomials':len(full),'coefficient_height':max(map(abs,full.values())),'residual_height':max(abs(c) for p in ps for c in p.values())}

def main(rebuild=False):
    pins=read('source_pins.json')
    for entry in pins['files']:
        data=(ROOT/entry['local']).read_bytes()
        require(hashlib.sha256(data).hexdigest()==entry['sha256'],'inherited source pin')
        require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==entry['git_blob_sha1'],'Git blob identity')
    old,interfaces,source,sc=[read(n) for n in ('baseline/factored.json','baseline/interfaces.json','source.json','source_change.json')]
    projected,pc,eq,tc,expanded=[read(n) for n in ('projected.json','projection.json','equation.json','translation.json','expanded_polynomial.json')]
    results={}
    results['source']=check_source(old,interfaces,source,sc)
    results['projection']=check_projection(source,projected,pc)
    results['translation']=check_translation(projected,eq,tc)
    metrics=expand_and_measure(eq,expanded);require(metrics==read('metrics.json'),'reported endpoint metrics');results['metrics']=metrics
    base=expand_and_measure(read('baseline/equation324.json'));bm=read('baseline/metrics324.json')
    require((base['variables'],base['residuals'],base['degree'],base['monomials'],base['coefficient_height'])==(bm['variables'],bm['rows'],bm['degree'],bm['monomials'],bm['height']),'literal baseline metrics')
    results['baseline']=base
    def rejected(action):
        try:action()
        except ValueError:return True
        raise ValueError('Corruption accepted')
    bad=copy.deepcopy(source);bad['residuals'][-1]['terms'][0][0]+=1
    rejected(lambda:check_source(old,interfaces,bad,sc))
    badpc=copy.deepcopy(pc);badpc['steps'][0]['restoration'][0][0]+=1
    rejected(lambda:check_projection(source,projected,badpc))
    badpoly=copy.deepcopy(expanded);badpoly['terms'][0][0]+=1
    rejected(lambda:expand_and_measure(eq,badpoly))
    results['rejected_corruptions']=3
    if rebuild:
        files=['source.json','source_change.json','projected.json','projection.json','projection_check.json','translation.json','equation.json','expanded_polynomial.json','metrics.json']
        with tempfile.TemporaryDirectory(prefix='direct314-') as d:
            cmd=[sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])+[str(ROOT/'code/build.py'),d]
            completed=subprocess.run(cmd,capture_output=True,text=True,check=True)
            for n in files:require((Path(d)/n).read_bytes()==(ROOT/n).read_bytes(),'deterministic rebuild '+n)
        results['byte_identical_rebuild_files']=len(files)
    results['status']='PASS';return results

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--rebuild',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args()
    result=main(a.rebuild);out=canonical(result)
    if a.output:a.output.write_bytes(out)
    print(json.dumps(result,sort_keys=True,indent=2))
