#!/usr/bin/env python3
"""Independent universal-identity and expansion checker. Imports no producer."""
import argparse,collections,hashlib,itertools,json,tempfile,subprocess,sys,copy
from pathlib import Path
def require(condition,message):
    if not condition:raise ValueError(message)
def clean(p):return {m:c for m,c in p.items() if c}
def poly(terms):
    p={}
    for c,m in terms:
        require(type(c) is int and c!=0 and all(type(i) is int and i>=0 for i in m),'integer sparse term')
        key=tuple(m);require(list(m)==sorted(m) and key not in p,'canonical unique monomial');p[key]=c
    return p
def linear(a,b,k):
    z=collections.Counter(a)
    for m,c in b.items():z[m]+=k*c
    return clean(z)
def multiply(p,q):
    out=collections.Counter()
    for (m,c),(n,d) in itertools.product(p.items(),q.items()):out[tuple(sorted(m+n))]+=c*d
    return clean(out)
def evaluate_symbolic(p,values):
    z=collections.Counter()
    for m,c in p.items():
        f={():c}
        for j in m:f=multiply(f,values[j])
        z.update(f)
    return clean(z)
def verify(root,item,cert=None,eq=None,expanded=None):
    raw=(root/item['source']).read_bytes();require(hashlib.sha256(raw).hexdigest()==item['source_sha256'],'pinned source bytes');source=json.loads(raw)
    if cert is None:cert=json.loads((root/item['certificate']).read_text())
    out=root/item['directory']
    if eq is None:eq=json.loads((out/'equation.json').read_text())
    if expanded is None:expanded=json.loads((out/'expanded_polynomial.json').read_text())
    require(source['domain']==eq['domain']=='unrestricted integers','unrestricted integer domains')
    initial=[poly(r['terms']) for r in source['residuals']];n=len(source['variables']);rows=copy.deepcopy(initial);identity=[{(i,):1} for i in range(n)];names={v['name']:i for i,v in enumerate(source['variables'])};require(len(names)==n,'unique coordinate names')
    # Check every coordinate transformation and its inverse as polynomial identities.
    coordinate_indices=[]
    for target,inputs in cert['coordinate_shears']:
        t=names[target];require(target not in inputs and all(type(c) is int for c in inputs.values()),'triangular integral shear')
        forward=copy.deepcopy(identity);inverse=copy.deepcopy(identity)
        for name,c in inputs.items():forward[t]=linear(forward[t],identity[names[name]],c);inverse[t]=linear(inverse[t],identity[names[name]],-c)
        require(all(evaluate_symbolic(forward[i],inverse)==identity[i] and evaluate_symbolic(inverse[i],forward)==identity[i] for i in range(n)),'coordinate inverse')
        rows=[evaluate_symbolic(r,forward) for r in rows];coordinate_indices.append((t,{names[s]:c for s,c in inputs.items()}))
    exposure=cert['affine_exposure_row_operations']
    for i,j,k in exposure:
        require(i!=j and 0<=i<len(rows) and 0<=j<len(rows) and type(k) is int,'elementary row operation')
        before=rows[i];rows[i]=linear(rows[i],rows[j],k);require(linear(rows[i],rows[j],-k)==before,'row inverse')
    erased_rows=[];erased_vars=[]
    for step in cert['affine_projections']:
        i,t=step['row'],step['variable'];v=poly(step['replacement']);r=rows[i]
        require(i not in erased_rows and t not in erased_vars,'unique projection')
        require(max(map(len,r))<=1 and r.get((t,)) in (-1,1),'unit affine equation')
        require(all(t not in m for m in v),'nonrecursive affine reconstruction')
        require(max(map(len,v),default=0)<=1,'affine replacement')
        require(source['variables'][t]['name']==step['name'],'coordinate name binding')
        replacements=copy.deepcopy(identity);replacements[t]=v
        require(not evaluate_symbolic(r,replacements),'affine identity before drop')
        rows=[evaluate_symbolic(r,replacements) for r in rows]
        require(not rows[i] and all(t not in m for r in rows for m in r),'zero row and eliminated coordinate absence')
        erased_rows.append(i);erased_vars.append(t)
    keep=[i for i in range(n) if i not in erased_vars];ren={i:j for j,i in enumerate(keep)};projected=[{tuple(ren[i] for i in m):c for m,c in r.items()} for j,r in enumerate(rows) if j not in erased_rows]
    require(eq['variables']==[source['variables'][i] for i in keep],'exact coordinate list')
    final=[poly(r['terms']) for r in eq['residuals']];require(len(final)==len(projected),'exact row count')
    backwards=copy.deepcopy(final)
    for i,j,k in reversed(cert['final_row_operations']):
        require(i!=j and 0<=i<len(backwards) and 0<=j<len(backwards) and type(k) is int,'final unimodular row operation')
        backwards[i]=linear(backwards[i],backwards[j],-k)
    require(backwards==projected,'reverse row certificate')
    # Reconstruct original coordinates as affine polynomials in final coordinates.
    restore={i:{(j,):1} for j,i in enumerate(keep)}
    for step in reversed(cert['affine_projections']):restore[step['variable']]=evaluate_symbolic(poly(step['replacement']),restore)
    require(set(restore)==set(range(n)),'total restoration map')
    restored_projected=[];it=iter(backwards)
    for i in range(len(initial)):restored_projected.append({} if i in erased_rows else next(it))
    for i,j,k in reversed(exposure):restored_projected[i]=linear(restored_projected[i],restored_projected[j],-k)
    for t,inputs in reversed(coordinate_indices):
        for j,c in inputs.items():restore[t]=linear(restore[t],restore[j],c)
    published=json.loads((out/'RESTORATION.json').read_text())['coordinates']
    require(len(published)==n,'complete published restoration map')
    for i,entry in enumerate(published):
        require(entry['index']==i and entry['name']==source['variables'][i]['name'] and poly(entry['terms'])==restore[i],'published restoration coordinate')
    pullback=[evaluate_symbolic(r,restore) for r in initial]
    require(pullback==restored_projected,'universal original-row restoration identities')
    P=collections.Counter()
    for r in final:
        terms=list(r.items())
        for j,(m,c) in enumerate(terms):
            P[tuple(sorted(m+m))]+=c*c
            for v,d in terms[j+1:]:P[tuple(sorted(m+v))]+=2*c*d
    P=clean(P);require(P==poly(expanded['terms']),'every collected quartic coefficient')
    actual={'variables':len(keep),'rows':len(final),'degree':max(map(len,P)),'monomials':len(P),'height':max(map(abs,P.values())),'row_degree':max(len(m) for r in final for m in r),'row_height':max(abs(c) for r in final for c in r.values()),'row_support':sum(map(len,final)),'used_coordinates':sorted({i for m in P for i in m})}
    require(actual==json.loads((out/'METRICS.json').read_text()),'metrics equality');require(actual['degree']==4 and actual['row_degree']<=2,'degree bounds');require(actual['used_coordinates']==list(range(len(keep))),'all declared coordinates live')
    return actual
def main():
    p=argparse.ArgumentParser();p.add_argument('--release',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--rebuild',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args();manifest=json.loads((a.release/'ENDPOINTS.json').read_text());results={};controls=[]
    for name,item in manifest['endpoints'].items():results[name]=verify(a.release,item)
    name,item=next(iter(manifest['endpoints'].items()));cert=json.loads((a.release/item['certificate']).read_text());eq=json.loads((a.release/item['directory']/'equation.json').read_text());expanded=json.loads((a.release/item['directory']/'expanded_polynomial.json').read_text())
    mutations=[]
    bad=copy.deepcopy(cert);bad['affine_projections'][0]['replacement'][0][0]+=1;mutations.append(('wrong affine reconstruction',bad,None,None))
    bad=copy.deepcopy(cert);bad['final_row_operations'][0][2]+=1;mutations.append(('wrong row shear',bad,None,None))
    bad=copy.deepcopy(cert);bad['coordinate_shears'][0][1][next(iter(bad['coordinate_shears'][0][1]))]+=1;mutations.append(('wrong coordinate shear',bad,None,None))
    bad=copy.deepcopy(eq);bad['residuals'][0]['terms'][0][0]+=1;mutations.append(('wrong final residual',None,bad,None))
    bad=copy.deepcopy(expanded);bad['terms'][0][0]+=1;mutations.append(('wrong expanded coefficient',None,None,bad))
    for title,c,e,x in mutations:
        try:verify(a.release,item,c,e,x)
        except (ValueError,KeyError,IndexError,StopIteration):controls.append(title)
        else:raise ValueError('accepted corruption: '+title)
    if a.rebuild:
        with tempfile.TemporaryDirectory() as td:
            subprocess.run([sys.executable,'-B',str(a.release/'build.py'),'--release',str(a.release),'--output',td],check=True,capture_output=True)
            for item in manifest['endpoints'].values():
                for file in ['equation.json','expanded_polynomial.json','METRICS.json']:require((a.release/item['directory']/file).read_bytes()==(Path(td)/Path(item['directory']).name/file).read_bytes(),'byte-identical rebuild')
    receipt={'status':'pass','optimized_python':not __debug__,'endpoints':results,'corruption_controls_rejected':controls,'byte_identical_rebuild':a.rebuild,'scope':'Exact finite polynomial identities and all-integer zero-set transformations; not a consistency test or a Lean build.'}
    text=json.dumps(receipt,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
