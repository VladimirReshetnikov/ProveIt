#!/usr/bin/env python3
"""Independent standard-library algebra replay; imports no artifact producer.
Checks affine export, every SOS coefficient, and complete monic elimination.
Not a proof of the inherited C222/Pell calibration.
"""
import argparse, collections, copy, hashlib, json
from fractions import Fraction
from pathlib import Path

def need(x,s):
    if not x: raise ValueError(s)
def collect(ts):
    out=collections.defaultdict(int)
    for c,m in ts: out[tuple(sorted(m))]+=c
    return {m:c for m,c in out.items() if c}
def serial(p): return [[int(c),list(m)] for m,c in sorted(p.items())]
def mul(p,q): return collect((a*b,ma+mb) for ma,a in p.items() for mb,b in q.items())
def substitute(p,images):
    out=[]
    for m,c in p.items():
        q={():c}
        for v in m: q=mul(q,images.get(v,{(v,):1}))
        out.extend((a,b) for b,a in q.items())
    return collect(out)
def shaobj(o):return hashlib.sha256(json.dumps(o,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def read(p):return json.loads(p.read_text())
def normrow(r):return collect(r['terms'])
def sos(eq):
    out=[]
    for r in eq['residuals']:
        p=normrow(r);out.extend((c,m) for m,c in mul(p,p).items())
    return collect(out)
def metrics(eq,p):
    ids={v for m in p for v in m}
    need(ids==set(range(len(eq['variables']))),'unused or out-of-range polynomial coordinate')
    need(all(len(m)<=2 for r in eq['residuals'] for m in normrow(r)),'nonquadratic residual')
    return {'variables':len(eq['variables']),'residuals':len(eq['residuals']),'monomials':len(p),'degree':max(map(len,p)),'height':max(map(abs,p.values()))}
def validate_proof(rest,pr):
    nonneg=pr['nonnegative_remainder']
    need(all(type(c)==int and c>0 and len(m)<=2 for c,m in nonneg),'invalid nonnegative monomial')
    total=collect(nonneg)
    for sq in pr['squares']:
        w=Fraction(*sq['weight']);need(w>0,'nonpositive square weight')
        form=collect((Fraction(*c),m) for c,m in sq['affine_form'])
        need(all(len(m)<=1 for m in form),'nonaffine square')
        total=collect([(c,m) for m,c in total.items()]+[(w*c,m) for m,c in mul(form,form).items()])
    need(total==rest,'false nonnegative identity')

def replay(raw,target,certificate):
    need(shaobj(raw)==certificate['source_equation_sha256'],'source hash mismatch')
    need(shaobj(target)==certificate['target_equation_sha256'],'target hash mismatch')
    need(raw['domain']==target['domain']=='nonnegative integers','wrong domain')
    rows={i:normrow(r) for i,r in enumerate(raw['residuals'])}; live=set(range(len(raw['variables'])))
    signed=0
    for j,s in enumerate(certificate['steps']):
        v,rid,sgn=s['variable_original_index'],s['source_row_id'],s['pivot_sign']
        need(v in live and rid in rows,'dead pivot')
        need(raw['variables'][v]['name']==s['variable_name'],'wrong pivot name')
        need(rows[rid]==collect(s['row_before']),'pivot prior mismatch')
        rest=collect(s['restoration']);need(len(rest)<=certificate['support_cap'],'support cap')
        need(all(type(c)==int and len(m)<=2 and v not in m and set(m)<=live for m,c in rest.items()),'invalid restoration')
        need(sgn in [-1,1],'nonunit pivot')
        expect=collect([(sgn,(v,))]+[(-sgn*c,m) for m,c in rest.items()])
        need(rows[rid]==expect,'wrong pivot identity')
        validate_proof(rest,s['nonnegative_certificate']); signed+=any(c<0 for c in rest.values())
        del rows[rid]
        for i,r in list(rows.items()):
            if any(v in m for m in r): rows[i]=substitute(r,{v:rest})
            need(all(len(m)<=2 for m in rows[i]),'degree increase')
        live.remove(v)
    retained=certificate['retained_original_indices_in_target_order']; unused=certificate['unused_original_indices_restored_to_zero']
    need(len(retained)==len(set(retained)) and len(unused)==len(set(unused)),'duplicate retained/unused')
    need(set(retained).isdisjoint(unused) and set(retained)|set(unused)==live,'incorrect coordinate partition')
    need({v for r in rows.values() for m in r for v in m}==set(retained),'used-variable mismatch')
    ids=[i for i,r in sorted(rows.items()) if r]
    need(ids==certificate['surviving_source_row_ids_in_target_order'],'surviving row mismatch')
    need([i for i,r in sorted(rows.items()) if not r]==certificate['zero_source_row_ids'],'zero row mismatch')
    need(len(ids)==len(target['residuals']),'target row count')
    rename={v:k for k,v in enumerate(retained)}
    for rid,tr in zip(ids,target['residuals']):
        expected=collect((c,tuple(rename[v] for v in m)) for m,c in rows[rid].items())
        need(expected==normrow(tr) and tr['label']==raw['residuals'][rid]['label'],'target row mismatch')
    need(target['variables']==[raw['variables'][v] for v in retained],'target metadata mismatch')
    return {'steps':len(certificate['steps']),'negative_coefficient_restorations':signed,'reverse_reconstruction':'Each restoration is an integer polynomial with proved nonnegative values on natural inputs, independent of its eliminated coordinate and all earlier-eliminated coordinates. Reverse step order restores every omitted coordinate uniquely; declared unused live coordinates may be set to zero.'}

def export_replay(meta,eq):
    vars=meta['variables']; rows=meta['rows']; gates={int(v):r for v,r in meta['gates'].items()}
    need(len(gates)==len(set(gates.values())),'duplicate gate row')
    for v,rid in gates.items():
        row=rows[rid];p=normrow(row);need(row['gate']==v and p.get((v,))==1,'invalid gate designation')
        need(all(all(w<v for w in m) for m in p if m!=(v,)),'nontriangular gate')
    images={}; deleted=set()
    for v in range(len(vars)):
        rid=gates.get(v); im=None
        if rid is not None and all(len(m)<=1 for m in normrow(rows[rid])):
            p=normrow(rows[rid]); need(p.pop((v,),None)==1,'nonmonic affine gate')
            im=substitute({m:-c for m,c in p.items()},images)
            need(all(c>=0 and len(m)<=1 for m,c in im.items()),'negative affine restoration')
            if len(im)<=4: deleted.add(rid)
            else: im=None
        images[v]=im if im is not None else {(v,):1}
    transformed=[]
    for rid,r in enumerate(rows):
        if rid in deleted: continue
        p=substitute(normrow(r),images)
        if p: transformed.append((r,p))
    gate_idx={r['gate']:i for i,(r,p) in enumerate(transformed) if r['gate'] is not None}
    keep={i for i,(r,p) in enumerate(transformed) if r['gate'] is None}
    used={v for i in keep for m in transformed[i][1] for v in m}
    while True:
        more={gate_idx[v] for v in used if v in gate_idx}-keep
        if not more: break
        keep|=more
        used|={v for i in more for m in transformed[i][1] for v in m}
    ordered=sorted(used); rename={v:i for i,v in enumerate(ordered)}
    expected=[{'label':r['label'],'terms':serial(collect((c,tuple(rename[v] for v in m)) for m,c in p.items()))} for i,(r,p) in enumerate(transformed) if i in keep]
    need(expected==eq['residuals'],'affine exporter replay residual mismatch')
    need([vars[v] for v in ordered]==eq['variables'],'affine exporter replay coordinates mismatch')
    dropped=[r for i,(r,p) in enumerate(transformed) if i not in keep]
    need(all(r['gate'] is not None and r['label'] in ('addition','multiplication') for r in dropped),'unproved dropped gate semantics')
    return {'input_variables':len(vars),'input_rows':len(rows),'affine_gates_eliminated':len(deleted),'unused_nonlinear_gates':len(dropped),'verified':True}

def majorant(cert):
    exps={i:1 for i,_ in enumerate(cert['inputs'])}
    def w(a):
        typ,n=a
        if typ=='c':return max(0,(n-1).bit_length())
        need(n in exps,'majorant forward reference');return exps[n]
    for g in cert['gates']:
        e=(max(w(g['left']),w(g['right']))+1 if g['operation']=='add' else w(g['left'])+w(g['right']))
        need(g['operation'] in ('add','mul') and e==g['exponent'],'majorant recurrence mismatch')
        exps[g['output']]=e
    need(w(cert['output'])==cert['exponent'],'majorant final exponent')
    return {'recurrence_verified':True,'exact_exponent':cert['exponent']}

def positive_exponents(meta):
    lower={}; gates={int(v):r for v,r in meta['gates'].items()}; report=[]
    for v in range(len(meta['variables'])):
        value=0
        if v in gates:
            row=meta['rows'][gates[v]]
            if row['label']!='nonnegative_square_difference':
                for c,m in row['terms']:
                    if m==[v]:continue
                    need(c<=0,'nonmonotone gate in syntactic positivity check')
                    a=-c
                    for w in m:a*=lower[w]
                    value=min(2,value+a)
        lower[v]=min(2,value)
    for j,p in enumerate(meta['powers']):
        typ,n=p['exponent']; bound=n if typ=='c' else lower[n]
        need(bound>=1,'power exponent not independently positive')
        report.append({'power':j,'exponent':p['exponent'],'syntactic_lower_bound':bound})
    return report

def audit(path):
    raw=read(path/'raw/equation.json');tar=read(path/'natural/equation.json');meta=read(path/'raw/raw_audit_input.json');c=read(path/'natural/elimination_certificate.json')
    res={'artifact':str(path),'affine_export':export_replay(meta,raw)}
    for name,eq in [('raw',raw),('natural',tar)]:
        p=sos(eq); need(p==collect(read(path/name/'expanded_polynomial.json')['terms']),name+' polynomial mismatch')
        res[name]=metrics(eq,p)
    res['contraction']=replay(raw,tar,c)
    res['local_majorant']=majorant(meta['local_majorant']);res['positive_exponents']=positive_exponents(meta)
    if 'derived_label_majorant' in meta['local_majorant']: res['derived_label_majorant']=majorant(meta['local_majorant']['derived_label_majorant'])
    if 'label_majorant' in meta: res['label_majorant']=majorant(meta['label_majorant'])
    res['sha256']={str(p.relative_to(path)):hashlib.sha256(p.read_bytes()).hexdigest() for p in path.rglob('*.json')}
    controls=[]
    for mode in ('coefficient','square_weight','partition'):
        bad=copy.deepcopy(c)
        if mode=='coefficient':bad['steps'][0]['restoration'][0][0]+=1
        elif mode=='partition':bad['retained_original_indices_in_target_order'].append(bad['retained_original_indices_in_target_order'][0])
        else:
            s=next(s for s in bad['steps'] if s['nonnegative_certificate']['squares'])
            s['nonnegative_certificate']['squares'][0]['weight'][0]=-1
        try:replay(raw,tar,bad)
        except ValueError as e:controls.append({'mutation':mode,'rejected':True,'reason':str(e)})
        else:raise ValueError('negative control accepted '+mode)
    res['negative_controls']=controls;res['verified']=True;return res

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directories',nargs='+',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result={'method':'Independent Python standard-library exact sparse integer algebra and rational-square checking; no producer imports','artifacts':[audit(x) for x in a.directories]}
    a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({x['artifact']:{k:x[k] for k in ('raw','natural','verified')} for x in result['artifacts']},indent=2))
