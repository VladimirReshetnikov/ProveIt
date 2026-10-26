#!/usr/bin/env python3
"""Independent source graft check for divisibility-forced Pell growth.

Reconstructs the actual semantic square frame, all thirteen retained principal
Pell pairs, their norms, orientation pool, and anchor cap. Does not import any
producer or inherited polynomial helper. Semantic unbounded proofs are separate.
"""
from collections import defaultdict
from pathlib import Path
import argparse,hashlib,json,copy,tempfile,importlib.util
ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'inherited/anchor/source/anchor219/equation.json'

def p(ts):
    d=defaultdict(int)
    for c,m in ts:
        if type(c) is not int or c==0 or type(m) is not list or any(type(j) is not int for j in m) or m!=sorted(m):
            raise ValueError('Invalid literal integer polynomial term')
        if tuple(m) in d:raise ValueError('Duplicate literal monomial')
        d[tuple(m)]+=c
    return {m:c for m,c in d.items() if c}

def V(i):return {(i,):1}
def C(i):return {():i} if i else {}
def plus(*args):
    d=defaultdict(int)
    for q in args:
        for m,c in q.items():d[m]+=c
    return {m:c for m,c in d.items() if c}
def times(a,b):
    d=defaultdict(int)
    for m,c in a.items():
        for n,e in b.items():d[tuple(sorted(m+n))]+=c*e
    return {m:c for m,c in d.items() if c}
def neg(a):return {m:-c for m,c in a.items()}
def sc(k,a):return {m:k*c for m,c in a.items() if k*c}
def minus(a,b):return plus(a,neg(b))
def sq(a):return times(a,a)
def need(t,msg):
    if not t:raise ValueError(msg)
def repl(a,i,b):
    d={}
    for m,c in a.items():
        x=C(c)
        for j in m:x=times(x,b if j==i else V(j))
        d=plus(d,x)
    return d

def check(growth,composition=None,parent=PARENT):
    old=json.loads(parent.read_text());new=json.loads((growth/'equation.json').read_text())
    need(old.get('domain')=='unrestricted integers' and new.get('domain')=='unrestricted integers','incorrect integer domain')
    e=1<<20
    t,F,A=V(0),V(2),plus(V(137),C(1))
    # Actual signed canonical pairs, reconstructed independently from the
    # source's named power interface, including two historical offsets.
    pair_data=[(141,142,143,t,0,0),(150,151,152,plus(F,t),0,0),
       (153,154,155,plus(V(8),C(-1)),-1,0),
       (156,157,158,V(9),0,0),(159,160,161,V(10),0,0),
       (162,163,164,V(11),0,0),(165,166,167,V(12),0,0),
       (168,169,170,V(4),0,0),(171,172,173,V(13),0,0),
       (174,175,176,V(14),0,0),(177,178,179,V(1),0,1),
       (180,181,182,V(15),0,0),(183,184,185,sc(2,V(16)),0,0)]
    old_polys=[p(r['terms']) for r in old['residuals']]
    norms=[];orient={};cap=minus(sq(V(184)),plus(sq(sc(2,V(16))),C(1),sq(V(207)),sq(V(208)),times(V(209),plus(V(209),C(1)))))
    for d,y,z,k,ys,zs in pair_data:
        D,Y,Z=V(d),plus(V(y),C(ys)),plus(V(z),C(zs));X=plus(D,Z)
        wire=minus(Z,times(A,Y));norm=minus(plus(sq(D),sc(2,times(D,Z)),sq(Y)),C(1))
        need(wire in old_polys,'retained AY wire missing')
        need(norm in old_polys,'retained norm missing')
        # Remove the norm polynomial from the exact error-square expression.
        # This independently reconstructs the reduced quadratic orientation row.
        orient=plus(orient,minus(plus(sq(minus(X,C(1))),sq(minus(Y,k))),norm))
        if y!=184:cap=minus(cap,sq(Y))
        norms.append({'D':d,'Y':y,'Z':z,'Y_offset':ys,'Z_offset':zs})
    orient=minus(orient,times(V(137),V(204)))
    # Exact square frame. D_old is still the named old self-radix base here;
    # the affine radix composition below updates that atom as well.
    atoms=[t,plus(t,C(1)),plus(F,t),V(1),t,V(3),F,V(4),plus(V(8),C(-1))]
    atoms += [V(i) for i in range(9,16)]
    atoms += [sc(2,V(16)),V(17),plus(V(100),C(-1)),V(100),V(189)]
    atoms += [V(i) for i in [101,102,106,109,112,115,118,119,122,125,126,130,133]]
    frame=minus(V(136),plus(C(2),*(sq(a) for a in atoms)))
    # The old individual exact power certificate at base t and exponent ell*t.
    need(old_polys[102]==plus(V(144),sq(t),sc(-2,times(A,t)),C(1)),'old growth modulus')
    need(old_polys[103]==plus(F,neg(V(186)),neg(times(t,V(187))),times(V(144),V(145))),'old growth power')
    need(old_polys[132]==minus(V(188),times(A,V(187))),'old growth AY')
    need(old_polys[133]==minus(plus(sq(V(186)),sc(2,times(V(186),V(188))),sq(V(187))),C(1)),'old growth norm')
    # Verify that old frame, pool and cap agree with this independent interface
    # upon restoring just the removed growth member.
    need(old_polys[134]==minus(frame,sq(sc(e,t))),'parent square frame mismatch')
    D,Y,Z=V(186),V(187),V(188);X=plus(D,Z)
    ng=old_polys[133]
    contribution=minus(plus(sq(minus(X,C(1))),sq(minus(Y,sc(e,t)))),ng)
    need(old_polys[147]==plus(orient,contribution),'parent orientation mismatch')
    need(old_polys[150]==minus(cap,sq(Y)),'parent cap mismatch')
    expected=[]
    for i,r in enumerate(old['residuals']):
        if i in {102,103,132,133}:continue
        value={134:frame,147:orient,150:cap}.get(i,old_polys[i])
        expected.append((r['label'],value))
    X,Z,u=V(219),V(220),V(221)
    expected += [('growth_pell.product',minus(Z,times(t,F))),
      ('growth_pell.norm',minus(minus(minus(sq(X),sc(16,sq(Z))),sc(8,times(Z,F))),C(1))),
      ('growth_pell.divisibility',minus(F,sc(1<<19,times(t,plus(sc(2,u),C(1))))))]
    oldvars=old['variables']+[{'name':name,'kind':'signed_growth_witness'} for name in ['growth_pell.X','growth_pell.tF','growth_pell.odd_half']]
    live=sorted({i for _,r in expected for m in r for i in m});ren={i:j for j,i in enumerate(live)}
    need(set(range(222))-set(live)=={144,145,186,187,188},'unexpected removed coordinates')
    need(new['variables']==[oldvars[i] for i in live],'variable table mismatch')
    need(len(expected)==len(new['residuals']),'row count mismatch')
    for i,((label,r),out) in enumerate(zip(expected,new['residuals'])):
        need(label==out['label'],f'label {i} mismatch')
        rr={tuple(ren[j] for j in m):c for m,c in r.items()}
        need(rr==p(out['terms']),f'row {i} mismatch')
        need(max(map(len,rr),default=0)<=2,'nonquadratic residual')
    full={}
    for r in new['residuals']:full=plus(full,sq(p(r['terms'])))
    need(full==p(json.loads((growth/'expanded_polynomial.json').read_text())['terms']),'expansion mismatch')
    receipt={'status':'PASS','independent_parent_frame_atoms':len(atoms)+1,'retained_frame_atoms':len(atoms),'retained_principal_pairs':len(pair_data),
             'variables':len(new['variables']),'rows':len(expected),'degree':max(map(len,full)),'monomials':len(full),'height':max(map(abs,full.values())),
             'parent_sha256':hashlib.sha256(parent.read_bytes()).hexdigest(),'growth_equation_sha256':hashlib.sha256((growth/'equation.json').read_bytes()).hexdigest(),
             'scope':'Exact finite source graft, canonical-interface binding, all frame/pool/cap coefficients, and collected polynomial. Unbounded semantic proof is separate.'}
    if composition is not None:
        eq=json.loads((composition/'equation.json').read_text())
        need(eq.get('domain')=='unrestricted integers','incorrect composition domain')
        names={v['name']:i for i,v in enumerate(new['variables'])}
        d=names['self_radix.BH'];c=names['crt.even_index_half'];f=names['growth.F']
        replacement=plus(C(2),sc(4,V(c)),sc(2,V(f)))
        expected=[(r['label'],repl(p(r['terms']),d,replacement)) for r in new['residuals'] if r['label']!='self_radix.base_definition']
        live=sorted({j for _,r in expected for m in r for j in m});ren2={j:i for i,j in enumerate(live)}
        need(eq['variables']==[new['variables'][i] for i in live],'composition variables')
        need(len(expected)==len(eq['residuals']),'composition rows')
        for i,((lab,row),r) in enumerate(zip(expected,eq['residuals'])):
            need(lab==r['label'],'composition label')
            rr={tuple(ren2[j] for j in m):v for m,v in row.items()}
            need(rr==p(r['terms']),f'composition row {i}')
        pol={}
        for r in eq['residuals']:pol=plus(pol,sq(p(r['terms'])))
        need(pol==p(json.loads((composition/'expanded_polynomial.json').read_text())['terms']),'composition expansion')
        receipt['affine_radix_composition']={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(map(len,pol)),'monomials':len(pol),'height':max(map(abs,pol.values()))}
    return receipt

def write_json(path,obj):
    path.write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')

def source_mutations(growth,parent):
    original=json.loads((growth/'equation.json').read_text())
    expanded=json.loads((growth/'expanded_polynomial.json').read_text())
    trials=[]
    def change(label,kind):
        eq=copy.deepcopy(original);ex=copy.deepcopy(expanded)
        if kind=='domain':eq['domain']='nonnegative integers'
        elif kind=='expansion':ex['terms'][0][0]+=1
        elif kind=='noninteger':eq['residuals'][0]['terms'][0][0]=float(eq['residuals'][0]['terms'][0][0])
        else:
            row=next(r for r in eq['residuals'] if r['label']==kind)
            row['terms'][0][0]*=-1
        trials.append((label,eq,ex))
    for label,kind in [
      ('growth norm coefficient changed','growth_pell.norm'),
      ('growth divisibility coefficient changed','growth_pell.divisibility'),
      ('growth product coefficient changed','growth_pell.product'),
      ('actual frame coefficient changed','shared.frame_definition'),
      ('retained orientation pool changed','cap.pooled_index_residue'),
      ('anchor cap coefficient changed','domain_guard.3'),
      ('collected polynomial coefficient changed','expansion'),
      ('integer domain silently restricted','domain'),
      ('noninteger literal coefficient','noninteger')]:change(label,kind)
    receipt=[]
    with tempfile.TemporaryDirectory(prefix='conzfc-graft-corruption-') as d:
        d=Path(d)
        for label,eq,ex in trials:
            write_json(d/'equation.json',eq);write_json(d/'expanded_polynomial.json',ex)
            try:check(d,parent=parent)
            except ValueError as err:receipt.append({'mutation':label,'rejected':True,'reason':str(err)})
            else:raise ValueError('Corruption accepted: '+label)
    return receipt


def canonical(obj):return (json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()
def sha(obj):return hashlib.sha256(canonical(obj)).hexdigest()
def read_eq(folder):return json.loads((folder/'equation.json').read_text())
def expand_doc(doc):
    need(doc.get('domain')=='unrestricted integers','wrong domain in projected equation')
    n=len(doc['variables']);out={}
    for row in doc['residuals']:
        rr=p(row['terms'])
        need(all(len(m)<=2 and all(0<=j<n for j in m) for m in rr),'invalid residual coordinates/degree')
        out=plus(out,sq(rr))
    need({j for m in out for j in m}==set(range(n)),'unused final polynomial coordinate')
    return out

def verify_expansion(folder,doc):
    out=expand_doc(doc);data=json.loads((folder/'expanded_polynomial.json').read_text())
    need(data.get('variables',len(doc['variables']))==len(doc['variables']),'expanded dimension')
    need(out==p(data['terms']),'collected coefficient mismatch at '+str(folder))
    measured={'variables':len(doc['variables']),'rows':len(doc['residuals']),'degree':max(map(len,out)),
       'monomials':len(out),'height':max(map(abs,out.values())),
       'row_height':max(abs(c) for row in doc['residuals'] for c,m in row['terms'])}
    supplied=json.loads((folder/'metrics.json').read_text())
    mapping={'residuals':'rows','collected_terms':'monomials','coefficient_height':'height'}
    for k,v in supplied.items():
        if k=='residual_terms':need(v==sum(len(row['terms']) for row in doc['residuals']),'residual support mismatch')
        else:need(mapping.get(k,k) in measured and measured[mapping.get(k,k)]==v,'metrics mismatch: '+k)
    return measured


def operations(rows,ops,inverse=False):
    rows=copy.deepcopy(rows);n=max((j for r in rows for m in r for j in m),default=-1)+1
    for op in reversed(ops) if inverse else ops:
        need(type(op) is dict,'operation shape')
        if op.get('type')=='row':
            i,j,k=op['target'],op['source'],op['multiple']
            need(type(i) is int and type(j) is int and i!=j and 0<=i<len(rows) and 0<=j<len(rows),'noninvertible row operation')
            need(type(k) is int,'noninteger row multiplier')
            rows[i]=plus(rows[i],sc(-k if inverse else k,rows[j]))
        elif op.get('type')=='coordinate':
            i=op['coordinate'];im=p(op['image'])
            need(type(i) is int and 0<=i<n,'coordinate out of range')
            need(all(len(m)<=1 and all(0<=j<n for j in m) for m in im),'nonaffine/invalid coordinate image')
            need(im.get((i,))==1,'coordinate map is not a unit shear')
            if inverse:im=minus(sc(2,V(i)),im)
            rows=[repl(r,i,im) for r in rows]
        else:raise ValueError('Unknown elementary operation')
    return rows


def check_chain(composition,radical,affine,optimized,helper,mutations=True,require_affine_hashes=True):
    spec=importlib.util.spec_from_file_location('independent_projection_audit',helper)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    source=read_eq(composition);cert=json.loads((radical/'certificate.json').read_text());current=source
    need(cert.get('schema')=='common_hessian_radical_projection_v1','radical certificate schema')
    steps=[]
    for step in cert['steps']:
        current=mod.one_step(current,step,numerical_controls=False)
        steps.append({'variables':len(current['variables']),'rows':len(current['residuals']),'sha256':sha(current)})
    need(current==read_eq(radical),'radical equation mismatch')
    radical_metric=verify_expansion(radical,current)
    rc=mod.mutation_controls(source,cert['steps'][0]) if mutations and cert['steps'] else []
    ac=json.loads((affine/'certificate.json').read_text());adoc=read_eq(affine)
    if require_affine_hashes or 'input_sha256' in ac or 'output_sha256' in ac:
        need(ac.get('input_sha256')==sha(current) and ac.get('output_sha256')==sha(adoc),'affine hash binding')
    need(mod.affine_projection(current,ac)==adoc,'affine equation mismatch')
    am=verify_expansion(affine,adoc);amuts=[]
    if mutations:
        for label,field in [('affine row-combination changed','combination'),('affine restoration changed','restoration')]:
            bad=copy.deepcopy(ac)
            if field=='combination':bad['affine_consequence']['row_combination'][0][0]+=1
            else:bad['restoration_terms_original_indices'][0][0]+=1
            try:
                result=mod.affine_projection(current,bad)
                need(result==adoc,'mutated affine result differs')
            except ValueError as err:amuts.append({'mutation':label,'rejected':True,'reason':str(err)})
            else:raise ValueError('Affine corruption accepted')
    oc=json.loads((optimized/'certificate.json').read_text());odoc=read_eq(optimized)
    need(oc['input_sha256']==sha(adoc) and oc['output_sha256']==sha(odoc),'optimization hash binding')
    need(adoc['variables']==odoc['variables'],'optimization changed coordinates table')
    need([r['label'] for r in adoc['residuals']]==[r['label'] for r in odoc['residuals']],'optimization row labels')
    before=[p(r['terms']) for r in adoc['residuals']];after=[p(r['terms']) for r in odoc['residuals']]
    ops=oc['operations']
    need(operations(before,ops)==after,'forward optimization coefficient identity')
    need(operations(after,ops,inverse=True)==before,'composed inverse coefficient identity')
    om=verify_expansion(optimized,odoc);omuts=[]
    if mutations:
        # These controls alter the actual maps rather than only their hashes.
        for label,kind in [('nonunit coordinate multiplier','nonunit'),('self row addition','self_row'),('first operation omitted','omit')]:
            bad=copy.deepcopy(ops)
            if kind=='nonunit':
                op=next(o for o in bad if o['type']=='coordinate');i=op['coordinate']
                next(term for term in op['image'] if term[1]==[i])[0]=2
            elif kind=='self_row':
                op=next(o for o in bad if o['type']=='row');op['source']=op['target']
            else:bad.pop(0)
            try:need(operations(before,bad)==after,'mutated optimization differs')
            except ValueError as err:omuts.append({'mutation':label,'rejected':True,'reason':str(err)})
            else:raise ValueError('Optimization corruption accepted')
    return {'status':'PASS','common_radical_steps':steps,'radical_metrics':radical_metric,'affine_metrics':am,
       'final_metrics':om,'elementary_operations':len(ops),'forward_and_composed_inverse':True,
       'affine_input_sha256':sha(current),'affine_output_sha256':sha(adoc),
       'final_sha256':sha(odoc),'radical_mutations':rc,'affine_mutations':amuts,'optimization_mutations':omuts,
       'independent_projection_helper_sha256':hashlib.sha256(helper.read_bytes()).hexdigest()}


if __name__=='__main__':
    a=argparse.ArgumentParser()
    a.add_argument('--growth',type=Path,default=ROOT/'stages/growth217')
    a.add_argument('--composition',type=Path)
    a.add_argument('--parent',type=Path,default=PARENT)
    a.add_argument('--radical',type=Path)
    a.add_argument('--affine',type=Path)
    a.add_argument('--optimized',type=Path)
    a.add_argument('--projection-helper',type=Path,default=PARENT.parents[2]/'code/audit_projection.py')
    a.add_argument('--mutations',action='store_true')
    a.add_argument('--receipt',type=Path)
    v=a.parse_args();r=check(v.growth,v.composition,v.parent)
    if v.mutations:r['source_mutations']=source_mutations(v.growth,v.parent)
    if any(x is not None for x in [v.radical,v.affine,v.optimized]):
        need(all(x is not None for x in [v.composition,v.radical,v.affine,v.optimized]),'all chain directories are required')
        r['projection_and_optimization']=check_chain(v.composition,v.radical,v.affine,v.optimized,v.projection_helper,v.mutations)
    s=json.dumps(r,indent=2)+'\n'
    if v.receipt:v.receipt.write_text(s)
    print(s,end='')
