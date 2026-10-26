#!/usr/bin/env python3
"""Independent affine-even audit. No producer modules are imported."""
from pathlib import Path
from collections import defaultdict
import json,hashlib,sys,zipfile
from fractions import Fraction
ROOT=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parents[2]/'integer209/final'
SOURCE_HASH='20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a'
ARCHIVE_HASH='33fecaaa728d5f38608b8b0930c09b08dbe9a01e03f6269f092ec6142d72a0ee'
def need(x,m):
    if not x:raise ValueError(m)
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def p(terms):
    out={}
    for c,m in terms:
        need(type(c) is int and c!=0,'integer nonzero coefficient')
        need(type(m) is list and m==sorted(m) and all(type(i) is int and i>=0 for i in m),'monomial')
        need(tuple(m) not in out,'duplicate monomial');out[tuple(m)]=c
    return out
def add(*ps):
    out=defaultdict(int)
    for q in ps:
        for m,c in q.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def scale(q,k):return {m:k*c for m,c in q.items() if k*c}
def mul(q,r):
    out=defaultdict(int)
    for m,c in q.items():
        for n,d in r.items():out[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in out.items() if c}
def V(i):return {(i,):1}
def C(c):return {():c} if c else {}
def sq(q):return mul(q,q)
def subst(q,i,r):
    out={}
    for m,c in q.items():
        term=C(c)
        for j in m:term=mul(term,r if j==i else V(j))
        out=add(out,term)
    return out
def terms(q):return [[c,list(m)]for m,c in sorted(q.items())]

src=ROOT/'sources/parent210.json';need(sha(src)==SOURCE_HASH,'original210 equation pin')
old=read(src);rs=[p(r['terms'])for r in old['residuals']]
need(len(rs)==150 and len(old['variables'])==210,'source dimensions')
need(old['domain']=='unrestricted integers' and old['variables'][0]['name']=='t0','source domain and physical t')
need(old['variables'][178]['name']=='cofinal.horizon_root','old root binding')
need(rs[125]=={():-16,(0,):1,(178,178):-4},'old horizon row')
need([i for i,r in enumerate(rs)if any(178 in m for m in r)]==[125],'root private to deleted row')
need(sha(ROOT/'inherited/Source210.zip')==ARCHIVE_HASH,'complete original210 archive pin')
with zipfile.ZipFile(ROOT/'inherited/Source210.zip')as z:
    names=[n for n in z.namelist()if n.endswith('/equations/principal210/equation.json')]
    need(len(names)==1 and z.read(names[0])==src.read_bytes(),'original archive principal210 binding')
    prefix=names[0].split('equations/principal210/equation.json')[0]
    ops=read(ROOT/'coordinate_map.json')
    inherited=json.loads(z.read(prefix+'equations/principal210/certificate.json'))['operations']
    need(all(o.get('coordinate')!=0 for o in inherited),'optimized coordinate0 remains physical t')
    need(all(o.get('source')!=125 and o.get('target')!=125 and o.get('coordinate')!=178 for o in inherited),'no final operation uses horizon row or root')
    need(all(178 not in m for o in inherited if o['type']=='coordinate'for c,m in o['image']),'no final image uses root')
    stage_privacy=[]
    for stage in ['inherited/anchor/source/anchor219','stages/growth217','stages/source216','stages/projection211','stages/projection210','equations/principal210']:
        e=json.loads(z.read(prefix+stage+'/equation.json'))
        roots=[i for i,v in enumerate(e['variables'])if v['name']=='cofinal.horizon_root']
        hrows=[i for i,r in enumerate(e['residuals'])if r['label']=='cofinal.horizon']
        need(len(roots)==len(hrows)==1,'unique source horizon')
        h,hr=roots[0],hrows[0]
        need([i for i,r in enumerate(e['residuals'])if any(h in m for c,m in r['terms'])]==[hr],'private horizon at '+stage)
        need(p(e['residuals'][hr]['terms'])=={():-16,(0,):1,(h,h):-4},'unchanged horizon at '+stage)
        stage_privacy.append({'stage':stage,'root':h,'row':hr})
    radical=json.loads(z.read(prefix+'stages/projection211/certificate.json'))
    h,hr=184,131
    for step in radical['steps']:
        need(step['pivot']!=h and step['deleted_row']!=hr,'radical keeps horizon')
        need(all(i not in [h,0]for i,c in step['direction']),'radical direction fixes t and root')
        need(all(h not in m and 0 not in m for c,m in step['sheared_pivot_solution']),'radical restoration independent of horizon')
        h=step['retained_old_indices'].index(h);hr-=int(step['deleted_row']<hr)
    ac=json.loads(z.read(prefix+'stages/projection210/certificate.json'))
    need(ac['eliminated_coordinate']!=h and ac['omitted_residual']!=hr,'affine projection keeps horizon')
    need(all(i!=hr for c,i in ac['affine_consequence']['row_combination']),'affine consequence does not use horizon')
    need(all(h not in m for c,m in ac['restoration_terms_original_indices']),'affine restoration independent of root')

# The actual square-frame atoms in the optimized210 chart, independently
# derived from the source power ports and coordinate translations.
t=V(0);F=V(2);CC=scale(V(16),2);rad=add(C(2),scale(F,2),scale(CC,2))
atoms=[t,add(t,C(1)),add(F,t),V(1),t,V(3),F,V(4),V(8)]
atoms += [V(i)for i in range(9,16)]
atoms += [CC,V(17),add(V(94),C(-1)),V(94),rad]
atoms += [V(i)for i in [95,96,100,103,106,109,112,113,116,119,120,124,127]]
need(len(atoms)==34,'frame atom count')
need(rs[124]==add(V(130),C(-2),*(scale(sq(a),-1)for a in atoms)),'full physical square-frame identity')
ports=[(V(3),V(1),V(17)),(rad,V(1),add(V(94),C(-1)))]
plusindices=[add(F,t),V(8),V(9),V(10),V(11),V(12),V(13),V(14),V(15),CC]
ports += [(V(94),k,V(o))for k,o in zip(plusindices,[95,100,103,106,109,112,116,119,124,127])]
ports += [(add(V(94),C(-1)),k,V(o))for k,o in zip([t,V(4),V(1)],[96,113,120])]
need(len(ports)==15 and all(q in atoms for trip in ports for q in trip),'all45 retained power ports framed')

affine=add(scale(V(0),4),C(2)); transformed=[subst(r,0,affine)for r in rs]
keep=[i for i in range(210)if i!=178];rkeep=[i for i in range(150)if i!=125]
inverse={(0,):Fraction(1,4),():Fraction(-1,2)}
need(all(subst(transformed[i],0,inverse)==rs[i]for i in rkeep),'149 affine inverse identities on retained physical front')
ren={i:j for j,i in enumerate(keep)}
out=[{tuple(ren[j]for j in m):c for m,c in transformed[i].items()}for i in rkeep]
eq=read(ROOT/'integer209/equation.json')
need(eq['domain']=='unrestricted integers' and eq['polynomial']=='sum(square(row) for row in residuals)','output domain and sum of squares')
need(len(eq['variables'])==209 and len(eq['residuals'])==149,'output dimensions')
need([p(r['terms'])for r in eq['residuals']]==out,'every emitted residual coefficient')
need([r['label']for r in eq['residuals']]==[old['residuals'][i]['label']for i in rkeep],'all row labels')
need(eq['variables'][1:]==[old['variables'][i]for i in keep[1:]],'retained coordinate metadata')
need(eq['variables'][0]['kind']=='unrestricted_integer','affine parameter unrestricted')
need(all(len(m)<=2 for r in out for m in r),'quadratic residuals')
need({j for r in out for m in r for j in m}==set(range(209)),'all coordinates live')
cert=read(ROOT/'semantic_certificate.json');maps=read(ROOT/'coordinate_map.json')
frame=read(ROOT/'frame_certificate.json')
need(frame['constant']==2 and frame['source_row']==frame['output_row']==124,'frame certificate parameters')
need(frame['power_ports']==45 and frame['power_requests']==15,'frame certificate ports')
need([p(a['parent_terms'])for a in frame['atoms']]==atoms,'all parent frame certificate atoms')
need([p(a['actual_terms'])for a in frame['atoms']]==[subst(a,0,affine)for a in atoms],'all affine frame certificate atoms')
need(p(frame['old_frame'])==rs[124] and p(frame['new_frame'])==out[124],'both certified frame rows')
need(cert['source']=='sources/parent210.json' and cert['source_sha256']==SOURCE_HASH,'semantic source pin')
for obj in [cert,maps]:
    need(obj['actual_t']==terms(affine),'actual affine t map')
    need(obj['retained_old_coordinates']==keep and obj['retained_old_rows']==rkeep,'retained maps')
    need(obj['old_to_new']==[[i,j]for i,j in ren.items()],'renumbering')
need(cert['deleted_coordinate']==178 and cert['deleted_row']==125,'semantic deletion')
edits=[{'old_row':i,'label':old['residuals'][i]['label'],'before':terms(rs[i]),'after_before_renumbering':terms(transformed[i])}for i in rkeep if transformed[i]!=rs[i]]
need(edits==cert['changed_retained_rows'],'complete substitution edit certificate')
need([x['old_row']for x in edits]==[0,124,136,147,149],'only five retained rows change')
delta=2**19
need(out[-3]==add(V(207),scale(mul(affine,F),-1)),'growth product')
need(out[-2]==add(sq(V(206)),scale(sq(V(207)),-16),scale(mul(V(207),F),-8),C(-1)),'growth norm')
need(out[-1]==add(F,scale(mul(affine,add(scale(V(208),2),C(1))),-delta)),'growth divisibility')
full=add(*(sq(r)for r in out));actual=read(ROOT/'integer209/expanded_polynomial.json')
need(actual['variables']==209 and p(actual['terms'])==full,'every collected quartic coefficient')
metric={'variables':209,'rows':149,'degree':max(map(len,full)),'monomials':len(full),'height':max(map(abs,full.values())),'row_height':max(abs(c)for r in out for c in r.values()),'residual_terms':sum(map(len,out))}
need(metric==read(ROOT/'integer209/metrics.json'),'all metrics')
need(17**8>2**32 and delta*2-1>=8,'smallest horizon growth threshold')
need(2**23*(32+2)<2**32,'local dyadic precision threshold')
receipt={'status':'PASS','scope':'Independent exact affine substitution, private deletion, physical frame/ports, every residual and expanded coefficient. Semantic equivalence is ordinary proof, not old-zero-set bijection.','metrics':metric,'changed_retained_rows':[x['old_row']for x in edits],'retained_inverse_identities':149,'frame_atoms':34,'power_requests':15,'power_ports':45,'inherited_horizon_privacy':stage_privacy,'inherited_radical_steps_fixing_t_and_root':len(radical['steps']),'equation_sha256':sha(ROOT/'integer209/equation.json'),'expansion_sha256':sha(ROOT/'integer209/expanded_polynomial.json'),'source210_sha256':SOURCE_HASH,'source210_archive_sha256':sha(ROOT/'inherited/Source210.zip'),'optimized_python':bool(sys.flags.optimize)}
print(json.dumps(receipt,sort_keys=True))
