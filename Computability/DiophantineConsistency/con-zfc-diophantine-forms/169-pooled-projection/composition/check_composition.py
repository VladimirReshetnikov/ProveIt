#!/usr/bin/env python3
"""Independent exact checker: factorial-free source242 to pooled P223.

Imports no producer or optimizer. All arithmetic is integer sparse polynomial
arithmetic. Unbounded semantic proofs are separate from this finite audit.
"""
from pathlib import Path
from collections import defaultdict
import argparse,copy,hashlib,json
from check_frame import check as frame_check, check_data as frame_data_check

def require(b,s):
    if not b:raise ValueError(s)
def add(*ps):
    r=defaultdict(int)
    for p in ps:
        for m,c in p.items():r[m]+=c
    return {m:c for m,c in r.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
def mul(p,q):
    r=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():r[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in r.items() if c}
def scale(k,p):return {m:k*c for m,c in p.items() if k*c}
def v(i):return {(i,):1}
def c(k):return {():k} if k else {}
def enc(p):return [[z,list(m)] for m,z in sorted(p.items())]
def dec(ts):
    p={}
    require(isinstance(ts,list),'terms must be list')
    for item in ts:
        require(isinstance(item,list) and len(item)==2,'coefficient/monomial pair')
        z,m=item
        require(type(z) is int and z!=0,'nonzero integer coefficient')
        require(isinstance(m,list) and all(type(i) is int and i>=0 for i in m),'integer indices')
        require(m==sorted(m),'monomial order')
        require(tuple(m) not in p,'no duplicated monomials')
        p[tuple(m)]=z
    return p
def sub(p,q):return add(p,neg(q))
def subst(p,mp):
    r={}
    for m,z in p.items():
        q=c(z)
        for i in m:q=mul(q,mp.get(i,v(i)))
        r=add(r,q)
    return r
def rows(e):
    require(e['domain']=='unrestricted integers','integer domain')
    require(len({z['name'] for z in e['variables']})==len(e['variables']),'unique variable names')
    rr=[dec(r['terms']) for r in e['residuals']]
    require(all(len(m)<=2 and all(i<len(e['variables']) for i in m) for r in rr for m in r),'quadratic valid variable indices')
    return rr
def names(e):return {z['name']:i for i,z in enumerate(e['variables'])}
def renumber(p,mp):return {tuple(sorted(mp[i] for i in m)):z for m,z in p.items()}
def unique(rr,p):
    hits=[i for i,r in enumerate(rr) if r==p]
    require(len(hits)==1,'expected exactly one literal polynomial row')
    return hits[0]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_bytes())

def strict_check(a,b,ct):
    rr=rows(a);ss=rows(b);ns=names(a)
    removed_names=['pow6.output','index_addition.D','pow6.quotient','remainder_budget.ratio1']
    rm={ns[s] for s in removed_names};p6=ns['pow6.output'];ratio1=ns['remainder_budget.ratio1'];ratio0=ns['remainder_budget.ratio0']
    uses={i:[j for j,r in enumerate(rr) if any(i in m for m in r)] for i in rm}
    frame=[j for j,r in enumerate(a['residuals']) if r['label']=='shared.frame_definition']
    require(len(frame)==1,'unique frame')
    removed=set(uses[ns['index_addition.D']])|set(uses[ns['pow6.quotient']])
    removed.add(next(j for j,r in enumerate(a['residuals']) if r['label']=='remainder_budget.ratio1'))
    require(len(removed)==3,'three removed rows')
    labels={'crt.range.'+s+'.quotient_multiple' for s in ['a','b','c','d','derived_label_sum']}
    changed=[j for j,r in enumerate(a['residuals']) if r['label'] in labels]
    require(len(changed)==5,'five tightened ranges')
    require(set(uses[ratio1])==set(changed)|{j for j in removed if a['residuals'][j]['label']=='remainder_budget.ratio1'},'ratio use completeness')
    keep=[i for i in range(len(a['variables'])) if i not in rm];rn={i:j for j,i in enumerate(keep)}
    out=[];orig=[];edits=[]
    for j,r in enumerate(rr):
        if j in removed:continue
        p=dict(r)
        if j==frame[0]:
            require(p.pop((p6,p6),None)==-1,'one discarded power-output square')
        if j in changed:p=subst(p,{ratio1:v(ratio0)})
        require(not any(i in rm for m in p for i in m),'no discarded variable retained')
        if p!=r:edits.append({'row':j,'old':a['residuals'][j],'new':dict(a['residuals'][j],terms=enc(p))})
        out.append(renumber(p,rn));orig.append(j)
    require(ss==out,'every strict-source coefficient')
    require(b['variables']==[a['variables'][i] for i in keep],'strict-source coordinate census')
    require(ct['removed_variables']==sorted(rm) and ct['removed_rows']==sorted(removed),'strict removal certificate')
    require(ct['edits']==edits and ct['old_to_new']==[[i,j] for i,j in rn.items()] and ct['row_origins']==orig,'strict exact edit certificate')
    return {'removed_coordinates':4,'removed_rows':3,'strict_ranges':5,'remaining_variables':len(keep)}

def basis_check(a,b,ct,reference):
    rr=rows(a);ss=rows(b);ns=names(a);ids={i:ns[z['name']] for i,z in enumerate(reference['variables']) if z['name'] in ns};ids[3]=ns['crt.growth_majorant_F']
    matches={j:unique(rr,renumber(dec(reference['residuals'][j]['terms']),ids)) for j in [54,65,67,68,69,70,72,73,74]}
    require(ct['matched_rows']==[[i,j] for i,j in matches.items()],'matched private-wire rows')
    require(ct['name_map']==[[i,j] for i,j in ids.items()],'literal inherited name map')
    n=len(a['variables']);rm={ids[i] for i in [83,84,85,89]};rmd={matches[j] for j in [67,68,70,73]}
    keep=[i for i in range(n+1) if i not in rm];rn={i:j for j,i in enumerate(keep)};inv={j:i for i,j in rn.items()}
    require(ct['removed_variables']==sorted(rm) and ct['removed_rows']==sorted(rmd),'private-wire removal census')
    require(ct['old_to_new']==[[i,j] for i,j in rn.items()],'private-wire renumbering')
    expectvars=copy.deepcopy(a['variables'])+[{'name':'horn.F_times_S','kind':'shared_product'}]
    expectvars[ids[81]]={'name':'horn.joint_square_sum','kind':'rank_aggregate'}
    require(b['variables']==[expectvars[i] for i in keep],'private-wire coordinate meaning')
    src=[renumber(p,inv) for p in ss];orig=[j for j in range(len(rr)) if j not in rmd]+[None]
    require(ct['row_origins']==orig,'private-wire row origins')
    byorigin=dict(zip(orig,src));J=v(n);F=v(ids[3]);S=v(ids[14]);Sp=v(ids[15]);aa=sub(v(ids[10]),c(1));bb=v(ids[11]);d=add(scale(6,v(ids[10])),scale(8,bb),scale(2,v(ids[21])))
    fw={ids[81]:add(v(ids[81]),v(ids[83])),n:mul(F,S)}
    rv={ids[81]:mul(v(ids[80]),v(ids[80])),ids[83]:sub(v(ids[81]),mul(v(ids[80]),v(ids[80]))),ids[84]:add(c(1),mul(F,bb)),ids[85]:add(c(1),mul(F,aa)),ids[89]:add(c(1),mul(F,d))}
    require(ct['forward']==[[i,enc(p)] for i,p in fw.items()] and ct['reverse']==[[i,enc(p)] for i,p in rv.items()],'polynomial restoration maps')
    require(byorigin[None]==sub(J,mul(F,S)),'new shared-product equation')
    for p,j in zip(src,orig):
        q=subst(p,fw)
        if j is None:target={}
        elif j==matches[65]:target=add(rr[j],rr[matches[67]])
        elif j==matches[69]:target=add(rr[j],mul(Sp,rr[matches[68]]),neg(mul(bb,rr[matches[54]])))
        elif j==matches[72]:target=add(rr[j],mul(S,rr[matches[70]]))
        elif j==matches[74]:target=add(rr[j],neg(mul(S,rr[matches[68]])),mul(Sp,rr[matches[73]]),neg(mul(d,rr[matches[54]])))
        else:target=rr[j]
        require(q==target,'private-wire forward ideal identity '+str(j))
    for j,p in enumerate(rr):
        q=subst(p,rv)
        if j in {matches[k] for k in [65,68,70,73]}:target={}
        elif j==matches[67]:target=byorigin[matches[65]]
        elif j==matches[69]:target=add(byorigin[j],mul(bb,rr[matches[54]]))
        elif j==matches[72]:target=add(byorigin[j],mul(aa,byorigin[None]))
        elif j==matches[74]:target=add(byorigin[j],neg(mul(bb,byorigin[None])),mul(d,rr[matches[54]]))
        else:target=byorigin[j]
        require(q==target,'private-wire reverse ideal identity '+str(j))
    return {'forward_residual_identities':len(src),'reverse_residual_identities':len(rr),'net_removed_coordinates':3}

PAIRS=[(0,'mul.460',0,0),(2,'mul.503',0,0),(3,'mul.529',-1,0),(5,'mul.554',0,0),(6,'mul.567',0,0),(7,'mul.580',0,0),(8,'mul.593',0,0),(9,'mul.606',0,0),(10,'mul.619',0,0),(11,'mul.632',0,0),(12,'mul.645',0,1),(13,'mul.658',0,0),(14,'mul.671',0,0),(15,'mul.684',0,0)]

def pool_check(a,b,ct):
    rr=rows(a);ss=rows(b);ns=names(a);n=len(a['variables'])
    def port(s,k=0):return add(v(ns[s]),c(k))
    A=port('shared.A',1);radix=port('pow2.output',-1)
    plus=[(3,2),(5,3),(7,5),(8,6),(9,7),(10,8),(12,10),(13,11),(15,13),(16,14),(17,15)]
    baseq=[(4,0),(11,9),(14,12)]
    pair={i:(s,ys,zs) for i,s,ys,zs in PAIRS};removed_vars=set();removed_rows=set();appended=[];varsnew=copy.deepcopy(a['variables']);gcounts=[]
    require(ct['frame_strengthened'] is False,'unchanged frame')
    require(len(ct['groups'])==2,'two fixed-base pools')
    for gi,(label,base,mname,members) in enumerate([('radix_plus_one',port('pow2.output'),'base3.T',plus),('radix',radix,'base4.T',baseq)]):
        gc=ct['groups'][gi];mi=ns[mname];T=add(scale(2,mul(A,base)),neg(mul(base,base)),c(-1));Tdef=sub(v(mi),T)
        hits=[j for j,r in enumerate(rr) if r in (Tdef,neg(Tdef))];require(len(hits)==1,'one modulus definition');tr=hits[0]
        removed_rows.add(tr);removed_vars.add(mi);H={};S={};Y2={};errors={};ay_error={};recs=[]
        for pno,ino in members:
            zn,ys,zs=pair[ino];X=port('index'+str(ino)+'.X',1);Y=port('index'+str(ino)+'.Y',ys);Z=port(zn,zs);m=port('pow'+str(pno)+'.output');qi=ns['pow'+str(pno)+'.quotient'];Q=v(qi)
            e=add(m,neg(X),Z,neg(mul(base,Y)))
            candidates=[j for j,r in enumerate(rr) if r in (add(e,mul(v(mi),Q)),sub(e,mul(v(mi),Q)),neg(add(e,mul(v(mi),Q))),neg(sub(e,mul(v(mi),Q))))]
            require(len(candidates)==1,'one actual power row');pr=candidates[0]
            AY=sub(Z,mul(A,Y));norm=add(mul(X,X),mul(Y,Y),neg(mul(Z,Z)),c(-1))
            ayhits=[j for j,r in enumerate(rr) if r in (AY,neg(AY))];nhits=[j for j,r in enumerate(rr) if r in (norm,neg(norm))]
            require(len(ayhits)==len(nhits)==1,'retained signed Pell norm and AY identities')
            removed_rows.add(pr);removed_vars.add(qi)
            H=add(H,mul(Y,sub(m,X)));D=add(m,neg(X),Z);S=add(S,mul(D,D),neg(mul(Y,Y)));Y2=add(Y2,mul(Y,Y));errors=add(errors,mul(e,e));ay_error=add(ay_error,scale(-2,mul(mul(base,Y),AY)))
            recs.append({'request':pno,'pair':ino,'output':enc(m),'X':enc(X),'Y':enc(Y),'Z':enc(Z),'removed_quotient':qi,'removed_row':pr,'retained_AY_row':ayhits[0],'retained_norm_row':nhits[0]})
        K=n+2*gi;L=K+1
        r1=add(v(K),scale(-2,H),neg(mul(sub(scale(2,A),base),v(L))))
        r2=add(S,neg(mul(base,v(K))),v(L))
        # Completing the squares independently verifies the pooled congruence identity.
        require(sub(errors,add(S,scale(-2,mul(base,H)),neg(mul(T,Y2))))==ay_error,'pooled completed-square identity')
        require(gc['group']==label and gc['requests']==recs and gc['norm_reduced'] is False,'exact pool membership and signs')
        for key,p in [('A',A),('base',base),('T',T),('H',H),('S',S),('sumY2',Y2)]:require(gc[key]==enc(p),'pool aggregate '+key)
        require(gc['new_K']==K and gc['new_L']==L and gc['modulus_row']==tr and gc['modulus_coordinate']==mi,'pool coordinate allocation')
        require([dec(z['terms']) for z in gc['new_rows']]==[r1,r2],'two certified pool rows')
        appended.extend([r1,r2]);varsnew.extend([{'kind':'pooled_power','name':label+'.K'},{'kind':'pooled_power','name':label+'.L'}]);gcounts.append(len(members))
    keep=[i for i in range(len(varsnew)) if i not in removed_vars];rn={i:j for j,i in enumerate(keep)}
    out=[r for j,r in enumerate(rr) if j not in removed_rows]+appended
    require(not any(i in removed_vars for r in out for m in r for i in m),'pooled quotient privacy')
    require(ss==[renumber(r,rn) for r in out],'every pooled polynomial coefficient')
    require(b['variables']==[varsnew[i] for i in keep],'pooled coordinate census')
    require(ct['removed_variables']==sorted(removed_vars) and ct['removed_rows']==sorted(removed_rows),'pooled removal certificate')
    require(ct['old_to_new']==[[i,j] for i,j in rn.items()],'pool renumbering')
    for f in ct['frame_edits']:require(f['old']==f['new'] and dec(f['old'])==rr[f['row']],'retained signed frame rows')
    return {'pooled_request_counts':gcounts,'retained_pell_norms':14,'net_removed_coordinates':12,'completed_square_identities':2}

def difference_check(a,b,ct):
    rr=rows(a);ss=rows(b);ns=names(a);mp={};normsum={};records=[];varsnew=copy.deepcopy(a['variables'])
    for ino,zn,ys,zs in PAIRS:
        xi=ns['index'+str(ino)+'.X'];yi=ns['index'+str(ino)+'.Y'];zi=ns[zn]
        X=add(v(xi),c(1));Y=add(v(yi),c(ys));Z=add(v(zi),c(zs));N=add(mul(X,X),mul(Y,Y),neg(mul(Z,Z)),c(-1))
        hits=[(j,1 if p==N else -1) for j,p in enumerate(rr) if p in (N,neg(N))];require(len(hits)==1,'one Pell norm before shear')
        records.append([ino,hits[0][0],hits[0][1]]);normsum=add(normsum,N);mp[xi]=add(v(xi),Z,c(-1));varsnew[xi]={'kind':'pell_difference','name':'index'+str(ino)+'.X_minus_AY'}
    qi=ns['cap.pooled_quotient'];hits=[j for j,r in enumerate(rr) if any(qi in m for m in r)];require(len(hits)==1,'one orientation pool row');j=hits[0]
    edited=list(rr);edited[j]=sub(rr[j],normsum);out=[subst(p,mp) for p in edited]
    inv={i:sub(scale(2,v(i)),p) for i,p in mp.items()}
    require(all(subst(q,inv)==p for p,q in zip(edited,out)),'all inverse affine shear identities')
    require(out==ss and b['variables']==varsnew,'all final difference coordinates and coefficients')
    require(ct['orientation_row']==j and ct['orientation_parent_terms']==enc(rr[j]) and ct['norm_subtractions']==records,'orientation row operation certificate')
    require(ct['old_in_new']==[[i,enc(p)] for i,p in mp.items()] and ct['new_in_old']==[[i,enc(p)] for i,p in inv.items()],'all fourteen exact unimodular Pell shears')
    return {'integer_affine_maps':len(mp),'inverse_row_identities':len(rr),'orientation_norm_subtractions':14}

def expansion_check(e,path):
    rr=rows(e);expected={}
    for p in rr:expected=add(expected,mul(p,p))
    artifact=read(path/'expanded_polynomial.json');require(dec(artifact['terms'])==expected,'every collected quartic coefficient')
    m={'variables':len(e['variables']),'rows':len(rr),'degree':max(map(len,expected)),'monomials':len(expected),'height':max(map(abs,expected.values())),'row_height':max(abs(c) for p in rr for c in p.values())}
    require(m==read(path/'METRICS.json'),'exact full metric tuple')
    require({i for mon in expected for i in mon}==set(range(len(e['variables']))),'all declared coordinates occur')
    return m

def run(root,controls=True):
    source=root/'157-linear-crt/source/equation.json';reference=root/'158-pooled-powers/inputs/parent245.json';d=root/'composed'
    # Authenticate source through its Git object id and exact byte count.
    sb=source.read_bytes();gitsha=hashlib.sha1(b'blob '+str(len(sb)).encode()+b'\0'+sb).hexdigest()
    require(gitsha=='0de72d57e14aca0c7ed0b97fc05676b6e5a63153' and len(sb)==30211,'pinned157 source bytes')
    require(sha(reference)=='1a42dd3a148c3084cd95a367869d251ed92e2f9852397215e4909e70b03d278e','pinned158 private-wire reference bytes')
    a=read(source);ref=read(reference)
    es=[read(d/s/'equation.json') for s in ['strict238','basis235','pooled223','differences223']]
    cs=[read(d/s/f) for s,f in [('strict238','strict_certificate.json'),('basis235','basis_certificate.json'),('pooled223','pool_certificate.json'),('differences223','shear_certificate.json')]]
    parentpaths=[source]+[d/s/'equation.json' for s in ['strict238','basis235','pooled223']]
    for i,ct in enumerate(cs):
        key='parent_sha256' if i<2 else 'parent_equation_sha256';require(ct[key]==sha(parentpaths[i]),'parent identity certificate '+str(i))
    r={'status':'passed','source157_git_blob_sha1':gitsha,'source157_sha256':sha(source),
       'strict':strict_check(a,es[0],cs[0]),'private_wires':basis_check(es[0],es[1],cs[1],ref),
       'pooling':pool_check(es[1],es[2],cs[2]),'pell_differences':difference_check(es[2],es[3],cs[3]),
       'frame':frame_check(d/'differences223/equation.json')}
    r['metrics']={s:expansion_check(e,d/s) for e,s in zip(es,['strict238','basis235','pooled223','differences223'])}
    r['negative_controls']=[]
    if controls:
        def rejection(label,fn):
            try:fn()
            except (ValueError,KeyError,IndexError):r['negative_controls'].append(label)
            else:raise ValueError('corruption not rejected: '+label)
        bad=copy.deepcopy(es[0]);bad['residuals'][0]['terms'][0][0]+=1
        rejection('changed strict-source coefficient',lambda:strict_check(a,bad,cs[0]))
        bc=copy.deepcopy(cs[1]);bc['reverse'][0][1][0][0]+=1
        rejection('changed private-wire reverse map',lambda:basis_check(es[0],es[1],bc,ref))
        badpool=copy.deepcopy(es[2]);badpool['residuals'][-1]['terms'][-1][0]*=-1
        rejection('changed pool quotient sign',lambda:pool_check(es[1],badpool,cs[2]))
        bp=copy.deepcopy(cs[2]);bp['groups'][0]['requests'].pop()
        rejection('omitted pooled request',lambda:pool_check(es[1],es[2],bp))
        bd=copy.deepcopy(cs[3]);bd['old_in_new'][0][1][0][0]+=1
        rejection('wrong Pell affine offset',lambda:difference_check(es[2],es[3],bd))
        bad=copy.deepcopy(es[3]);bad['residuals'][0]['terms'][0][0]=True
        rejection('boolean coefficient',lambda:rows(bad))
        badframe=copy.deepcopy(es[3]);fr=next(q for q in badframe['residuals'] if q['label']=='shared.frame_definition');fr['terms'][0][0]+=1
        rejection('changed actual square frame',lambda:frame_data_check(badframe))
    r['scope']='Independent finite polynomial, integer-map and squared-frame checks. No new end-to-end proof-assistant build; unbounded semantic proof and inherited C222 calibration are separate.'
    return r

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--receipt',type=Path);a=ap.parse_args();r=run(a.root);s=json.dumps(r,indent=2,sort_keys=True)+'\n'
    if a.receipt:a.receipt.write_text(s)
    print(json.dumps({k:v for k,v in r.items() if k!='frame'},indent=2))
