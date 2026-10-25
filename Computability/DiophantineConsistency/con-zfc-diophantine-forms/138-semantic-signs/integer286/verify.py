#!/usr/bin/env python3
"""Offline exact verification; finite checks do not prove Con(ZFC)."""
from pathlib import Path
import argparse, contextlib, copy, hashlib, io, json, math, sys, tempfile
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'vendor'))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T
from build import build
from center_integer import center

def need(p,m):
    if not p:raise ValueError(m)
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def digest(x):return hashlib.sha256(E.canonical_bytes(x)).hexdigest()
def mul(p,q):
    d={}
    for a,c in p.items():
        for b,e in q.items():
            k=tuple(sorted(a+b));d[k]=d.get(k,0)+c*e
    return {m:c for m,c in d.items() if c}
def add(*ps):
    d={}
    for p in ps:
        for m,c in p.items():d[m]=d.get(m,0)+c
    return {m:c for m,c in d.items() if c}
def scale(p,k):return {m:k*c for m,c in p.items() if k*c}
def v(i):return {(i,):1}

def literal_source_check():
    parent=read(ROOT/'input/source.json');pc=read(ROOT/'input/transform_certificate.json')
    need(digest(parent)=='110c68baefdd955bd5af9af44564e81b9a43a08a088a3424c913bc185178a845','pinned parent source')
    need(digest(pc)=='f0740929667f2e2f88ab8e921a45aee5890de0999676dad877e5b820fb0e2ebf','pinned parent transformation')
    source=read(ROOT/'principal/source.json');cert=read(ROOT/'principal/transform_certificate.json')
    names={m['name']:i for i,m in enumerate(source['variables'])}
    W,A=names['shared.W'],names['shared.A'];C=names['cap.Y'];J=names['cap.J'];e=names['cap.e']
    Y2=names['cap.Y2'];q=names['pow2.output'];B=names['choose0.output'];V=names['pow0.output']
    frame=v(W)
    frame=add(frame,{():-2})
    for a in pc['square_budget']['atoms']:
        atom=E.normalize(a['affine']);frame=add(frame,scale(mul(atom,atom),-2))
    pooled=scale(mul(add(v(A),{():-1}),v(pc['pooled_quotient'])),-1)
    for sd in pc['seed_data']:
        x,y=sd['pair'];delta=add(v(y),scale(E.normalize(sd['exponent']),-1))
        pooled=add(pooled,mul(delta,delta),mul(add(v(x),{():-1}),add(v(x),{():-1})))
    reps=[names[n] for n in ('crt.encoded.a','crt.encoded.b','crt.encoded.c','crt.encoded.d','crt.encoded.S','crt.encoded.Sp','crt.encoded.u','crt.encoded.vq','crt.encoded_index_minus_one')]
    H=add({():21},*[{(i,):2} for i in reps])
    expected={
        'shared.frame_definition':frame,
        'cap.common_multiple':add(v(J),scale(mul(v(Y2),add(scale(v(e),2),{():1})),-2)),
        'cap.pooled_index_residue':pooled,
        'self_radix.base_definition':add(v(names['self_radix.BH']),scale(mul(v(B),H),-1)),
        'cofinal.beta_base':add(v(names['y']),scale(v(V),-1),{():1})}
    seen=set()
    for i,old in enumerate(parent['residuals']):
        new=source['residuals'][i];need(new['label']==old['label'],'row-order preservation')
        if old['label'] in expected:
            need(E.normalize(new['terms'])==expected[old['label']],old['label']);seen.add(old['label'])
        else:need(new==old,'unlisted mutation at row '+str(i))
    need(seen==set(expected),'missing source mutation')
    need(len(source['variables'])==len(parent['variables'])+2,'exactly two new signed coordinates')
    need(source['variables'][:len(parent['variables'])]==parent['variables'],'old coordinate metadata unchanged')
    need(len(source['residuals'])==len(parent['residuals'])+2,'exactly two appended rows')
    aa=names['even_frame.half_abscissa'];rr=names['odd_radix.half_root']
    need(E.normalize(source['residuals'][-2]['terms'])==add(v(A),{(aa,aa):-2,():1}),'doubled abscissa row')
    need(E.normalize(source['residuals'][-1]['terms'])==add(v(q),{(rr,rr):-4,(rr,):-4,():-1}),'odd-square radix row')
    need(cert['new_source_sha256']==digest(source),'new source binding')
    actual_ledger=[]
    for i,call in zip(reps,[5,7,8,9,10,12,13,15,16]):
        p=pc['square_budget']['power_calls'][call]
        need(E.normalize(p['base'])==add(v(q),{():1}),'representative request base')
        need(E.normalize(p['exponent'])==add(v(i),{():1}),'representative request index')
        actual_ledger.append({'call':call,'stored_coordinate':source['variables'][i]['name'],'base':'q+1','exponent':'stored coordinate + 1'})
    px=pc['square_budget']['power_calls'][14]
    need(E.normalize(px['base'])==v(q),'x+1 base')
    need(E.normalize(px['exponent'])==add(v(names['x']),{():1}),'x+1 index')
    remove=set(reps+[A,names['x'],names['choose0.oslack']])
    expected_guards=[]
    for g in pc['guards']:
        if g.get('coordinate') in remove or g['kind']=='anchor_common_multiplier':continue
        expected_guards.append({k:v for k,v in g.items() if k not in ('auxiliary','row')})
    need(len(expected_guards)==14,'fourteen semantic guards')
    need(expected_guards==[{k:v for k,v in g.items() if k not in ('auxiliary','row')} for g in cert['guards']],'exact retained guards')
    guarded=read(ROOT/'principal/guarded.json');literal=copy.deepcopy(source)
    for j,g in enumerate(cert['guards']):
        a,b,c=range(len(literal['variables']),len(literal['variables'])+3)
        literal['variables'] += [{'name':f'guard{j}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        p=add(E.normalize(g['expression']),{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})
        literal['residuals'].append({'label':f'domain_guard.{j}','terms':E.as_terms(p)})
        need(g['auxiliary']==[a,b,c] and g['row']==len(literal['residuals'])-1,'guard witness indices')
    need(literal['variables']==guarded['variables'] and literal['residuals']==guarded['residuals'],'exact quadratic guard insertion')
    return {'source_hash':digest(source),'modified_rows':sorted(expected),'guard_count':14,'representative_power_ledger':actual_ledger}

def endpoint_check(folder):
    guarded=read(folder/'guarded.json');factored=read(folder/'factored_source.json');fc=read(folder/'factorization_certificate.json')
    actual,ac=F.transform(guarded)
    need(E.canonical_bytes(actual)==E.canonical_bytes(factored) and E.canonical_bytes(ac)==E.canonical_bytes(fc),'exact Horn factorization and certificate')
    projected=read(folder/'projected.json');proj=read(folder/'projection_certificate.json')
    replay=E.verify(factored,projected,proj)
    eq=read(folder/'equation.json');tr=read(folder/'translation_certificate.json')
    need(digest(projected)==tr['input_sha256'] and digest(eq)==tr['output_sha256'],'first translation hashes')
    translated=T.translate(projected,dict(tr['shifts']))
    need(translated==eq,'first integral translation')
    centered=folder/'centered';ceq=read(centered/'equation.json');ctr=read(centered/'translation_certificate.json')
    need(digest(projected)==ctr['input_sha256'] and digest(ceq)==ctr['output_sha256'],'centered translation hashes')
    ctrans=T.translate(projected,dict(ctr['shifts']))
    need(ctrans['residuals']==ceq['residuals'] and ctrans['variables']==ceq['variables'],'composed integral translation')
    need(ceq['domain']=='unrestricted integers','unrestricted integer domain')
    total={}
    for row in ceq['residuals']:
        p=E.normalize(row['terms']);need(max(map(len,p),default=0)<=2,'quadratic residual')
        need(all(isinstance(c,int) and all(isinstance(i,int) and 0<=i<len(ceq['variables']) for i in m) for m,c in p.items()),'literal integer coefficient and coordinate range')
        total=add(total,mul(p,p))
    expanded=read(centered/'expanded_polynomial.json')
    need(E.normalize(expanded['terms'])==total,'independent complete sum-of-squares expansion')
    actual_metrics={'variables':len(ceq['variables']),'rows':len(ceq['residuals']),'degree':max(map(len,total)),'monomials':len(total),'height':max(map(abs,total.values())),'row_height':max(abs(c) for r in ceq['residuals'] for c,m in r['terms'])}
    need(actual_metrics==read(centered/'METRICS.json'),'exact centered census')
    return {'metrics':actual_metrics,'projection':replay,'equation_sha256':sha(centered/'equation.json'),'polynomial_sha256':sha(centered/'expanded_polynomial.json')}

def pell(b,n,mod=None):
    ans=(1,0);x=(b,1);D=b*b-1
    def times(a,c):
        z=(a[0]*c[0]+D*a[1]*c[1],a[0]*c[1]+a[1]*c[0])
        return tuple(t%mod for t in z) if mod else z
    while n:
        if n&1:ans=times(ans,x)
        x=times(x,x);n//=2
    return ans

def arithmetic_regressions():
    count=0
    for A in range(3,20,2):
        for i in range(1,13):
            U,C=pell(A,i);l=2*i*C
            H,J=pell(A,l,4*C*C)
            need(J==2*C*C,'odd common quotient modular regression')
            need(H%2==1,'odd common abscissa regression');count+=1
    for W in range(2,30,2):
        A,Y=pell(W+1,W);half,_=pell(W+1,W//2)
        need(A==2*half*half-1 and Y%W==0 and (Y//W)%2==1,'even frame regression')
    for t in range(16,30):
        F=math.factorial(t);V=(F*F+1)**t;y=V-1
        need(((t+1)*F)**(t+1)<F**(2*t)<=y,'linear cofinal accumulator regression')
        need(y%F==0 and y>=F+1,'linear cofinal modulus regression')
    return {'odd_anchor_modular_samples':count,'even_frame_samples':14,'cofinal_samples':14,'scope':'Finite regressions only; the unbounded proof is PROOF.md and PROOF_ORIENTED.md.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--rebuild',action='store_true');p.add_argument('--receipt',type=Path);a=p.parse_args()
    provenance=read(ROOT/'SOURCE_PROVENANCE.json')
    for item in provenance['files']:
        need(sha(ROOT/item['path'])==item['sha256'],'retained source hash '+item['path'])
    result={'status':'PASS','source':literal_source_check(),'principal':endpoint_check(ROOT/'principal'),'parity_companion':endpoint_check(ROOT/'generated'),'arithmetic':arithmetic_regressions(),'retained_source_files':len(provenance['files']),'rebuild':False,'optimized_python':bool(sys.flags.optimize)}
    need(result['principal']['metrics']=={'variables':286,'rows':196,'degree':4,'monomials':6607,'height':128446,'row_height':256},'principal claimed census')
    need(result['parity_companion']['metrics']=={'variables':319,'rows':207,'degree':4,'monomials':5779,'height':128446,'row_height':256},'parity claimed census')
    if a.rebuild:
        with tempfile.TemporaryDirectory(prefix='conzfc-semantic-signs-') as tmp:
            target=Path(tmp)
            for name,opts in [('principal',{'orient':True,'odd_radix':True,'linear_cofinal':True}),('generated',{})]:
                d=target/name
                with contextlib.redirect_stdout(io.StringIO()):
                    build(d,**opts);center(d,d/'centered')
                selected=['source.json','guarded.json','transform_certificate.json','factored_source.json','factorization_certificate.json','projected.json','projection_certificate.json','translation_certificate.json','METRICS.json','equation.json','expanded_polynomial.json','centered/equation.json','centered/expanded_polynomial.json','centered/translation_certificate.json','centered/METRICS.json']
                for f in selected:need((d/f).read_bytes()==(ROOT/name/f).read_bytes(),'exact rebuild '+name+'/'+f)
            result['rebuild']=True
    if a.receipt:a.receipt.write_bytes(E.canonical_bytes(result))
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
