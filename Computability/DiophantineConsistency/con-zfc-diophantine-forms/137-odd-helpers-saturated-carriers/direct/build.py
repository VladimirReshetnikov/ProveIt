#!/usr/bin/env python3
"""Local finite odd-helper/cofinal composition; reviewed standard-library closure."""
import argparse,copy,hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE/'vendor'))
import terminal_elimination as E
import factor_horn as F

def need(p,m):
    if not p:raise ValueError(m)
def read(p):return json.loads(p.read_bytes())
def put(p,d):p.write_bytes(E.canonical_bytes(d))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(*polys):
    r={}
    for p in polys:
        for m,c in p.items():r[m]=r.get(m,0)+c
    return {m:c for m,c in r.items() if c}
def row(label,p):return {'label':label,'terms':E.as_terms(p)}
def transform(cofinal_y=False,self_radix=False):
    src=read(HERE/'source/source.json');domain=read(HERE/'source/domain.json');eq=copy.deepcopy(src)
    need(len(eq['variables'])==406 and len(eq['residuals'])==341,'whole fused-nine source dimensions')
    edits=[]
    def replace(i,p):
        edits.append({'row':i,'old':eq['residuals'][i],'new':row(eq['residuals'][i]['label'],p)})
        eq['residuals'][i]=edits[-1]['new']
    p=E.normalize(eq['residuals'][202]['terms']);need(p[(245,247)]==-1,'frame multiplier');p[(245,247)]=-2;replace(202,p)
    p=E.normalize(eq['residuals'][322]['terms']);need(p[(375,389)]==-1,'helper multiplier');p[(375,389)]=-2;replace(322,p)
    if cofinal_y:
        # Keep r0=y-F-1 in row7, but supply its sign independently of the strict product.
        eq['residuals'].append(row('cofinal.beta_modulus',{(2,):1,(6,6):-1,(6,):1}))
    if self_radix:
        need(cofinal_y,'self-radix sibling requires cofinal y')
        # v178 is now the sum of the nine positive representatives;
        # the former private slack v174 becomes the actual base B*(1+v178).
        p=E.normalize(eq['residuals'][161]['terms']);need(p[(174,)]==-1,'old aggregate slack');del p[(174,)];replace(161,p)
        replace(162,{(174,):1,(5,):-1,(5,178):-1})
        eq['variables'][174]={'name':'self_radix.base','kind':'gate'}
        replace(158,{(175,):1,(174,174):-1})
        for rid in (235,237):
            p=E.normalize(eq['residuals'][rid]['terms']);p={tuple(sorted(174 if v==26 else v for v in m)):c for m,c in p.items()};replace(rid,p)
        p=E.normalize(eq['residuals'][333]['terms']);need((174,174) not in p,'new distinct frame atom');p[(174,174)]=-2;replace(333,p)
    removed=[];kept=[];newgraphs=[]
    pairtargets={183,184,191,192}|({213,214} if cofinal_y else set())
    for g in domain['guards']:
        if g['kind']=='cap_square_bound':continue
        if g.get('coordinate') in pairtargets or g.get('coordinate')==247 or g['kind']=='comparison_base_lower' or (self_radix and g.get('coordinate')==174):
            removed.append(g);continue
        expr=E.normalize(g['expression'])
        if g.get('coordinate')==0:
            aux=[len(eq['variables'])];eq['variables'].append({'name':'cofinal.horizon','kind':'integer_guard'})
            equation=add(expr,{(aux[0],aux[0]):-1});label='cofinal.square_horizon'
        else:
            if cofinal_y and g['kind']=='strict_fused_index_endpoint_product':expr={():-1,(405,):1}
            aux=list(range(len(eq['variables']),len(eq['variables'])+3))
            eq['variables'] += [{'name':'retained.'+str(g['row'])+'.'+c,'kind':'integer_guard'} for c in 'abc']
            a,b,c=aux;equation=add(expr,{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1});label='guard.from.'+str(g['row'])
        rid=len(eq['residuals']);eq['residuals'].append(row(label,equation));kept.append({'old':g,'new_row':rid,'new_auxiliary':aux,'expression':E.as_terms(expr)})
    pairs=[(183,184),(191,192)]+([(213,214)] if cofinal_y else [])
    for u,v in pairs:
        aux=list(range(len(eq['variables']),len(eq['variables'])+3));eq['variables'] += [{'name':f'support.{u}.{v}.'+c,'kind':'integer_guard'} for c in 'abc']
        a,b,c=aux;rid=len(eq['residuals']);eq['residuals'].append(row(f'support_product.{u}.{v}',{(u,v):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}))
        newgraphs.append({'pair':[u,v],'row':rid,'auxiliary':aux})
    eq['variant']='round17_odd_helper_self_radix' if self_radix else ('round17_odd_helper_cofinal_y' if cofinal_y else 'round17_odd_helper_cofinal_t')
    eq['ordinary_manifest_sha256']='See SOURCE_BINDING.json and PROOF.md; inherited seal is not a seal of this modified equation.'
    eq.pop('metrics',None)
    cert={'schema':'round17_signed_odd_helper_transform_v1','input_body_sha256':sha(HERE/'source/source.json'),'input_guarded_sha256':sha(HERE/'source/guarded.json'),'cofinal_y':cofinal_y,'self_radix':self_radix,'body_edits':edits,'removed_graphs':removed,'retained_graphs':kept,'new_product_graphs':newgraphs,'original_body_coordinates':406,'original_body_rows':341,'new_body_rows':342 if cofinal_y else 341,'odd_frame':True,'odd_helper':True,'cofinal_square_horizon':True}
    return eq,cert

def translate(eq,shifts):
    out=copy.deepcopy(eq)
    for r in out['residuals']:
        p=E.normalize(r['terms'])
        for i,s in sorted(shifts.items()):p=E.substitute(p,i,{(i,):1,():s})
        r['terms']=E.as_terms(p)
    return out
def census(eq,poly):
    return {'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(map(lambda x:len(x[1]),poly['terms'])),'monomials':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms']),'row_height':max(abs(c) for r in eq['residuals'] for c,m in r['terms'])}
def build(out,cofinal_y=False,self_radix=False,max_support=16,quadratic_first=False):
    for n,h in read(HERE/'SOURCE_PINS.json')['files'].items():
        need('__pycache__' not in Path(n).parts and Path(n).suffix not in ('.pyc','.pyo'),'cache is not a source dependency '+n)
        need(sha(HERE/n)==h,'source pin '+n)
    eq,tc=transform(cofinal_y,self_radix);factored,fc=F.transform(eq)
    projected,pc,metrics=E.optimize(factored,max_support=max_support,quadratic_first=quadratic_first);receipt=E.verify(factored,projected,pc)
    shifts={i:(-16 if v['name']=='t0' else -1) for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'] in ('t0','M0') or v['name'].endswith('minus1')}
    final=translate(projected,shifts);final.pop('metrics',None);poly=E.expand(final)
    out.mkdir(parents=True,exist_ok=True)
    artifacts={'raw_equation.json':eq,'transformation_certificate.json':tc,'factored_source.json':factored,'factorization_certificate.json':fc,'projected.json':projected,'projection_certificate.json':pc,'terminal_elimination_certificate.json':pc,'equation.json':final,'expanded_polynomial.json':poly,'translation_certificate.json':{'convention':'old=new+shift','shifts':[[i,s] for i,s in shifts.items()]},'METRICS.json':census(final,poly),'ENGINE.json':metrics|receipt}
    artifacts['SOURCE_BINDING.json']=read(HERE/'SOURCE_BINDING.json')
    for n,v in artifacts.items():put(out/n,v)
    print(json.dumps(artifacts['METRICS.json'],indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('--cofinal-y',action='store_true');p.add_argument('--self-radix',action='store_true');p.add_argument('--max-support',type=int,default=16);p.add_argument('--quadratic-first',action='store_true');a=p.parse_args();build(a.output,a.cofinal_y or a.self_radix,a.self_radix,a.max_support,a.quadratic_first)
