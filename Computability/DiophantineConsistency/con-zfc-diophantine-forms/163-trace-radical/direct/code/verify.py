#!/usr/bin/env python3
"""Independent exact checker for the new direct quartics (stdlib only).

New polynomial arithmetic uses exponent dictionaries, not the producer's
repeated-index arithmetic.  No new producer or optimizer is imported.
"""
from pathlib import Path
from collections import Counter
import argparse,copy,hashlib,importlib.util,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent.parent

def need(ok,msg):
    if not ok:raise ValueError(msg)
def read(p):return json.loads(p.read_text())
def poly(terms):
    ans={}
    for c,m in terms:
        need(type(c)is int and all(type(v)is int and v>=0 for v in m),'integer sparse terms')
        key=tuple(sorted(Counter(m).items()));ans[key]=ans.get(key,0)+c
    return {m:c for m,c in ans.items() if c}
def add(a,b,k=1):
    out=a.copy()
    for m,c in b.items():out[m]=out.get(m,0)+k*c
    return {m:c for m,c in out.items() if c}
def times(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            ex=dict(m)
            for i,p in n:ex[i]=ex.get(i,0)+p
            key=tuple(sorted(ex.items()));out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}
def variable(v):return {((v,1),):1}
def sub(p,v,q):
    out={}
    for m,c in p.items():
        rest={i:d for i,d in m};power=rest.pop(v,0)
        term={tuple(sorted(rest.items())):c}
        for _ in range(power):term=times(term,q)
        out=add(out,term)
    return out
def degree(p):return max((sum(e for _,e in m) for m in p),default=0)
def rename(p,ren):return {tuple(sorted((ren[i],e) for i,e in m)):c for m,c in p.items()}
def hessian_rows(rows):
    answer=[]
    for r,p in enumerate(rows):
        h={}
        for m,c in p.items():
            if sum(e for _,e in m)!=2:continue
            if len(m)==1:
                i=m[0][0];h.setdefault(i,{})[i]=2*c
            else:
                i,j=m[0][0],m[1][0];h.setdefault(i,{})[j]=c;h.setdefault(j,{})[i]=c
        answer.extend(((r,i),a) for i,a in sorted(h.items()))
    return answer

def modular_rank(rows,n,prime=101):
    piv={};source=[]
    for ident,a in hessian_rows(rows):
        a={j:c%prime for j,c in a.items() if c%prime}
        while a:
            col=min(a)
            if col not in piv:
                u=pow(a[col],-1,prime);piv[col]={j:c*u%prime for j,c in a.items()}
                source.append(list(ident));break
            k=a[col]
            a={j:c%prime for j,c in add(a,piv[col],-k).items() if c%prime}
    return {'prime':prime,'rank':len(piv),'columns':n,'pivot_source_rows':source}

def replay(source,steps):
    rows=[poly(r['terms']) for r in source['residuals']]
    variables=source['variables']
    for number,st in enumerate(steps):
        n=len(variables);v=st['pivot_variable'];r=st['pivot_row']
        need([a['name'] for a in variables]==st['variables_before'],'stage variable identities')
        d=dict(st['direction']);need(all(type(i)is int and 0<=i<n and type(c)is int for i,c in d.items()),'integer direction')
        need(d.get(v)==1,'unit pivot direction')
        need(variables[v]['name']==st['pivot_name'],'pivot name')
        for ident,h in hessian_rows(rows):need(sum(c*d.get(i,0) for i,c in h.items())==0,'common Hessian radical')
        slope=sum(rows[r].get(((i,1),),0)*c for i,c in d.items())
        need(abs(slope)==1,'unit row slope')
        expected=[[w,v,c] for w,c in sorted(d.items()) if w!=v]
        need(st['shears']==expected,'exact triangular shear recipe')
        for w,_,c in expected:
            q=add(variable(w),variable(v),c)
            inv=add(variable(w),variable(v),-c)
            need(sub(q,w,inv)==variable(w),'symbolic inverse of coordinate shear')
            rows=[sub(p,w,q) for p in rows]
        need(all(all(i!=v or (len(m)==1 and e==1) for i,e in m) for p in rows for m in p),'pivot occurs only linearly')
        f=poly(st['restoration']);need(degree(f)<=2 and all(i!=v for m in f for i,e in m),'quadratic acyclic restoration')
        want=add(variable(v),f,-1)
        need(rows[r]==want or rows[r]=={m:-c for m,c in want.items()},'exact monic defining residual')
        transformed=[sub(p,v,f) for j,p in enumerate(rows) if j!=r]
        need(all(degree(p)<=2 for p in transformed),'degree-preserving substitution')
        keep=[i for i in range(n) if i!=v]
        need(st['retained_variables']==keep,'only the pivot is removed')
        need(all(transformed),'no unexplained row deletion')
        ren={i:j for j,i in enumerate(keep)}
        rows=[rename(p,ren) for p in transformed];variables=[variables[i] for i in keep]
    return variables,rows

SOURCES={
 'self_power235':'lineage/self_power/affine241/equation.json',
 'self_power236':'lineage/self_power/affine242/equation.json',
 'shared_error234':'inherited/shared_error/equations/equation240/equation.json',
}
def check_endpoint(name,steps_override=None,eq_override=None,expanded_override=None):
    folder=ROOT/'equations'/name
    src=read(ROOT/SOURCES[name]);steps=steps_override if steps_override is not None else read(folder/'certificate.json')
    variables,rows=replay(src,steps)
    eq=eq_override if eq_override is not None else read(folder/'equation.json')
    need(eq['domain']=='unrestricted integers','integer domain')
    need(eq['variables']==variables,'complete endpoint coordinates')
    need([poly(r['terms']) for r in eq['residuals']]==rows,'complete endpoint residuals')
    collected={}
    for row in rows:collected=add(collected,times(row,row))
    expanded=expanded_override if expanded_override is not None else read(folder/'expanded_polynomial.json')
    need(poly(expanded['terms'])==collected,'every collected quartic coefficient')
    need({i for m in collected for i,e in m}==set(range(len(variables))),'all coordinates occur')
    metrics={'variables':len(variables),'rows':len(rows),'degree':degree(collected),'terms':len(collected),'height':max(abs(c) for c in collected.values())}
    need(read(folder/'METRICS.json')==metrics,'exact endpoint metrics')
    rank=modular_rank(rows,len(variables));need(rank['rank']==len(variables),'terminal common Hessian rank')
    need(read(folder/'common_radical_rank.json')==rank,'exact finite rank certificate')
    return dict(metrics=metrics,radical_projections=len(steps),terminal_hessian_rank=rank['rank'],rank_prime=rank['prime'])

def check_source_chain():
    base=ROOT/'inherited/factorial_free/direct'
    spec=importlib.util.spec_from_file_location('inherited_independent_factorial_free_checker',base/'check_factorial_free.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    old_folder=base/'factorial_free_affine';old=mod.source_check(old_folder)
    folder=ROOT/'lineage/self_power';new=read(folder/'raw_source.json');edit=read(folder/'source_edit.json')
    row=edit['row'];names={v['name']:i for i,v in enumerate(old['variables'])}
    need(old['residuals'][row]==edit['old'],'old growth row identity')
    need(old['residuals'][row]['label']=='growth.base_definition','growth relation target')
    t,d=names['t0'],names['growth.power_base']
    expected=add(variable(d),variable(t),-1);expected=add(expected,{():-16})
    need(poly(edit['new']['terms'])==expected,'new base is actual t=t0+16')
    want=copy.deepcopy(old);want['residuals'][row]=edit['new'];want['variant']='self_power_t_to_t'
    need(new==want,'only the authenticated growth-base relation changes')
    result={'exact_source_edit':True,'projection':mod.projection_check(folder,new)}
    source=read(folder/'equation.json')
    result['affine235']=mod.affine_check(source,folder/'affine241')
    result['affine236']=mod.affine_check(source,folder/'affine242')
    return result

def run_inherited():
    commands=[
      ('factorial_free_parent',ROOT/'inherited/factorial_free/direct/parent','code/verify.py',[]),
      ('factorial_free_source',ROOT/'inherited/factorial_free/direct','check_factorial_free.py',['--affine-only','--skip-parent']),
      ('shared_error_core',ROOT/'inherited/shared_error/equations','verify_unified_bootstrap.py',['--affine-radix']),
      ('shared_error_source240',ROOT/'inherited/shared_error/equations','verify_affine.py',['--profile','equation240']),
    ]
    out={}
    for name,cwd,script,args in commands:
        flags=['-B']+(['-O'] if sys.flags.optimize else [])
        proc=subprocess.run([sys.executable,*flags,script,*args],cwd=cwd,text=True,capture_output=True)
        need(proc.returncode==0,'inherited checker '+name+' failed: '+proc.stdout+' '+proc.stderr)
        out[name]={'status':'PASS','stdout_sha256':hashlib.sha256(proc.stdout.encode()).hexdigest()}
    return out

def controls():
    name='self_power235';f=ROOT/'equations'/name
    tests=[]
    a=read(f/'certificate.json');a[0]['direction'][0][1]+=1;tests.append(('direction',dict(steps_override=a)))
    a=read(f/'certificate.json');a[0]['restoration'][0][0]+=1;tests.append(('restoration',dict(steps_override=a)))
    a=read(f/'certificate.json');a[0]['retained_variables']=a[0]['retained_variables'][1:];tests.append(('coordinate deletion',dict(steps_override=a)))
    a=read(f/'equation.json');a['residuals'][0]['terms'][0][0]+=1;tests.append(('endpoint residual',dict(eq_override=a)))
    a=read(f/'expanded_polynomial.json');a['terms'][0][0]+=1;tests.append(('quartic coefficient',dict(expanded_override=a)))
    rejected=[]
    for label,kw in tests:
        try:check_endpoint(name,**kw)
        except ValueError:rejected.append(label)
        else:raise ValueError('accepted corruption: '+label)
    return rejected

def main():
    a=argparse.ArgumentParser();a.add_argument('--full',action='store_true');a.add_argument('--receipt',type=Path);args=a.parse_args();start=time.monotonic()
    result={'status':'PASS','optimized':bool(sys.flags.optimize),'self_power_source_chain':check_source_chain()}
    result['endpoints']={n:check_endpoint(n) for n in SOURCES}
    result['rejected_controls']=controls()
    if args.full:result['inherited_checks']=run_inherited()
    result['seconds']=round(time.monotonic()-start,3)
    result['scope']='Exact polynomial identities, reversible coordinate maps, literal source edit, complete coefficients, and finite Hessian-rank certificates. The unbounded semantic theorem is proved separately; no fresh proof-assistant calibration is claimed.'
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
