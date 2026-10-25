#!/usr/bin/env python3
"""Offline verification of the complete delivered equations and printed rows.

Finite identities authenticate the artifact. They do not decide Con(ZFC).
The unbounded arguments and inherited calibration are documented separately.
"""
from pathlib import Path
from collections import defaultdict
import argparse, hashlib, json, re, subprocess, sys

ROOT=Path(__file__).resolve().parent
PROFILES={'P258':'odd_three_pools_centered','P261':'four_pools_centered'}
EXPECTED={'P258':(258,186,4,5319,47281,128),'P261':(261,185,4,5332,47281,128)}

def need(value,message):
    if not value:raise ValueError(message)
def read(p):return json.loads(p.read_text())
def poly(ts):
    out={}
    for c,m in ts:
        need(type(c) is int and c!=0,'invalid coefficient')
        need(all(type(i) is int and i>=0 for i in m),'invalid monomial')
        m=tuple(m);need(m==tuple(sorted(m)) and m not in out,'noncanonical monomial')
        out[m]=c
    return out
def add(a,b,k):
    c=dict(a)
    for m,v in b.items():
        c[m]=c.get(m,0)+k*v
        if not c[m]:del c[m]
    return c
def expansion(rows):
    out=defaultdict(int)
    for r in rows:
        ts=list(r.items())
        for i,(m,c) in enumerate(ts):
            for j in range(i,len(ts)):
                n,d=ts[j];out[tuple(sorted(m+n))]+=(1 if i==j else 2)*c*d
    return {m:c for m,c in out.items() if c}

def parse_printed(text):
    matches=re.findall(r'\\begin\{aligned\}\s*r_\{(\d+)\}&=(.*?)\\end\{aligned\}',text,re.S)
    rows=[]
    for number,raw in matches:
        need(int(number)==len(rows),'printed row order')
        expression=raw.replace('\\\\','').replace('&{}','')
        expression=''.join(expression.split())
        out={}
        for t in re.findall(r'[+-]?[^+-]+',expression):
            sign=-1 if t.startswith('-') else 1
            t=t.lstrip('+-');mons=[]
            for m in re.finditer(r'x_\{(\d+)\}(?:\^\{(\d+)\})?',t):
                mons.extend([int(m.group(1))]*int(m.group(2) or '1'))
            rest=re.sub(r'x_\{\d+\}(?:\^\{\d+\})?','',t)
            need(rest=='' or rest.isdigit(),'unsupported printed term '+t)
            c=sign*int(rest or '1');key=tuple(sorted(mons))
            out[key]=out.get(key,0)+c
        rows.append({m:c for m,c in out.items() if c})
    return rows

def check_final(name,profile):
    basepath=ROOT/'direct'/profile/'equation.json';base=read(basepath)
    p=ROOT/'equations'/name;eq=read(p/'equation.json')
    need(eq['domain']=='unrestricted integers','wrong final domain')
    need(eq['variables']==base['variables'],'coordinate list changed')
    need(eq['row_reduction_source_sha256']==hashlib.sha256(basepath.read_bytes()).hexdigest(),'row source hash')
    old=[poly(r['terms']) for r in base['residuals']]
    target=[poly(r['terms']) for r in eq['residuals']]
    changed=[dict(r) for r in old];ops=read(p/'row_operations.json')
    need(len(ops)==30,'wrong row operation count')
    for i,j,k in ops:
        need(i!=j and 0<=i<len(old) and 0<=j<len(old) and type(k) is int,'bad row operation')
        changed[i]=add(changed[i],changed[j],k)
    need(changed==target,'row transform mismatch')
    for i,j,k in reversed(ops):changed[i]=add(changed[i],changed[j],-k)
    need(changed==old,'inverse row transform mismatch')
    need(all(len(m)<=2 for r in target for m in r),'nonquadratic residual')
    pfull=expansion(target);literal=poly(read(p/'expanded_polynomial.json')['terms'])
    need(pfull==literal,'collected polynomial mismatch')
    printed=parse_printed((p/'residuals.tex').read_text())
    need(printed==target,'printed equation differs from JSON')
    used={i for m in pfull for i in m};need(used==set(range(len(eq['variables']))),'unused or undefined coordinate')
    measured=(len(eq['variables']),len(target),max(map(len,pfull)),len(pfull),max(map(abs,pfull.values())),max(abs(c) for r in target for c in r.values()))
    need(measured==EXPECTED[name],'final metric mismatch')
    need(pfull.get((10,10,12,12))==47281,'height witness mismatch')
    if name=='P258':need(pfull.get((0,0,0,0))==13,'quartic witness mismatch')
    declared=read(p/'METRICS.json')
    need(tuple(declared[k] for k in ['variables','residuals','degree','monomials','height','row_height'])==measured,'declared metrics')
    # A changed coefficient must fail an actual equality, not only a hash.
    corrupt=dict(literal);corrupt[()]=corrupt.get((),0)+1
    need(corrupt!=expansion(target),'corruption was not distinguished')
    altered_tex=(p/'residuals.tex').read_text().replace('r_{0}&=','r_{0}&=1+',1)
    need(parse_printed(altered_tex)!=target,'printed corruption was not distinguished')
    return {'status':'PASS','variables':measured[0],'rows':measured[1],'degree':measured[2],
            'monomials':measured[3],'height':measured[4],'row_height':measured[5],
            'exact_forward_and_reverse_operations':len(ops),'printed_rows_parsed':len(printed),
            'height_witness':[47281,[10,10,12,12]],'all_coordinates_live':True,
            'negative_controls':['changed expanded constant','changed printed residual']}

def child(relative):
    args=[sys.executable,'-B']
    if sys.flags.optimize:args+=['-O']
    args+=[str(ROOT/relative)]
    p=subprocess.run(args,cwd=ROOT,capture_output=True,text=True)
    need(p.returncode==0,relative+' failed:\n'+p.stdout+'\n'+p.stderr)
    return json.loads(p.stdout)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);a=ap.parse_args()
    report={'status':'PASS','python_optimized':bool(sys.flags.optimize)}
    report['final_equations']={name:check_final(name,profile) for name,profile in PROFILES.items()}
    report['direct_source']=child('direct/verify.py')
    report['compact']=child('compact/verify.py')
    if (ROOT/'MANIFEST_SHA256.json').exists():
        hashes=read(ROOT/'MANIFEST_SHA256.json')
        for p,h in hashes.items():need(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,'manifest '+p)
        report['manifest_files_checked']=len(hashes)
    report['scope']='Complete finite row/circuit/coefficient checks plus printed residual parsing; ordinary proofs and named inherited calibrations remain the mathematical basis.'
    text=json.dumps(report,indent=2,sort_keys=True)+'\n'
    if a.receipt:a.receipt.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
