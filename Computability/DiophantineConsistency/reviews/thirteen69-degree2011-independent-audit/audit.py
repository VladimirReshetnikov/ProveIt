#!/usr/bin/env python3
"""Independent tropical upper bound and univariate modular lower bound."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen69-dag-binding'
GRAPH=BASE/'research/thirteen-variable-independent/polynomial69.json'
NODES=PKG/'Thirteen69Nodes.lean'
MASK=BASE/'Lean/DiophantineConsistency/CurrentMaskData2011.lean'
KERNEL=BASE/'Lean/DiophantineConsistency/CurrentKernelData2011.lean'
P=1_000_000_007
VARS=('J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma')
PORTS=('beta','K0','MC','MF')

def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def op(a,b,sign):
    out=[0]*(len(a)+len(b)-1 if sign=='*' else max(len(a),len(b)))
    if sign=='*':
        for i,x in enumerate(a):
            for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%P
    else:
        for i,x in enumerate(a):out[i]=(out[i]+x)%P
        for i,x in enumerate(b):out[i]=(out[i]+x*(1 if sign=='+' else -1))%P
    while len(out)>1 and out[-1]==0:out.pop()
    return out

def main():
    for p in [PKG/'check_degree2011.py',PKG/'degree2011-receipt.json',PKG/'check_rows.py',NODES,GRAPH,MASK,KERNEL]:
        blob=subprocess.run(['git','show','d57ddf63de:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(blob).hexdigest()==sha(p),'committed input '+str(p))
    need(sha(GRAPH)=='3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f','graph pin')
    audit=BASE/'reviews/thirteen69-dag-binding-independent-audit/CHECK.json'
    need(sha(audit)=='26a42d561a232e2a49dae61f3a1f6f4cd882e3d38b6616aa62ed2ffcb0c081e5','prior independent row audit')
    checker=PKG/'check_degree2011.py'
    a=subprocess.run([sys.executable,'-I','-S',str(checker)],capture_output=True,timeout=180)
    need(a.returncode==0 and not a.stderr and a.stdout==(PKG/'degree2011-receipt.json').read_bytes(),'author normal receipt')
    b=subprocess.run([sys.executable,'-I','-S','-O',str(checker)],capture_output=True,timeout=60)
    need(b.returncode!=0 and not b.stdout and b'optimized Python is unsupported' in b.stderr,'optimized rejection')
    mask=MASK.read_text();kernel=KERNEL.read_text()
    need('def radix : ℕ := 2 ^ 47' in mask and 'def beta : ℕ := radix ^ 2011 - 1' in mask and
         '![beta, K, lowPort, highPort + beta]' in mask and 'def K : ℕ := rawWord radix' in kernel and
         'CurrentMasks2011.ports (K : ℤ)' in kernel,'exact port definitions')
    graph=json.loads(GRAPH.read_bytes());rows=graph['source'];by={r[0]:r for r in rows}
    # This local identity gives a valid bound despite cancellation of a²c²:
    # (X+ac+γH)²−(a²+H)c² = (X+γH)²+2ac(X+γH)−Hc².
    for row in [['ac','*','a','c'],['main_base','+','X','ac'],['gammaH','*','gamma','H'],
                ['main_root','+','main_base','gammaH'],['main_square','*','main_root','main_root'],
                ['c2','*','c','c'],['a2','*','a','a'],['Delta','+','a2','H'],
                ['Dc2','*','Delta','c2'],['N1','-','main_square','Dc2']]:need(by[row[0]]==row,'N1 cut '+row[0])
    neg=float('-inf')
    # Pair: upper total degree; upper degree of terms containing K0, MC or MF.
    degree={n:(1,neg) for n in VARS}
    degree.update({n:(0,0 if n!='beta' else neg) for n in PORTS})
    scalar={n:[0,1] for n in VARS}
    beta=(pow(2,47*2011,P)-1)%P
    scalar.update({'beta':[beta],'K0':[0],'MC':[0],'MF':[0]})
    def at(d,x):return d[x] if isinstance(x,str) else ((0,neg) if d is degree else [x%P])
    for name,operation,left,right in rows:
        x,y=at(degree,left),at(degree,right)
        if operation=='*':z=(x[0]+y[0],max(x[1]+y[0],x[0]+y[1]))
        else:z=(max(x[0],y[0]),max(x[1],y[1]))
        if name=='N1':
            du=max(degree['X'][0],degree['gammaH'][0])
            bound=max(2*du,degree['a'][0]+degree['c'][0]+du,degree['H'][0]+2*degree['c'][0])
            need(bound==18 and all(degree[n][1]==neg for n in ('X','gammaH','a','c','H')),'N1 cancellation bound')
            z=(bound,neg)
        degree[name]=z
        scalar[name]=op(at(scalar,left),at(scalar,right),operation)
    need(degree['polynomial']==(174,173),'degree and other-port sensitivity bounds')
    coefficient=scalar['polynomial'][174] if len(scalar['polynomial'])>174 else 0
    need(len(scalar['polynomial'])==175 and beta==878756698 and coefficient==737305404,'nonzero univariate leading coefficient')
    # These K0/MC/MF values are arbitrary substitutions: the separate degree
    # sensitivity bound proves no such port can occur in the top degree.
    print(json.dumps({'status':'PASS_INDEPENDENT_2011_DEGREE_174','source_commit':'d57ddf63de',
      'author_normal_exit':a.returncode,'author_optimized_exit':b.returncode,
      'parent_row_audit_sha256':sha(audit),'ordinary_degree_upper_bound':174,'other_port_degree_upper_bound':173,
      'modulus':P,'beta_modulus':beta,'univariate_t174_coefficient':coefficient,
      'univariate_substitution':'all thirteen variables t; beta fixed mod p; K0=MC=MF=0; separate bound excludes those three ports from degree 174',
      'scope':'External rigorous degree bound and modular nonvanishing; no Lean degree theorem, PDF binding, model converse, calibration or iPRA proof.'},indent=2))

if __name__=='__main__':main()
