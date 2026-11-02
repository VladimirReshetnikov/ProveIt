#!/usr/bin/env python3
"""Independent tropical/sensitivity upper bound and modular lower bound."""
import collections,gzip,hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';GRAPH=BASE/'research/thirteen-unit-sphere96/polynomial.json';MASK=BASE/'Lean/DiophantineConsistency/CurrentMaskData2011.lean';KERNEL=BASE/'Lean/DiophantineConsistency/CurrentKernelData2011.lean';P=1000000007
VARS=('J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma');PORTS=('beta','K0','MC','MF')
def need(b,m):
    if not b:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def op(a,b,kind):
    out=[0]*(len(a)+len(b)-1 if kind=='*' else max(len(a),len(b)))
    if kind=='*':
        for i,x in enumerate(a):
            for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%P
    else:
        for i,x in enumerate(a):out[i]=(out[i]+x)%P
        for i,x in enumerate(b):out[i]=(out[i]+x*(1 if kind=='+' else -1))%P
    while len(out)>1 and out[-1]==0:out.pop()
    return out
def main():
    b=subprocess.run(['git','show','9294c63bd0:'+GRAPH.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
    need(hashlib.sha256(b).hexdigest()==sha(GRAPH)=='48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1','graph provenance')
    need(sha(MASK)=='8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582' and sha(KERNEL)=='529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c','exact 2011 port source hashes')
    m=MASK.read_text();k=KERNEL.read_text();need('def radix : ℕ := 2 ^ 47' in m and 'def beta : ℕ := radix ^ 2011 - 1' in m and '![beta, K, lowPort, highPort + beta]' in m and 'CurrentMasks2011.ports (K : ℤ)' in k,'actual port definitions')
    g=json.loads(GRAPH.read_bytes());rows=g['source'];need(g['witnesses']==list(VARS) and g['fixed_numerals']==list(PORTS) and len(rows)==75 and g['output']=='polynomial','graph signature')
    by={r[0]:r for r in rows};need(len(by)==75 and collections.Counter(r[1] for r in rows)=={'*':42,'+':18,'-':15},'graph operators')
    portreceipt=BASE/'reviews/equation14-historical-literal-binding/ports-receipt.json'
    need(sha(portreceipt)=='b9f356e64350b0d6c34d7dbd7b766561fbe3ec30374dd26158f92db92176f413','prior captured-port receipt')
    captured=json.loads(portreceipt.read_bytes());need(captured['kernel_data_source_sha256']==sha(KERNEL) and len(captured['ports'])==4,'captured tuple provenance')
    sys.set_int_max_str_digits(0);binding=g['coefficient_binding'];records={}
    for i,name in enumerate(PORTS):
        entry=binding['ports'][name];fpath=GRAPH.parent/binding['path']/entry['file'];raw=gzip.decompress(fpath.read_bytes());record=captured['ports'][i]
        cpath=BASE/'reviews/equation14-historical-literal-binding/port-outputs'/f'port{i}.txt.gz'
        need(sha(fpath)==entry['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==entry['raw_sha256']==record['integer_sha256'] and len(raw)==entry['raw_bytes']==record['integer_bytes'],'bound port '+name)
        need(sha(cpath)==record['captured_gzip_sha256'] and int(gzip.decompress(cpath.read_bytes()).strip())==int.from_bytes(raw,'big'),'captured port '+name)
        if name=='beta':need(int.from_bytes(raw,'big')==(1<<(47*2011))-1,'actual beta')
        records[name]=entry['raw_sha256']

    for row in [['ac','*','a','c'],['main_base','+','X','ac'],['gammaH','*','gamma','H'],['main_root','+','main_base','gammaH'],['main_square','*','main_root','main_root'],['c2','*','c','c'],['a2','*','a','a'],['Delta','+','a2','H'],['Dc2','*','Delta','c2'],['N1','-','main_square','Dc2']]:need(by[row[0]]==row,'N1 cut '+row[0])
    # (X+ac+gamma H)^2-(a^2+H)c^2 = (X+gamma H)^2+2ac(X+gamma H)-Hc^2.
    neg=float('-inf');d={n:(1,neg) for n in VARS};d.update({n:(0,0 if n!='beta' else neg) for n in PORTS});beta=(pow(2,47*2011,P)-1)%P;f={n:[0,1] for n in VARS};f.update({'beta':[beta],'K0':[0],'MC':[0],'MF':[0]})
    def at(env,x):return env[x] if isinstance(x,str) else ((0,neg) if env is d else [x%P])
    for name,kind,l,r in rows:
        a,b=at(d,l),at(d,r)
        z=(a[0]+b[0],max(a[1]+b[0],a[0]+b[1])) if kind=='*' else (max(a[0],b[0]),max(a[1],b[1]))
        if name=='N1':
            u=max(d['X'][0],d['gammaH'][0]);bound=max(2*u,d['a'][0]+d['c'][0]+u,d['H'][0]+2*d['c'][0]);need(bound==18 and all(d[n][1]==neg for n in ('X','gammaH','a','c','H')),'N1 cancellation bound');z=(bound,neg)
        d[name]=z;f[name]=op(at(f,l),at(f,r),kind)
    need(d['polynomial']==(96,95),'degree and non-beta port upper bounds')
    coefficient=f['polynomial'][96] if len(f['polynomial'])>96 else 0
    expected=256*pow(beta,44,P)*pow(2,8,P)*pow((beta-2)%P,4,P)%P
    need(len(f['polynomial'])==97 and beta==878756698 and coefficient==expected==645917148,'nonzero diagonal leading coefficient')
    def diagonal(bvalue, mutations=None):
        env={n:[0,1] for n in VARS};env.update({'beta':[bvalue], 'K0':[0], 'MC':[0], 'MF':[0]})
        for name,kind,l,r in rows:
            if mutations and name in mutations:kind,l,r=mutations[name]
            x=env[l] if isinstance(l,str) else [l%P];y=env[r] if isinstance(r,str) else [r%P];env[name]=op(x,y,kind)
        return env['polynomial']
    altered=diagonal(beta,{'polynomial':('-','sqPQ',3)})
    need(len(altered)<=81,'mutated highest square should lose degree 96')
    exceptional=diagonal(2);need(len(exceptional)<=96,'beta 2 must cancel diagonal leading term')
    need(max(d['MC'][1]+d['sqU'][0],d['MC'][0]+d['sqU'][1])==96,'synthetic other-port top-degree sensitivity')
    live=set()
    def visit(n):
        if type(n) is int or n in live:return
        live.add(n)
        if n in by:visit(by[n][2]);visit(by[n][3])
    visit('polynomial');need(set(by)<=live and set(VARS)<=live and set(PORTS)<=live,'graph liveness')
    print(json.dumps({'status':'PASS_INDEPENDENT_2011_75_DEGREE_96','source_commit':'9294c63bd0','graph_sha256':sha(GRAPH),'operations':dict(sorted(collections.Counter(r[1] for r in rows).items())),'degree_upper_bound':96,'other_port_degree_upper_bound':95,'tuple_port_raw_sha256':records,'prior_port_receipt_sha256':sha(portreceipt),'negative_controls':['drop_top_square','exceptional_beta_diagonal','synthetic_top_degree_port'],'modulus':P,'beta_modulus':beta,'diagonal_t96_coefficient':coefficient,'scope':'External exact degree of the 75-row graph at the actual beta; the sensitivity bound makes K0/MC/MF immaterial to degree 96. No Lean expression binding, TeX decoder, iPRA statement or minimum claim.'},indent=2))
if __name__=='__main__':main()
