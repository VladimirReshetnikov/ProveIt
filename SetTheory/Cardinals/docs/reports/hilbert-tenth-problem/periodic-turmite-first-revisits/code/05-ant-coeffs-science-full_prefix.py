#!/usr/bin/env python3
"""Independently authored exact literal1/3 coefficient prefix.
Imports only our new symbolic source compiler and finite JSON-only profile builder.
Never imports or executes any authenticated upstream code or saved schedule.
"""
import argparse,hashlib,json,pathlib,sys
from occurrence_compiler import Source,Occurrences
PROFILE_ROOT=pathlib.Path(__file__).resolve().parent/'geometry'
sys.path.insert(0,str(PROFILE_ROOT))
from profile_api import build_profiles

U=481238074400;S=576000;V=U//2;R=601547591;X0=481225262775
KINDS=('DUP','NAND','MOVE_LEFT','MOVE_RIGHT')

def geometric(d,z,n):
    assert n>=1
    p=z;g='one'
    for bit in bin(n)[3:]:
        oldp=p;p=d.gate('*',p,p);g=d.gate('+',g,d.gate('*',oldp,g))
        if bit=='1':g=d.gate('+',g,p);p=d.gate('*',p,z)
    return p,g

class Profiles:
    def __init__(self,d,zero,minus):self.d=d;self.zero=zero;self.minus=minus;self.cache={};self.hist={}
    def get(self,width,plus,minus=0):
        assert not(plus&minus) and 0<=plus<1<<width and 0<=minus<1<<width
        if not(plus|minus):return self.zero
        key=width,plus,minus
        if key in self.cache:return self.cache[key]
        def digit(k):return 'one' if plus>>k&1 else self.minus if minus>>k&1 else self.zero
        a=digit(width-1)
        for k in range(width-2,-1,-1):a=self.d.gate('+',self.d.gate('*',a,'three'),digit(k))
        self.cache[key]=a;self.hist[width]=self.hist.get(width,0)+1
        return a

def build(d,program,anchor):
    stages={};last=(0,0)
    def stage(name):
        nonlocal last
        stages[name]={'M':d.M-last[0],'A':d.A-last[1],'total':d.M+d.A-sum(last)};last=d.M,d.A
    o=Occurrences(d,program);occ,oreceipt=o.compile();stage('occurrences')
    zero=o.zero;minus=d.gate('-',zero,'one');two=d.gate('+','one','one')
    H,B,F,Q=build_profiles()
    assert len(H)==len(B)==len(F)==S
    pf=Profiles(d,zero,minus)
    hw=[pf.get(400,a) for a in H];bw=[pf.get(400,a) for a in B];fw=[pf.get(400,a) for a in F]
    hlo=[pf.get(25,a&((1<<25)-1)) for a in H];hhi=[pf.get(375,a>>25) for a in H]
    qw={kind:{dx:pf.get(400,*Q[kind][dx]) for dx in sorted(Q[kind])} for kind in KINDS}
    stage('small_profiles_and_basic_literals')
    _,G=geometric(d,o.z,R)
    exponents=[375,V-425,V-400,V-25,U-25]
    powers={e:d.power('three',e) for e in exponents}
    stage('geometric_sum_and_fixed_shifts')
    corr=[zero]*S
    for kind in KINDS:
        for s,t in enumerate(occ[kind]):
            for dx,q in qw[kind].items():
                x=(600*(s+1)+dx)%S
                corr[x]=d.gate('+',corr[x],d.gate('*',t,q))
    stage('operation_corrections')
    full=[None]*S;cut=[None]*S
    for x in range(S):
        bulk=d.gate('+',d.gate('*',bw[x],G),corr[x])
        full[x]=d.gate('+',hw[x],d.gate('+',d.gate('*',o.z,bulk),d.gate('*',powers[V-400],fw[x])))
        cut[x]=d.gate('+',hhi[x],d.gate('+',d.gate('*',powers[375],bulk),d.gate('*',powers[V-425],fw[x])))
    tile=[None]*S
    for x in range(S):
        tile[x]=d.gate('+',d.gate('+',cut[x],d.gate('*',powers[V-25],full[(x-S//2)%S])),d.gate('*',powers[U-25],hlo[x]))
    stage('bulk_boundary_and_period_join')
    labels={}
    for j in range(S):
        x=(288650-j)%S;labels[f'tile:{j}']=tile[x];labels[f'first:{j}']='one' if H[x]>>25&1 else zero
    symbols={-1:minus,0:zero,1:'one'}
    adata=[[0]*221 for _ in range(584)]
    seen=set()
    for x,y,old,new in anchor['patch']:
        j=289200-x;i=y+144
        assert 0<=j<584 and 0<=i<=220 and (j,i) not in seen
        seen.add((j,i));adata[j][i]=new-old
    for j,row in enumerate(adata):
        a=symbols[row[220]]
        for i in range(219,-1,-1):a=d.gate('+',d.gate('*',a,'three'),symbols[row[i]])
        labels[f'anchor:{j}']=a
    stage('anchor_rows')
    labels['Cu']=d.power('three',U);labels['Cbase']=d.power('three',U-219);labels['C198']=d.power('three',198)
    labels['Cx']=d.gate('-',labels['Cu'],'one')
    four=d.gate('+',two,two);six=d.gate('+','three','three');eight=d.gate('+',four,four);nine=d.gate('*','three','three')
    labels['EndpointK']=d.power('three',X0);labels['EndpointD']=d.gate('-',labels['Cx'],'one')
    labels.update({'0':zero,'1':'one','2':two,'3':'three','4':four,'6':six,'8':eight,'9':nine})
    stage('remaining_named_constants')
    assert len(labels)==1152598
    output_digest=hashlib.sha256()
    for name,value in labels.items():output_digest.update(f'{name}\t{value}\n'.encode())
    receipt={'source':d.receipt(),'stages':stages,'occurrence_details':oreceipt,'profile_cache_by_width':pf.hist,'profile_total':len(pf.cache),'correction_nonzero_columns':{k:len(Q[k]) for k in KINDS},'coefficient_labels':len(labels),'output_alias_sha256':output_digest.hexdigest(),'two_input_strict_total':d.n+2307457,'one_input_strict_total':d.n+2307467,'old_strict_prefix':554386261707905131,'saved_operations':554386261707905131-d.n}
    return labels,receipt

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--assets',required=True);ap.add_argument('--anchor',required=True);ap.add_argument('--out',required=True);ap.add_argument('--digest',action='store_true');ap.add_argument('--emit');a=ap.parse_args()
    assets=pathlib.Path(a.assets);assert assets.resolve()==PROFILE_ROOT.parent/'data/recipe_assets';program_path=assets/'ca/physical_program.json';anchor_path=pathlib.Path(a.anchor)
    program=json.loads(program_path.read_text());anchor=json.loads(anchor_path.read_text())
    sink=open(a.emit,'x') if a.emit else None
    try:d=Source(sink,a.digest);labels,receipt=build(d,program,anchor)
    finally:
        if sink is not None:sink.close()
    pins=list(sorted(assets.rglob('*.json')))+[pathlib.Path(__file__),pathlib.Path(__file__).with_name('occurrence_compiler.py'),PROFILE_ROOT/'profile_api.py',PROFILE_ROOT/'verify_profiles.py',PROFILE_ROOT/'scan_motifs.py',program_path,anchor_path]
    receipt.update(status='EXACT_STRUCTURED_LITERAL_PREFIX',pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in pins},no_upstream_execution=True,arithmetic_literals=[1,3],arithmetic_opcodes=['+','-','*'],new_witnesses=0,new_equations=0,variable_degree_unchanged=2304000)
    pathlib.Path(a.out).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
