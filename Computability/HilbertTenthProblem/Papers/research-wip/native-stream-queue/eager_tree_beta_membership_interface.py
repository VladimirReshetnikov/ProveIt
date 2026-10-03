"""Paid beta-coded suffix membership and the unbounded Tree row-coherence boundary."""
import argparse, hashlib, itertools, json, math
from collections import Counter
from pathlib import Path
if not __debug__: raise RuntimeError('Run without -O')
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
PIN_NAMES=[WIP+'eager_tree_pointer_product_scout.py',WIP+'eager_tree_pointer_product_scout.json',WIP+'eager_tree_pointer_product_scout.md',WIP+'review_eager_tree_aebfa.md',WIP+'review_one_coordinate_aebfa.md','Computability/HilbertTenthProblem/Lean/Diophantine/Common/MRDPCore.lean','Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean','Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding/BoundedCipherDioph.lean','SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex']
PINS= {'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/eager_tree_pointer_product_scout.py': '35fab9c363c38421a2d4b569bfd56f1cddf95717f9dfaa37ada4ce7dc6fe49bd', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/eager_tree_pointer_product_scout.json': '9d0eaa72ffee7c900f8e348c305293193a8b4ebaa066c534902795f6b87ba4cc', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/eager_tree_pointer_product_scout.md': 'c0c5991e451ae74fc9a6b9c15e996a4e2f80dd04b33d2bb2a433d03142bf47b3', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_eager_tree_aebfa.md': 'a8a5ff72f4e90ccb461ec77339653c4613d65dc7fc40ff98445370ee13e4ff6d', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_one_coordinate_aebfa.md': 'e3bcb9711921b77c4de4823b889fc1f9b1c4d790f05a6da12684067091192937', 'Computability/HilbertTenthProblem/Lean/Diophantine/Common/MRDPCore.lean': 'c6f8b993f95be28b1f18e21cb82442c61d4011907f73f6725ac2f15486864c78', 'Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean': 'b644241111b4ff0232d6c49838588cbcc49c44751cfaa440226f2820d4f1aa02', 'Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding/BoundedCipherDioph.lean': '889385240f9bbd51bf7732b85aaaf4071f3bc1904fb64af68b80763af031cbf6', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex': 'e7047ec1f4708fd6497607b41c7b8e37da230ca77398933820c63ebc5a28a3ce', 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_fixed_affine_exponent52.md': '891301377f3740657c268e3e48f697dc5cb5a08037665aa772c1bff0d200b9ec'}

def need(x,msg):
    if not x:raise AssertionError(msg)
def exact(a,b):
    return type(a) is type(b) and (a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a) if type(a) is dict else len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b)) if type(a) in (tuple,list) else a==b)
def digest(b):return hashlib.sha256(b).hexdigest()
def build(active=False):
    need(type(active) is bool,'Exact active flag')
    rows=[['ih','+','i','h'],['j1','+','ih',2],['g','*','b','j1'],['m','+','g',1],['qm','*','q','m'],['AD','-','A','D'],['r0','-','AD','qm'],['gD','-','g','D'],['r1','-','gD','s'],['Nj','-','N','j1'],['r2','-','Nj','k'],['sq0','*','r0','r0'],['sq1','*','r1','r1'],['sq2','*','r2','r2'],['sum01','+','sq0','sq1'],['sos','+','sum01','sq2']]
    if active:rows.append(['out','*','active','sos'])
    return dict(inputs=['A','b','i','N','D']+(['active'] if active else []),witnesses=['h','k','q','s'],residuals=['r0','r1','r2'],source=rows,output='out' if active else 'sos')
def run(rows,v):
    e=dict(v)
    for n,o,a,b in rows:
        a=e[a] if type(a) is str else a;b=e[b] if type(b) is str else b;e[n]=a+b if o=='+' else a-b if o=='-' else a*b
    return e
def polyadd(a,b,sgn=1):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+sgn*c
    return {m:c for m,c in out.items() if c}
def polymul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():mn=tuple(sorted(m+n));out[mn]=out.get(mn,0)+c*d
    return {m:c for m,c in out.items() if c}
def atom(x):return {(x,):1} if type(x) is str else ({():x} if x else {})
def expansion(packet):
    e={x:atom(x) for x in packet['inputs']+packet['witnesses']}
    for n,o,a,b in packet['source']:
        a=e[a] if type(a) is str else atom(a);b=e[b] if type(b) is str else atom(b);e[n]=polymul(a,b) if o=='*' else polyadd(a,b,1 if o=='+' else -1)
    return e

def beta(A,b,j):return A%((j+1)*b+1)
def encode(seq):
    # This constructs a finite CRT witness; its running cost is not hidden in the paid atom.
    b=math.factorial(len(seq))*(max(seq,default=0)+1);A=0;M=1;mods=[]
    for j,v in enumerate(seq):
        m=(j+1)*b+1;need(0<=v<m and math.gcd(M,m)==1,'canonical coprime CRT moduli')
        A+=M*((v-A)*pow(M,-1,m)%m);M*=m;mods.append(m)
    need(all(beta(A,b,j)==v for j,v in enumerate(seq)),'actual CRT sequence')
    return A,b,mods

def witness(A,b,i,N,D,j):
    need(i<j<N and beta(A,b,j)==D,'actual suffix member')
    return dict(h=j-i-1,k=N-j-1,q=A//((j+1)*b+1),s=(j+1)*b-D)
def P(a,b):return (a+b)**2+a
def C(x,y,z):return P(z,P(x,y))

def verify(repo):
    repo=Path(repo);data={}
    for path,pin in PINS.items():
        b=(repo/path).read_bytes();need(digest(b)==pin,'Pinned source '+path);data[path]=b
    counts=Counter();forms=[]
    for active in (False,True):
        p=build(active);e=expansion(p);j1=polyadd(polyadd(atom('i'),atom('h')),atom(2));g=polymul(atom('b'),j1)
        r0=polyadd(polyadd(atom('A'),atom('D'),-1),polymul(atom('q'),polyadd(g,atom(1))),-1)
        r1=polyadd(polyadd(g,atom('D'),-1),atom('s'),-1);r2=polyadd(polyadd(atom('N'),j1,-1),atom('k'),-1)
        want=polyadd(polyadd(polymul(r0,r0),polymul(r1,r1)),polymul(r2,r2))
        if active:want=polymul(atom('active'),want)
        need(e[p['output']]==want,'exact entire source polynomial')
        M=sum(r[1]=='*' for r in p['source']);A=len(p['source'])-M;need((M,A)==(5+int(active),11),'full paid local ledger')
        live={p['output']}
        for n,o,a,b in reversed(p['source']):
            if n in live:live.update(x for x in (a,b) if type(x) is str)
        need(set(p['inputs']+p['witnesses'])|{r[0] for r in p['source']}<=live,'all local gates and inputs live')
        degree=max(map(len,want));need(degree==6+int(active),'actual formal degree includes b*(i+h+2)*q')
        forms.append(dict(packet=p,M=M,A=A,degree=degree,polynomial_terms=[dict(monomial=list(m),coefficient=c) for m,c in sorted(want.items())]));counts['full_polynomial_and_ledger_checks']+=1
    # Unfiltered natural tuples: forward soundness at every small zero.
    p=build(False)
    for A,b,i,N,D in itertools.product(range(7),range(3),range(3),range(4),range(4)):
        has=any(beta(A,b,j)==D for j in range(i+1,N))
        for h,k,q,s in itertools.product(range(3),repeat=4):
            v=dict(A=A,b=b,i=i,N=N,D=D,h=h,k=k,q=q,s=s)
            zero=run(p['source'],v)['sos']==0
            if zero:need(has,'natural zero implies exact suffix member');counts['unfiltered_natural_zeros']+=1
            counts['unfiltered_natural_assignments']+=1
        for j in range(i+1,N):
            if beta(A,b,j)==D:
                v=dict(A=A,b=b,i=i,N=N,D=D,**witness(A,b,i,N,D,j));need(run(p['source'],v)['sos']==0,'all true members have explicit natural witnesses');counts['natural_lifts']+=1
    sequences=[]
    for n in range(0,9):
        for shape in range(4):
            seq=[(j*j+shape*j+2*shape)%17 for j in range(n)];A,b,mods=encode(seq);sequences.append(dict(values=seq,A=A,b=b,moduli=mods));counts['crt_sequence_encodings']+=1
            for i in range(n+1):
                for D in range(18):
                    js=[j for j in range(i+1,n) if seq[j]==D]
                    need(bool(js)==any(beta(A,b,j)==D for j in range(i+1,n)),'exact arbitrary-length slice semantics');counts['sequence_suffix_checks']+=1
                    for j in js:need(run(p['source'],dict(A=A,b=b,i=i,N=n,D=D,**witness(A,b,i,n,D,j)))['sos']==0,'CRT member paid atom zero');counts['crt_member_lifts']+=1
    # Actual retained Tree rows all pass while an unlinked code column admits a false root.
    saved=json.loads(data[WIP+'eager_tree_pointer_product_scout.json']);tree=next(f['packet'] for f in saved['forms'] if f['packet']['N']==3 and f['packet']['cleanup'])
    v={n:0 for n in tree['free']};v.update(program=4,argument=0,output=0,r0_x=4,r0_u=1,r0_v=1,r0_t3=1,r1_z=1,r1_t0=1,r2_z=1,r2_t0=1)
    env=run(tree['polynomial_source'],v);common=tree['residuals'][:5*3+3];need(all(env[r]==0 for r in common),'every actual retained local/root equation')
    actual_codes=[C(v[f'r{j}_x'],v[f'r{j}_y'],v[f'r{j}_z']) for j in range(3)];fake_codes=[actual_codes[0],actual_codes[1],C(1,1,0)];A,b,mods=encode(fake_codes);atoms=[];gp=build(True)
    for m in tree['slot_map']:
        i,s=m['row'],m['slot'];a=env[m['active_port']];D=env[m['target_port']] if m['target_port'] else 0
        w=witness(A,b,i,3,D,next(j for j in range(i+1,3) if fake_codes[j]==D)) if a else dict(h=0,k=0,q=0,s=0)
        av=dict(A=A,b=b,i=i,N=3,D=D,active=a,**w);out=run(gp['source'],av)[gp['output']];need(out==0,'unlinked beta lookup counterfeit');atoms.append(dict(row=i,slot=s,assignment=av,output=out))
    need(actual_codes==[400,2,2] and fake_codes==[400,2,25] and env[tree['output']]==279841,'actual original compiler rejects false tree')
    # Direct five-rule derivation: app(4,0)=app(app(0,0),app(0,0))=app(1,1)=6.
    need(2*0+1==1 and (0+1)*(0+1+1)+2*1+2==6,'false root has actual output6')
    counterfeit=dict(tree_assignment=v,actual_codes=actual_codes,unlinked_codes=fake_codes,A=A,b=b,retained_residuals=[env[r] for r in common],original_full_output=env[tree['output']],true_output=6,lookup_atoms=atoms)
    counts['complete_unlinked_code_counterexamples']=1
    # A second, separate trap: composite divisibility does not identify a zero factor.
    divisibility=dict(B=6,D=0,values=[2,3],encoded_product=(6-2)*(6-3));need(divisibility['encoded_product']%6==0 and 0 not in divisibility['values'],'false divisibility membership');counts['composite_divisibility_counterexamples']=1
    from fractions import Fraction
    signed=dict(A=0,b=1,i=0,N=2,D=3,h=0,k=0,q=-1,s=-1)
    real=dict(A=1,b=1,i=0,N=2,D=0,h=0,k=0,q=Fraction(1,3),s=2)
    for v in (signed,real):need(run(p['source'],v)['sos']==0 and all(beta(v['A'],v['b'],j)!=v['D'] for j in range(v['i']+1,v['N'])),'domain counterexample')
    counts['domain_counterexamples']=2
    # Actual source infrastructure exists, but this review did not instantiate its closure proof.
    core=data['Computability/HilbertTenthProblem/Lean/Diophantine/Common/MRDPCore.lean'].decode()
    for token in ('lemma boundedForall_dioph','abbrev encodedModuliProduct','lemma factorial_diophFn','lemma recursionTrace_iff'):need(token in core,'reviewed arithmetic interface token')
    return dict(status='PASS_SCOPED_TREE_BETA_MEMBERSHIP_INTERFACE',source_sha256=digest(Path(__file__).read_bytes()),pins=PINS,counts=dict(counts),forms=forms,crt_examples=sequences,unlinked_code_counterexample=counterfeit,composite_divisibility_counterexample=divisibility,domain_examples=dict(signed=signed,rational={k:str(v) if isinstance(v,Fraction) else v for k,v in real.items()}),scope='Complete16/17-gate fixed-arity suffix-membership atoms only. Uniform Tree row-code coherence remains a bounded universal compilation obligation. No unbounded Tree polynomial or universal arithmetic count emitted.')
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.repo)
    if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed full receipt')
    if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(r['status'],r['counts'])
if __name__=='__main__':main()
