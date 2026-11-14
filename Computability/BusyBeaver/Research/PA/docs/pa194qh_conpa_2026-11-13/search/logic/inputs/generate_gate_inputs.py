from pathlib import Path
import json, importlib.util
ROOT=Path(__file__).resolve().parent
vp=ROOT.parent/'helpers/free_term_reference.py'
spec=importlib.util.spec_from_file_location('oldverify',vp);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
s=(ROOT/'input.txt').read_text().split();it=iter(map(int,s));nt,nw,np,nrows=[next(it)for _ in range(4)]; attrs=[[next(it)for _ in range(6)]for _ in range(nt)];rows=[[next(it)for _ in range(5)]for _ in range(nrows)];shape=[[next(it)for _ in range(2)]for _ in range(np)]
def rv():return[next(it)for _ in range(next(it))]
prefix,suffix,g0,g1=[rv()for _ in range(4)];hv=[[[rv()for _ in range(2)]for _ in range(6)]for _ in range(6)]
def I(a,b):return(0,a,b)
def M(a,b):return(1,a,b)
def U(a,b):return(2,b,a)
def N(a):return I(a,1)
def And(a,b):return N(I(a,N(b)))
def Gamma(a):return I(a,U(a,a))
def emit(t):
 if isinstance(t,str):return[{'A':6,'D':1,'H':0}[t]]
 if isinstance(t,int):return[7]+[3]*t
 tag,l,r=t;return emit(l)+emit(r)+[2]+[3]*tag
A,D,H='ADH'
point=I(A,M(A,D));V=I(M(H,D),U(A,M(H,D)))
left=I(M(H,D),point);right=I(M(A,D),A)
words=[];matrices=[]
for variant in range(4):
 L=I(A,I(M(H,D),M(A,D)))if variant//2 else left
 mat=And(right,L)if variant%2 else And(L,right)
 sep=U(D,mat);q=U(A,I(sep,N(point)));gate=N(I(V,q))
 suff=emit(Gamma(A))+emit(gate)+[8,9,10]
 assert len(suff)==69
 words.append(suff);matrices.append(mat)
assert words[0]==suffix
# Check all full source words with independent free-term evaluator, not numerical samples.
a,d0,h0,t,y,x=map(v.atom,('A','D0','H0','t','y','x'));d=v.add(d0,x);h=v.add(h0,y)
heads=v.heads(a,d,h);rho=v.I(v.I(v.I(h,d0),d),v.I(v.I(d,h),v.I(a,h)))
records=[]
for variant,suff in enumerate(words):
 full=prefix+sum((p[0][0]for p in hv),[])+suff
 pnt=v.I(a,v.M(a,d));vac=v.I(v.M(h,d),v.U(a,v.M(h,d)))
 L=v.I(a,v.I(v.M(h,d),v.M(a,d)))if variant//2 else v.I(v.M(h,d),pnt)
 R=v.I(v.M(a,d),a);mat=v.conjunction(R,L)if variant%2 else v.conjunction(L,R)
 gate=v.N(v.I(vac,v.U(a,v.I(v.U(d,mat),v.N(pnt)))))
 got=v.run(full[:-3],(t,a,d0,h0,[],[y,x]));expected=(gate,a,d,h,[t,v.U(d0,h0),rho]+heads+[v.gamma(a)],[])
 assert got==expected
 records.append({'matrix_variant':variant,'macro_tokens':len(full),'full_symbolic_stack_checked':True,'word':full})
for mode,inds in [('gates12',[1,2]),('gates13',[1,3])]:
 out=[' '.join(map(str,[nt,nw,np,nrows]))]+[' '.join(map(str,r))for r in attrs+rows+shape]
 for vv in [prefix,[],words[inds[0]],words[inds[1]]]+[xx for hh in hv for pp in hh for xx in pp]:out.append(' '.join(map(str,[len(vv)]+vv)))
 (ROOT/(mode+'.input.txt')).write_text('\n'.join(out)+'\n')
(ROOT/'gate_word_receipt.json').write_text(json.dumps(records,indent=2)+'\n')
print('Checked four free-term gate emitters; all 190 tokens and ten stack entries.')
