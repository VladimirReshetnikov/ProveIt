# New experiment assembled in this study. Imported dependencies and baseline search
# attribution are recorded in PROVENANCE.json and NOTICE.txt.
from pathlib import Path
import sys,json,importlib.util,collections,argparse
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description="Experimental mixed-radix 3/6 source compiler; no small-machine theorem.")
ap.add_argument('--construction-dir',type=Path,default=HERE/'upstream/construction')
ap.add_argument('--profiles-dir',type=Path,default=HERE/'profiles')
args=ap.parse_args()
BASE=args.construction_dir.resolve()
PROFILES=args.profiles_dir.resolve()
sys.path.insert(0,str(BASE));import compiler as c,baseline_tools as b
INC=('leaf','inc',1);BREAK=('leaf','breakTo',1)

def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x

def audit(profile):
 root=PROFILES/profile;nn={k:tup(v) for k,v in json.loads((root/'nodes.json').read_text()).items()};fixed=b.read_table(root/'fixed.native.tm')
 c.raw_nodes=lambda:nn;c.machine=lambda:(fixed,None)
 c.MACROS[(INC,INC)]=99;c.MACROS[(INC,(INC,INC))]=190
 c.MACROS['mixed6root']=330;c.MACROS['mixed6mult']=334;c.MACROS['doubleroot']=330
 grammar=c.read_grammar(root/'run.best.grammar.json')
 raw,_,shape=c.build(grammar);sites,ins,contracts=c.source(grammar)
 def word(t):
  if t=='node60':return [61,61]
  if t=='node61':return [61]*3
  if t=='mixed6mult':return [61]*6
  if c.isnode(t):return word(t[0])+word(t[1])
  return [c.MACROS.get(t,-1) if t!=BREAK else -1]
 ww=word(grammar);expected=json.loads((root/'word.json').read_text());assert ww==expected
 ZERO=('z',);ONE=('s',ZERO)
 def inc(t,n=1):
  for _ in range(n):t=('s',t)
  return t
 def C(k,a,b):return ('C',k,a,b)
 def I(a,b):return C(3,a,b)
 def M(a,b):return inc(C(6,a,b))
 def E(a,b):return inc(C(6,a,b),4)
 def U(a,B):return inc(I(B,a),2)
 def N(a):return I(a,ONE)
 def Aand(a,b):return N(I(a,N(b)))
 def Ex(a,B):return N(U(a,N(B)))
 oldt,A,d,h,Y,X=(('atom',a) for a in ('t','a','d','h','y','x'));T,D,H=oldt,d,h;stack=[];fields=[Y,X]
 for op in ww[:-3]:
  if op==19:stack.append(T);T=ZERO
  elif op in (98,12,166):stack.append(T);T={98:D,12:H,166:A}[op]
  elif op==90:T=I(stack.pop(),T)
  elif op==330:
   if profile=='cons6':T=C(6,stack.pop(),T)
   else:assert T[0:2]==('C',3);T=C(6,T[2],T[3])
  elif op==61:T=inc(T)
  elif op==69:H=('add',H,fields.pop(0))
  elif op==213:D=('add',D,fields.pop(0));T=I(T,D)
  else:raise AssertionError(op)
 assert not fields and ww[-3:]==[194,221,-1]
 heads=[I(Ex(D,U(D,H)),H),I(U(D,U(A,H)),U(A,U(D,H))),I(M(H,D),I(E(H,A),M(A,D))),I(E(H,D),I(M(A,H),M(A,D))),Ex(D,E(H,D)),I(U(D,A),I(U(D,I(A,H)),U(D,H)))]
 rho=I(I(I(H,d),D),I(I(D,H),I(A,H)));gamma=I(A,U(A,A));v=I(M(H,D),U(A,M(H,D)));point=I(A,M(A,D));S=U(D,Aand(I(M(H,D),point),I(M(A,D),A)));Q=U(A,I(S,N(point)))
 assert stack==[oldt,U(d,h),rho]+heads+[gamma]
 assert T==N(I(v,Q))
 # Count fold opportunities including each new fixed helper, then separately qualify all-nominal pairs.
 helpers={q:None for q,b in fixed if q>=330}
 op=c.opportunities_fast(raw,{**shape,**helpers});matching=c.max_matching(op)
 rec={'profile':profile,'fixed_controls':len(fixed)//2,'raw_AX_readers':len(shape),'raw_controls':len(raw)//2,'nominal_matching_with_new_helpers':len(matching),'optimistic_total_with_all_helper_matching':len(raw)//2-len(matching),'matching_pairs':matching,'matching_is_not_simultaneous_fold_certificate':True,'macro_tokens':len(ww),'source_sites':len(sites),'source_outcomes':len(contracts),'all_natural_free_constructor_emitter_audit':True,'source_max_path':max(len(p)for p,_,_ in sites),'literal_startup_checked':False,'full_source_simulation_checked':False,'status':'experimental; no accepted smaller TM'}
 (root/'raw.native.tm').write_text(b.table_text(raw));(root/'source_instructions.json').write_text(json.dumps(ins));(root/'source_sites.json').write_text(json.dumps([[list(p),o,a]for p,o,a in sites]));(root/'audit.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
for p in ['cons6','double']:audit(p)
