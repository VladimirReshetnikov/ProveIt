#!/usr/bin/env python3
"""Portable free-algebra checks for 51 AX words and 54 head variants.
This is a source formula/stack audit, not a physical TM-runtime verifier.
No numerical sampling or Python assertions establish the identities.
"""
from pathlib import Path
from itertools import permutations
import argparse,json,hashlib
P=Path(__file__).resolve().parent
ZERO=('zero',);BOT=('succ',ZERO)
def atom(n):return('atom',n)
def I(x,y):return('im',x,y)
def S(x):return('succ',x)
def M(x,y):return S(I(x,y))
def E(x,y):return S(S(S(I(x,y))))
def U(x,y):return S(S(I(y,x)))
def N(x):return I(x,BOT)
def conjunction(x,y):return N(I(x,N(y)))
def exists(x,y):return N(U(x,N(y)))
def add(x,y):return('add',x,y)
def need(c,msg):
 if not c:raise ValueError(msg)
def run(word,initial):
 t,a,d,h,old,fields=initial;stack=list(old);fields=list(fields)
 for op in word:
  if op in(0,1,6,7):stack.append(t);t={0:h,1:d,6:a,7:ZERO}[op]
  elif op==2:
   need(bool(stack),'empty pair stack');t=I(stack.pop(),t)
  elif op==3:t=S(t)
  elif op==4:
   need(bool(fields),'missing H field');h=add(h,fields.pop(0))
  elif op==5:
   need(bool(fields),'missing D field');d=add(d,fields.pop(0));t=I(t,d)
  else:raise ValueError('unexpected primitive before guard suffix')
 return(t,a,d,h,stack,fields)
def heads(a,d,h):
 return[I(exists(d,U(d,h)),h),I(U(d,U(a,h)),U(a,U(d,h))),
         I(M(h,d),I(E(h,a),M(a,d))),I(E(h,d),I(M(a,h),M(a,d))),
         exists(d,E(h,d)),I(U(d,a),I(U(d,I(a,h)),U(d,h)))]
def gamma(x):return I(x,U(x,x))
def gate(a,d,h,meta):
 if meta['a_b_reversed']:h,d=d,h
 point=I(a,M(a,d));v=I(M(h,d),U(a,M(h,d)))
 left=I(a,I(M(h,d),M(a,d)))if meta['matrix_variant']//2 else I(M(h,d),point)
 right=I(M(a,d),a)
 matrix=conjunction(right,left)if meta['matrix_variant']%2 else conjunction(left,right)
 sep=U(d,matrix);q=U(a,I(sep,N(point)))
 g=gamma({'c':a,'a':h,'b':d}[meta['gamma']])
 return N(I(v,I(g,q)))if meta['outer_antecedents_exchanged']else N(I(g,I(v,q)))
def old_gate(a,d,h):
 v=I(M(h,d),U(a,M(h,d)));p=I(a,M(a,d))
 sep=U(d,conjunction(I(M(h,d),p),I(M(a,d),a)))
 return N(I(v,U(a,I(sep,N(p)))))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path);args=ap.parse_args()
 cfg=json.loads((P/'source_inputs.json').read_text());prefix=cfg['prefix'];suffix=cfg['suffix']
 need(suffix==[8,9,10],'guard suffix changed')
 t,a,d0,h0,y,x=map(atom,('t','A','D0','H0','y','x'));d=add(d0,x);h=add(h0,y)
 initial=(t,a,d0,h0,[],[y,x])
 rho=I(I(I(h,d0),d),I(I(d,h),I(a,h)))
 expected_prefix=(rho,a,d,h,[t,U(d0,h0)],[])
 need(run(prefix,initial)==expected_prefix,'register read and rho prefix')
 hwords=cfg['head_words'];head_values=heads(a,d,h)
 ordinary=prefix+sum((vv[0]for vv in hwords),[])
 variants=0
 for slot,choices in enumerate(hwords):
  for w in choices:
   result=run(w,(rho,a,d,h,[t],[]));ok=False
   for aa,dd,hh in permutations((a,d,h)):
    goal=heads(aa,dd,hh)[slot];alternatives=[goal]
    if slot in(2,3,5):alternatives.append(I(goal[2][1],I(goal[1],goal[2][2])))
    if result[0]in alternatives:ok=True
   need(ok and result[1:]==(a,d,h,[t,rho],[]),'head role or stack contract')
   variants+=1
 checked=[]
 for j,(w,meta)in enumerate(zip(cfg['gate_words'],cfg['gate_metadata'])):
  full=ordinary+w+suffix
  need(len(full)==191,'gate token count')
  target=(gate(a,d,h,meta),a,d,h,expected_prefix[4]+[rho]+head_values,[])
  need(run(full[:-3],initial)==target,'complete gate expression or stack')
  checked.append(full)
 need(checked[0]==cfg['baseline'],'baseline word binding')
 for j,w in enumerate(cfg['bundle_words'][1:]):
  hh=head_values.copy();b=[a,h,d][j]
  hh[4]=N(I(gamma(b),U(d,N(E(h,d)))))
  target=(old_gate(a,d,h),a,d,h,expected_prefix[4]+[rho]+hh,[])
  need(len(w)==191 and w[:len(prefix)]==prefix and w[-3:]==suffix,'bundled boundaries')
  need(run(w[:-3],initial)==target,'complete bundled expression or stack')
  checked.append(w)
 need(len(set(map(tuple,checked)))==51,'distinct word count')
 # Negative control: the declared baseline must reject a changed parameter token.
 bad=checked[0][:-3];bad[121]=0
 need(run(bad,initial)!=run(checked[0][:-3],initial),'negative control accepted')
 result={'ok':True,'distinct_full_words':len(checked),'gate_variants':48,'bundled_witness_variants':3,'head_role_variants':variants,'macro_tokens_each':191,'pushed_entries_each':9,'symbolic_parameter_reads_exact':True,'guard_suffix_unchanged':True,'negative_control_rejected':True,'input_sha256':hashlib.sha256((P/'source_inputs.json').read_bytes()).hexdigest(),'scope':'Free-algebra formula, stack and register identities; excludes physical scanners, compatible folds, startup, and a new kernel proof endpoint.'}
 if args.out:args.out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
