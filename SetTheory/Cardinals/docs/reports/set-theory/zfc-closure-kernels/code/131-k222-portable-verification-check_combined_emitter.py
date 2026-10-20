#!/usr/bin/env python3
"""Independent all-natural binding of G plus helper-free seed source.

No source-construction or optimizer module is imported. Direct formula ASTs
are compiled to postfix words and linked to the pinned upstream arithmetic
macros by all-register bisimulation. Replacing two closed baseline intervals
gives an independent reference. Both complete CFG resolvers must agree with
the actual candidate and that reference, instruction for instruction.
"""
from pathlib import Path
from functools import cache
import argparse,hashlib,json,re,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(ROOT))

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(v):return tuple(map(freeze,v)) if isinstance(v,list) else v
I=lambda a,b:('I',a,b)
R=lambda a,b:('R',a,b)
Q=lambda a,b:('Q',a,b)
E=lambda a,b:('E',a,b)
N=lambda a:I(a,1)
def formulas():
 a,b,c='a','b','c'
 r=R(b,c);s=Q(c,I(R(c,a),R(c,b)))
 w=Q(b,I(c,N(Q(b,I(c,N(r))))))
 u=Q(a,I(s,w));h=Q(b,I(r,N(Q(a,I(c,N(u))))))
 v=I(R(a,b),Q(c,R(a,b)));e=I(E(a,b),Q(R(a,b),E(a,b)))
 oldcore=N(Q(c,I(I(c,r),N(h))))
 oldbundle=N(I(oldcore,I(v,N(e))))
 newbundle=N(I(v,Q(c,I(h,N(w)))))
 oldrow=I(E(c,a),I(E(c,b),E(a,b)))
 newrow=I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b))))
 return oldrow,newrow,oldbundle,newbundle

def postfix(t):
 if not isinstance(t,tuple):return [{'a':166,'b':121,'c':168,1:177}[t]]
 op,a,b=t
 if op=='I' and b==1:return postfix(a)+[218]
 return postfix(a)+postfix(b)+[{'I':119,'R':181,'Q':180,'E':182}[op]]
def execute(word):
 top='arbitrary_old_top';stack=['arbitrary_older_stack']
 for m in word:
  if m in (166,121,168,177):stack.append(top);top={166:'a',121:'b',168:'c',177:1}[m]
  elif m==218:top=N(top)
  else:top={119:I,181:R,180:Q,182:E}[m](stack.pop(),top)
 assert stack==['arbitrary_older_stack','arbitrary_old_top']
 return top

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--source',type=Path,required=True)
 p.add_argument('--output',type=Path,required=True)
 a=p.parse_args()
 assert __debug__,'Do not run with -O'
 import source_language as c
 from local_bisimulation import check as bisim
 from audit_native_decoding import check as decoder
 baseline=ROOT/'inputs/sites224.json'
 assert sha(baseline)=='309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878'
 original=c.tree(json.loads(baseline.read_text()));actual=c.tree(json.loads(a.source.read_text()))
 @cache
 def flat(t):return (t,) if c.leaf(t) else flat(t[0])+flat(t[1])
 def seq(xs):
  assert xs
  t=xs[-1]
  for n in reversed(xs[:-1]):t=(n,t)
  return t
 macrofile=HERE/'macro_data.json'
 macros={int(k):freeze(v) for k,v in json.loads(macrofile.read_text())['macros'].items()}
 asts=formulas();words=[postfix(t) for t in asts]
 assert all(execute(w)==t for w,t in zip(words,asts))
 programs=[seq([macros[m] for m in w]) for w in words]
 assert all(c.boundary(t)==(0,0,False) for t in programs)
 raw=HERE/'Dag230.v'
 assert sha(raw)=='7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf'
 dag={int(k):(x,y) for k,x,y in re.findall(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',raw.read_text())}
 @cache
 def expand(k):
  def edge(text):
   if text=='EHalt':return ('CH',None)
   op,n=text.split();n=int(n)
   if op=='ENode':return expand(n)
   return ({'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC'}[op],n)
  return tuple(edge(t) for t in dag[k])
 contracts={str(m):bisim(expand(m),macros[m]) for m in sorted(set(sum(words,[])))}
 oldflat=flat(original)
 assert oldflat[486:786]==flat(programs[0]),'Old rho7 interval differs'
 assert oldflat[2541:4618]==flat(programs[2]),'Old bundle interval differs'
 expected=oldflat[:486]+flat(programs[1])+oldflat[786:2541]+flat(programs[3])+oldflat[4618:]
 assert flat(actual)==expected,'Candidate has unexpected primitive source changes'
 def splice(tree,lo,hi,new):
  inserted=[];chunks=[]
  def visit(t,start):
   end=start+len(flat(t))
   if end<=lo or start>=hi:return t
   if lo<=start and end<=hi:
    assert c.boundary(t)==(0,0,False),('Splice segment is not closed',start,end)
    chunks.append([start,end])
    if start==lo:
     inserted.append(start);return new
    return None
   assert not c.leaf(t),'Splice endpoint cuts a leaf'
   left=visit(t[0],start);right=visit(t[1],start+len(flat(t[0])))
   return right if left is None else left if right is None else (left,right)
  result=visit(tree,0)
  assert inserted==[lo] and chunks[0][0]==lo and chunks[-1][1]==hi
  return result,chunks
 # Descending interval order preserves the baseline ordinal coordinates.
 reference,bundle_chunks=splice(original,2541,4618,programs[3])
 reference,row_chunks=splice(reference,486,786,programs[1])
 assert flat(reference)==expected
 ga,na=c.graph_arithmetic(c.sites(actual));gr,nr=c.graph_arithmetic(c.sites(reference))
 assert ga==c.graph_intervals(c.sites(actual)),'Candidate CFG resolvers disagree'
 assert gr==c.graph_intervals(c.sites(reference)),'Reference CFG resolvers disagree'
 assert ga==gr,'Candidate control targets differ from direct closed replacement'
 sides={'G':decoder(asts[1]),'seed_no_H_bundle':decoder(asts[3])}
 report=dict(status='INDEPENDENT_G_SEED_NO_H_EMITTER_AND_COMPLETE_CFG_PASS',
  source_sha256=sha(a.source),baseline_source_sha256=sha(baseline),macro_data_sha256=sha(macrofile),upstream_dag_sha256=sha(raw),
  expressions=dict(zip(['old_rho7','new_G','old_bundle','new_seed_bundle'],asts)),
  macro_words=dict(zip(['old_rho7','new_G','old_bundle','new_seed_bundle'],words)),
  old_source_leaves=len(oldflat),new_source_leaves=len(expected),metrics=c.metrics(actual),
  source_intervals=dict(old_row=[486,786],old_bundle=[2541,4618],new_row_leaves=len(flat(programs[1])),new_bundle_leaves=len(flat(programs[3]))),
  every_other_primitive_unchanged=True,closed_replacement_chunks=dict(row=row_chunks,bundle=bundle_chunks),
  all_register_macro_contracts=contracts,
  complete_CFG=dict(candidate_arithmetic_checks=na,reference_arithmetic_checks=nr,independent_resolvers_agree=True,all_guarded_targets_equal=True),
  decoder_constructor_sideconditions=sides,
  scope='All-natural formula equality and complete source binding only. Inherited arithmetic macro contracts linked by all-register finite bisimulations. Theory consistency, blank startup, and binary unbounded runtime are separate.')
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k] for k in ('status','source_sha256','old_source_leaves','new_source_leaves','metrics','source_intervals','complete_CFG')},indent=2))
if __name__=='__main__':main()
