#!/usr/bin/env python3
"""Check the exact K224 -> reordered-SYM source calibration.

No grammar optimizer is imported. The candidate may have arbitrary closed
reassociation, but must have the exact fine-instruction graph of the explicit
reference assembled here. Register macro equivalence is checked against the
pinned Dag230 source by finite all-register local bisimulation.
"""
from pathlib import Path
from functools import cache,reduce
import argparse,json,hashlib,re,sys

def req(p,m):
 if not p:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def seq(parts):
 req(bool(parts),'emptysequence');return reduce(lambda a,b:(a,b),parts)
def at(n,p):
 for b in p:n=n[int(b)]
 return n
def put(n,p,x):
 if not p:return x
 b=int(p[0]);v=list(n);v[b]=put(v[b],p[1:],x);return tuple(v)

PREFIX_PATHS=['111010010010','11101001001100','111010010011010','1110100100110110','11101001001010','11101001001101110']
SUFFIX_PATHS=['111010010011001000','111010010011101']
AX_PATH='11101001001'
PINS={'source':'309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878','table':'f886dd8d11e9705c5315140f68d5ae2f26c80afb015e08074c7e3da1414fa37f','dag':'7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf'}

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--baseline-root',type=Path,required=True,help='K224_Construction_2026-10-20root')
 p.add_argument('--parent-root',type=Path,required=True,help='K225portable directory')
 p.add_argument('--candidate-source',type=Path,required=True)
 p.add_argument('--output',type=Path,required=True)
 args=p.parse_args()
 sys.path.insert(0,str(args.parent_root/'baseline226/verification'));import reconstruct227 as c
 sys.path.insert(0,str(args.baseline_root/'portable/verification'));import construct_rel225 as b
 from local_bisimulation import check as bisim
 src=args.baseline_root/'portable/machine/results/sites.json';tab=args.baseline_root/'portable/machine/results/candidate224.k.tm';dagfile=args.parent_root/'baseline226/vendor/k230-rocq/coq/prog/Dag230.v'
 req(sha(src)==PINS['source'],'baseline source pin');req(sha(tab)==PINS['table'],'baseline tablepin');req(sha(dagfile)==PINS['dag'],'Dag230pin')
 old=c.tree(json.loads(src.read_text()));candidate=c.tree(json.loads(args.candidate_source.read_text()));table=b.read_table(tab);qs,ps=b.decoder_map(c,table,old)
 macros={166:b.sole(qs,98),121:b.sole(qs,12),168:b.sole(qs,166),119:b.sole(qs,90),180:b.sole(qs,86),183:b.sole(qs,180)}
 macros[181]=next(n for n in qs[150]if len(c.sites(n))==28)
 macros[182]=(macros[119],(('CI',1),(('CI',1),('CI',1))))
 req(all(c.boundary(n)==(0,0,False)for n in macros.values()),'unclosedmacro')
 nodes={int(q):(x,y)for q,x,y in re.findall(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',dagfile.read_text())}
 @cache
 def expand(q):
  def ed(s):
   if s=='EHalt':return 'CH',None
   k,n=s.split();n=int(n)
   return expand(n)if k=='ENode'else({'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC'}[k],n)
  return tuple(map(ed,nodes[q]))
 macro_proofs={str(q):bisim(expand(q),n)for q,n in macros.items()}
 @cache
 def word(n):return(n,)if c.leaf(n)else word(n[0])+word(n[1])
 I=lambda x,y:('I',x,y);R=lambda x,y:('R',x,y);E=lambda x,y:('E',x,y);Q=lambda x,y:('Q',x,y);X=lambda x,y:('X',x,y)
 a,bb,cc='a','b','c'
 rows=[('rho6c',I(X(a,Q(a,cc)),cc)),('SYMbc',I(E(bb,cc),E(cc,bb))),('rho5',I(E(cc,a),I(R(cc,bb),R(a,bb)))),('rho4',I(Q(a,Q(bb,cc)),Q(bb,Q(a,cc)))),('rho3',I(E(a,bb),I(R(cc,a),R(cc,bb)))),('rho2',I(Q(a,I(bb,cc)),I(Q(a,bb),Q(a,cc)))),('rho1',X(a,E(a,bb)))]
 def emit(f):
  if isinstance(f,str):return({'a':166,'b':121,'c':168}[f],)
  return emit(f[1])+emit(f[2])+({'I':119,'R':181,'E':182,'Q':180,'X':183}[f[0]],)
 def symbolic(ms):
  top='older_top';stack=['older_stack']
  for m in ms:
   if m in(166,121,168):stack.append(top);top={166:'a',121:'b',168:'c'}[m]
   else:top=({119:I,181:R,182:E,180:Q,183:X}[m])(stack.pop(),top)
  req(stack==['older_stack','older_top'],'badrowstackcontract');return top
 for name,f in rows:req(symbolic(emit(f))==f,'badformulaemitter '+name)
 prefix=[at(old,p)for p in PREFIX_PATHS];suffix=[at(old,p)for p in SUFFIX_PATHS]
 req(all(c.boundary(n)==(0,0,False)for n in prefix+suffix),'unclosedfixedpiece')
 req(sum(map(lambda n:len(word(n)),prefix))==446,'prefixextent')
 req(sum(map(lambda n:len(word(n)),suffix))==2111,'suffixextent')
 reference=put(old,AX_PATH,(seq(prefix+[macros[m]for name,f in rows for m in emit(f)]+suffix),('CB',1)))
 rr=c.sites(reference);cr=c.sites(candidate)
 req(word(reference)==word(candidate),'candidatefineword differsfromexplicitSYMreference')
 rg,rc=c.graph_arithmetic(rr);cg,ccheck=c.graph_arithmetic(cr)
 req(rg==cg==c.graph_intervals(rr)==c.graph_intervals(cr),'guardedCFG differs')
 req(len(cr)==4690,'expected4690 fineinstructions')
 # Exact unchangedoldprogrambefore/aftertheAXsubtree.
 old_ax=at(old,AX_PATH);cand_ax=at(candidate,AX_PATH)
 req(put(old,AX_PATH,cand_ax)==candidate,'changewasnotconfinedtoAXsubtree')
 old_axword=word(old_ax);new_axword=word(cand_ax)
 req(old_axword[:446]==new_axword[:446],'Lukasiewicz/GENprefixchanged')
 req(old_axword[-2112:]==new_axword[-2112:],'K/gate/tailsuffixchanged')
 result={'status':'EXACT_SYMMETRY_SOURCE_CALIBRATION_PASS','candidate_source_sha256':sha(args.candidate_source),'baseline_pins':PINS,'fine_instructions':len(cr),'guarded_cases':sum(2 if op=='CD'else 1 for pc,op,arg in cr),'changed_logical_rows':[{'name':name,'formula':f,'macro_word':emit(f)}for name,f in rows],'retained':['Original GEN and Lukasiewicz sourceprefix','Original K224fusedK/privateRelhelper/gatesource suffix','OriginalproofenumeratoroutsideAX','EightlogicalrowsplusGENandK'],'register_macro_proofs':macro_proofs,'independent_CFG_checks':{'reference':rc,'candidate':ccheck},'seed_contract':'Unchangedregisterfile(3,0,0,0,3,0,0,0,0):nextproof=3,topwff=0,wffstack=0,axiomcode=0,param1=3,param2=0,scratch1=0,scratch2=0,prooflist=0. The3sarecounters,notinitialequalityaxioms. Seed230_sound usesT_true,T_true,good_0; theunchangedpropositionalbasisprovidesT_true.','scope':'Exactsource arithmetic/CFG andsymbolicrowcontracts; ordinarylogicalequiconsistencyanduniversalbinaryruntimeareseparateobligations.'}
 args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k]for k in('status','candidate_source_sha256','fine_instructions','guarded_cases')},indent=2))
if __name__=='__main__':main()
