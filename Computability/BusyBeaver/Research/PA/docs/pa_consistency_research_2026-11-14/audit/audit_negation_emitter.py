#!/usr/bin/env python3
"""Audit AX grammar words after any of four conditional negation peepholes.

The replacements use a move into register6, eight final accumulator increments,
or register7 preloads. All restore to push/incT/cons before the full free-algebra
audit. The clean-scratch condition and physical binding are separate gates.
"""
from pathlib import Path
import argparse,json,hashlib
import audit_sevenhead_emitter as e
INC=('leaf','inc',1)
INC7=('leaf','inc',7)
CLOSE=('leaf','breakTo',1)
IDS={'node58':0,'node55':1,'node65':2,INC:3,'node72':4,'node75':5,'node70':6,'node49':7,'node142':8,'node150':9,CLOSE:10}
def require(v,msg):
 if not v:raise ValueError(msg)
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x

def grammar_word(cfg):
 rules=cfg['rules'];visiting=set();memo={}
 def expand(n):
  n=freeze(n)
  if n=='node60':return [INC,INC]
  if n=='node61':return [INC]*4
  if n not in rules:return [n]
  require(n not in visiting,'cyclic grammar')
  if n in memo:return memo[n]
  visiting.add(n);ch=rules[n];require(len(ch)==2,'nonbinary grammar')
  result=expand(ch[0])+expand(ch[1]);visiting.remove(n);memo[n]=result;return result
 return expand(cfg['root'])

def integer_grammar_word(cfg):
 symbols=list(map(freeze,e.SYMBOLS))+['node37','node64','node61',INC7];words=[]
 for i,pair in enumerate(cfg['rules']):
  require(isinstance(pair,list)and len(pair)==2,'nonbinary integer grammar')
  word=[]
  for n in pair:
   require(isinstance(n,int),'noninteger grammar reference')
   if n<0:
    k=-1-n;require(0<=k<len(symbols),'integer terminal range')
    word+=([INC]*4 if symbols[k]=='node61'else[symbols[k]])
   else:
    require(n<i,'integer grammar is not topological');word+=words[n]
  require(len(word)<=2000,'unexpected grammar expansion');words.append(word)
 root=cfg['root'];require(isinstance(root,int)and 0<=root<len(words),'integer grammar root')
 return words[root]

def normalize_word(raw):
 restored=[];replacements=[];j=0
 while j<len(raw):
  if raw[j]==INC7:
   if raw[j:j+3]==[INC7,INC7,'node64']:
    kind='preload2_pair';number=3;size=3
   else:
    require(raw[j:j+6]==[INC7,'node64']+[INC]*4,'incomplete register7-preload negation peephole')
    kind='preload1_pair_plus4';number=4;size=6
   replacements.append({'expanded_macro_offset':j,'restored_macro_offset':len(restored),'kind':kind,'kind_number':number})
   restored.extend([7,3,2]);j+=size
  elif raw[j]=='node37':
   require(raw[j:j+3]==['node37',INC,'node64'],'incomplete drain/pair negation peephole')
   replacements.append({'expanded_macro_offset':j,'restored_macro_offset':len(restored),'kind':'drain_inc_pair','kind_number':1})
   restored.extend([7,3,2]);j+=3
  elif raw[j]=='node64':
   require(raw[j+1:j+9]==[INC]*8,'incomplete pair/plus8 negation peephole')
   replacements.append({'expanded_macro_offset':j,'restored_macro_offset':len(restored),'kind':'pair_plus8','kind_number':2})
   restored.extend([7,3,2]);j+=9
  else:
   require(raw[j]in IDS,'unexpected macro outside a negation peephole');restored.append(IDS[raw[j]]);j+=1
 return restored,replacements

def check_mask(witness,restored,replacements,encoding):
 byoffset={x['restored_macro_offset']:x['kind_number']for x in replacements}
 found=[];j=0
 while j+2<len(restored):
  if restored[j:j+3]==[7,3,2]:found.append(byoffset.get(j,0));j+=3
  else:j+=1
 require(len(found)==8,'expected eight negation occurrences')
 mask=witness['negmask'];require(isinstance(mask,int)and mask>=0,'invalid negation mask')
 bits={'binary':1,'ternary':2,'five':3}[encoding]
 require(mask>>(bits*8)==0,'negation mask exceeds eight occurrences')
 declared=[(mask>>(bits*j))&((1<<bits)-1)for j in range(8)]
 require(all(k<{'binary':2,'ternary':3,'five':5}[encoding]for k in declared),'invalid negation kind')
 require(found==declared,'negation grammar does not match declared mask')
 return found

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--inputs',type=Path,required=True)
 src=ap.add_mutually_exclusive_group(required=True);src.add_argument('--grammar',type=Path);src.add_argument('--witness',type=Path)
 ap.add_argument('--mask-encoding',choices=['binary','ternary','five'],default='ternary');ap.add_argument('--family',choices=['separate','diagonal'],default='separate');ap.add_argument('--out',type=Path);args=ap.parse_args()
 inp=json.loads(args.inputs.read_text());e.check_inputs(inp)
 source=args.grammar or args.witness;cfg=json.loads(source.read_text())
 raw=grammar_word(cfg)if args.grammar else integer_grammar_word(cfg)
 restored,replacements=normalize_word(raw)
 witness_audit=None;mask_audit=None
 if args.witness:
  require(args.family=='separate','joint witness uses the separated seven-head family')
  witness_audit=e.check_word_witness(inp,cfg,restored)
  mask_audit=check_mask(cfg,restored,replacements,args.mask_encoding)
 base=inp['prefix']+sum([inp['heads'][0][j][0]for j in range(7)],[])+inp['gate'][0][0]+inp['suffix']
 if args.family=='diagonal':base=base[:184]+[2]+base[184:]
 if args.grammar:require(restored==base,'restored emitter differs from the exact declared baseline family')
 rho,a,d,h,stack,fields=e.prefix_state();values=e.heads(a,d,h)
 top=e.gate_value(a,d,h,0)
 if args.family=='diagonal':
  # The original outer gate is N(I(gamma, I(v,Q))). Its inner implication
  # is exactly the argument negated in separated top.
  require(top[0]=='im'and top[2]==e.ONE,'separated gate form')
  top=e.N(e.I(values[6],top[1]));values=values[:6]
 expected=(top,a,d,h,stack+[rho]+values,[])
 if args.grammar:require(e.execute(restored[:-3])==expected,'restored complete formula/stack identity')
 result={'grammar_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'family':args.family,
  'macro_tokens_after_increment_expansion':len(raw),'peephole_count':len(replacements),'peepholes':replacements,
  'restored_exact_baseline_word':args.grammar is not None,'restored_free_algebra_stack_contract':True,
  'conditional_arithmetic_identities':{'drain_inc_pair':'The 20-site replacement equals the old 47-site block when incoming source r7=0. As a formula negation macro, r6=0 is also needed.',
   'pair_plus8':'With r6=r7=0, node64 then eight increments maps t to 4*p(0,t)+8 = 4*p(t,1). Both expressions are 2*t^2+6*t+8. It preserves the encoded stack.',
   'preload2_pair':'With r6=r7=0, two INC7 operations followed by node64 map t to 4*(2+p(0,t)) = 4*p(t,1). The raw core contract is (T,S,Y)=(t,s,y) -> (4*(y+p(s,t)),0,0).',
   'preload1_pair_plus4':'With r6=r7=0, INC7 followed by node64 and four accumulator increments maps t to 4*(1+p(0,t))+4 = 4*p(t,1).'},
  'required_unproved_here':'Bind the clean-scratch macro contracts to every replacement entry in this exact changed source, establishing r6=r7=0. The upstream AXMacro.registers model sets both to zero, and AXMacroSound preserves clean macro stores; this checker does not bind those contracts or prove any tape simulation.',
  'no_new_logical_schema':True}
 if witness_audit is not None:result['joint_witness']=witness_audit;result['negation_kinds_by_occurrence']=mask_audit
 if args.out:args.out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
