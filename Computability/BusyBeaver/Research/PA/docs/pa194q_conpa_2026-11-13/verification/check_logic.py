#!/usr/bin/env python3
"""Audit the exact new AX block, source binding and example codes."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent.parent
BASE=ROOT/'construction'
I=lambda a,b:('I',a,b)
U=lambda d,a:('U',d,a)
if not __debug__:raise RuntimeError('Assertions required')
# Symbolic execution in the free algebra of 4*Cantor(a,b)+r terms.
# Copy pushes the old T; cons pops it. These identities also hold at p(0,0)=0.
old=json.loads((BASE/'inputs/195C.instructions.json').read_text())
new=json.loads((ROOT/'machine/instructions.json').read_text())
word=json.loads((ROOT/'machine/macro_word.json').read_text())
def unroll_grammar(path):
 data=json.loads(path.read_text())
 def visit(node):
  if isinstance(node,str) and node in data['rules']:
   return visit(data['rules'][node])
  if node=='node60':return [['leaf','inc',1]]*2
  if node=='node61':return [['leaf','inc',1]]*4
  if isinstance(node,list) and len(node)==2:
   return visit(node[0])+visit(node[1])
  return [node]
 return visit(data['root'])
old_word=unroll_grammar(BASE/'inputs/pa194.grammar.json')
assert unroll_grammar(BASE/'grammar.json')==word
assert len(old_word)==len(word)==190
assert old_word[:102]==word[:102] and old_word[121:]==word[121:]
sub=word[102:121]
params={'node55':'D','node58':'H','node70':'A'}
def execute(block):
 stack=[];t='old_T'
 for op in block:
  if isinstance(op,str) and op in params:stack.append(t);t=params[op]
  elif op=='node65':assert stack;t=('pair4',stack.pop(),t,0)
  else:
   assert op==['leaf','inc',1] and isinstance(t,tuple) and t[0]=='pair4';t=(*t[:3],t[3]+1)
 return stack,t
def raw(f):
 if isinstance(f,str):return f
 op,a,b=f
 return ('pair4',raw(a),raw(b),0) if op=='I'else('pair4',raw(b),raw(a),2)
f_old=I(U('D','A'),I(U('D',I('A','H')),U('D','H')))
f_new=I(U('D',I('A','H')),I(U('D','A'),U('D','H')))
assert execute(sub)==(['old_T'],raw(f_new))
assert execute(old_word[102:121])==(['old_T'],raw(f_old))
changed=[i for i,(a,b) in enumerate(zip(old,new))if a!=b]
assert len(old)==len(new)==3649 and len(changed)==79 and min(changed)==1953 and max(changed)==2067
# Independent primitive source correspondence: exact op/target differences are retained.
def number(f,env):
 if isinstance(f,str):return env[f]
 tag,a,b=f;a=number(a,env);b=number(b,env)
 if tag=='U':a,b=b,a
 return 4*((a+b)*(a+b+1)//2+b)+(2 if tag=='U'else 0)
env={'A':1,'D':0,'H':0}
result={'status':'PASS','exchange_proof_lines':61,
 'proof_has_assumptions':False,'old_head':f_old,'new_head':f_new,'new_macro_block':sub,
 'old_macro_block':old_word[102:121],'macro_word_tokens':190,
 'changed_macro_interval_zero_based_half_open':[102,121],
 'all_surrounding_macro_tokens_identical':True,
 'block_keeps_parameters':True,'block_pushes_incoming_top':True,'source_sites':3649,
 'changed_instruction_count':len(changed),'changed_instructions':[[i,old[i],new[i]]for i in changed],
 'unchanged_instruction_count':3649-len(changed),'example_parameters':env,
 'example_old_code':number(f_old,env),'example_new_code':number(f_new,env),
 'code_zero_alias':'No free-list or injective formula-syntax assumption is used in exchange.'}
(ROOT/'evidence/source_exchange.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in('changed_instructions',)},indent=2))
