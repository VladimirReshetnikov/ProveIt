#!/usr/bin/env python3
"""Exact planar adjacent-word algebra, not yet a physical row compiler."""
if not __debug__:raise RuntimeError('Assertions required')
import collections,hashlib,itertools,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
XOR=[('DUP',0),('DUP',2),('NAND',1),('DUP',1),('NAND',0),('NAND',1),('NAND',0)]
def at(prog,i):return[(op,k+i)for op,k in prog]
SWAP=[('DUP',0),('DUP',2)]+at(XOR,1)+[('DUP',1)]+at(XOR,0)+at(XOR,1)
def execute(word,prog):
 word=list(word);trace=[word[:]]
 for op,i in prog:
  assert 0<=i<len(word)
  if op=='DUP':word[i:i+1]=[word[i],word[i]]
  elif op=='NAND':
   assert i+1<len(word);word[i:i+2]=[1-word[i]*word[i+1]]
  else:raise ValueError(op)
  trace.append(word[:])
 return word,trace

def copy_to_end(i,width):
 assert 0<=i<width
 return[('DUP',i)]+sum([at(SWAP,j)for j in range(i+1,width)],[])
def append_nand(u,v,width):
 return copy_to_end(u,width)+copy_to_end(v,width+1)+[('NAND',width)]
def main():
 records=[]
 for name,prog,fn in [('XOR',XOR,lambda p,q:[p^q]),('SWAP',SWAP,lambda p,q:[q,p])]:
  cases=[]
  for p,q in itertools.product([0,1],repeat=2):
   out,t=execute([p,q],prog);assert out==fn(p,q)
   cases.append({'input':[p,q],'output':out,'trace':t})
  records.append({'name':name,'program':prog,'operations':dict(collections.Counter(op for op,i in prog)),
    'maximum_word_length':max(len(w)for c in cases for w in c['trace']),'cases':cases})
 copies=appends=0
 for width in range(1,7):
  for word in itertools.product([0,1],repeat=width):
   for i in range(width):
    p=copy_to_end(i,width);out,tr=execute(word,p);assert out==list(word)+[word[i]];copies+=1
   for u in range(width):
    for v in range(width):
     p=append_nand(u,v,width);out,tr=execute(word,p)
     assert out==list(word)+[1-word[u]*word[v]];appends+=1
 result={'status':'PASS_ABSTRACT_ADJACENT_BOOLEAN_WORD_PROGRAMS','scope':'No literal physical row realization asserted. Source NAND/COPY macros give prospective physical primitives, but delayed copies, displaced storage columns, and the complete row compiler remain obligations.',
  'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'programs':records,'copy_to_end_tests':copies,'append_nand_tests':appends,
  'general_proof':'DUP duplicates a selected token. Each adjacent SWAP exchanges its two tokens and preserves surrounding tokens. Thus moving the extra duplicate to the right end preserves the original word. Two such moves followed by NAND append one circuit gate without changing prior wire values. Induction on a finite NAND DAG compiles every Boolean circuit into this adjacent rewrite system.',
  'resources_per_swap':{'DUP':12,'NAND':12,'maximum_word_length_for_two_input_program':6},
  'copy_to_end_operation_count':'1+24*(width-i-1)',
  'append_nand_operation_count':'3+24*(2*width-u-v-1)',
  'max_live_width_for_appending_one_gate':'at most width+6'}
 (ROOT/'receipts/boolean_word_programs.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'copy_tests':copies,'append_tests':appends,'SWAP_operations':len(SWAP)}))
if __name__=='__main__':main()
