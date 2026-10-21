#!/usr/bin/env python3
"""Portable finite corroboration and source pin checks, not a kernel proof."""
from pathlib import Path
from math import isqrt
from itertools import product
import hashlib,json,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
D=Path(__file__).resolve().parent
for f,h in json.loads((D/'INPUT_PINS.json').read_text()).items():
 assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f

def P(a,b):return (a+b)*(a+b+1)//2+b
def unP(n):
 s=(isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2
 return s-b,b

def pack(c,r,old=False):
 if c[0]=='R':return P(0,r)
 if c[0]=='D':assert old;return P(1,r)
 if c[0]=='M':return P(2 if old else 1,P(c[1],r))
 _,a,x,y=c;return P(a+(3 if old else 2),P(y,P(x,r)))
def decode(n,old=False):
 a,r=unP(n)
 if a==0:return ('R',),r
 if old and a==1:return ('D',),r
 if a==(2 if old else 1):
  x,r=unP(r);return ('M',x),r
 y,r=unP(r);x,r=unP(r);return ('A',a-(3 if old else 2),x,y),r

def enc(word,old=False):
 assert word,'No empty-word encoding is used'
 n=pack(word[-1],0,old)
 for c in reversed(word[:-1]):n=pack(c,n+1,old)
 return n

def word(n,old=False):
 out=[]
 while True:
  c,r=decode(n,old);assert r<=n;out.append(c)
  if r==0:return tuple(out)
  assert r-1<n;n=r-1

counts={}
for old in(False,True):
 alphabet=[('R',),('M',0),('M',2),('A',0,0,0),('A',2,1,3)]
 if old:alphabet.insert(1,('D',))
 nw=0;np=0;maxbits=0
 for c in alphabet:
  for r in range(100):
   n=pack(c,r,old);assert decode(n,old)==(c,r)and r<=n;np+=1
 for size in range(1,5):
  for w in product(alphabet,repeat=size):
   n=enc(w,old);assert n>=size-1 and word(n,old)==w
   assert len(word(n,old))<=n+1
   if w[0][0]=='A':assert n>=1
   nw+=1;maxbits=max(maxbits,n.bit_length())
 counts['EnumPerm'if old else'common_NIP']={'word_roundtrips':nw,'pack_roundtrips':np,'max_code_bit_length':maxbits}
assert [enc((('R',),)*n)for n in range(1,4)]==[0,2,9]
# Negative control: omitting the positive wrapper collapses two zero opcodes.
wrong=P(0,P(0,0));assert wrong==0 and wrong<2-1
# Exhaust all total Option-valued two-command transition systems on three stores.
# This checks the prefix algebra, not any arithmetic calculus or physical machine.
states=range(3);vals=(None,0,1,2);words=[p for k in range(1,4)for p in product(range(2),repeat=k)]
prefixes=[p for k in range(3)for p in product(range(2),repeat=k)]
systems=universal=prefixchecks=earlyprefix=0
for flat in product(vals,repeat=6):
 def run(w,s):
  for c in w:
   s=flat[c*3+s]
   if s is None:return None
  return s
 systems+=1
 for u in words:
  if not all(run(u,s)is None for s in states):continue
  universal+=1
  for p in prefixes:
   for s in states:
    assert run(p+u,s)is None
    prefixchecks+=1
    earlyprefix+=run(p,s)is None
source=(D/'inputs/EnumPerm.lean').read_text();lines=source.splitlines()
required=['decode_pack','decode_le','encL','cexec_append','exec_list','drain','reach','program_none','encL_ge','complete','halts_iff']
loc={}
for name in required:
 loc[name]=next(i+1 for i,l in enumerate(lines)if l.startswith(('theorem '+name+' ','def '+name+' ')))
assert loc['complete']==530 and loc['halts_iff']==542
assert '| c, c\' :: cs => pack c (encL c\' cs + 1)' in source
assert 'if s.pl = 0 then (s.np, s.np + 1) else (s.pl - 1, s.np)' in source
assert 'length at most n+1' in (D/'inputs/common_nip_CREDIT_PROOF.md').read_text()
result={'status':'LENGTH_PADDING_CORROBORATION_PASS','codec_checks':counts,
 'zero_opcode_codes':[0,2,9],'missing_positive_wrapper_rejected':True,
 'finite_option_systems':systems,'universally_halting_test_words':universal,
 'prefix_state_checks':prefixchecks,'early_halting_prefix_cases':earlyprefix,
 'source_declaration_lines':loc,'common_NIP_STORE_command_count':10,
 'common_NIP_universal_word_length':'22 + length(B_1)',
 'common_NIP_existing_length_bound':'length(W(n)) <= n+1',
 'common_NIP_fixed_cutoff':1,'generic_length_lower_bound':21,
 'minimal_actual_cutoff_argument':'First opcode2 implies a positive fresh code',
 'validation':'Finite corroboration and source/hash audit only. All-natural proof is LENGTH_PADDING.md; Lean adapter was not compiled. No sealed machine or proof artifact changed.'}
print(json.dumps(result,indent=2))
