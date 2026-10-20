#!/usr/bin/env python3
"""Reduce recorded full symbolic return entries using owned native symbolic engine."""
import json,collections,hashlib
from pathlib import Path
import symbolic_contexts as own
D=Path(__file__).resolve().parent;ROOT=D.parent
records=json.loads((ROOT/'research218_encoding/RETURN_FULL_CONTRACTS.json').read_text())
m={int(k):v for k,v in json.loads((ROOT/'research218_encoding/NATIVE_TO_LEGACY.json').read_text()).items()};inverse={v:k for k,v in m.items()}
tm=own.readtm(ROOT/'latest219_baseline/candidate-k219/k219.native.tm')
def translate(xs):
 out=[]
 for a in xs:
  if a[0]=='run':out.append(('r',a[1],tuple(a[2])))
  elif a[0]=='list':assert a[2]=='spare_tail';out.append(('l',a[1],a[3]))
  else:out.append(tuple(a))
 return out
def leftbits(xs):
 bits=''
 for a in xs:
  if a==own.B:return bits
  assert a[0]=='r' and all(v==0 for v in a[2][1:]),a
  bits+=str(a[1])*a[2][0]
 raise ValueError('no blank exterior')
counts=collections.Counter();details=[];selected=[]
for rec in records:
 q=inverse[rec['state']];assert q in [103,113]
 t=own.Tape(q,translate(rec['left']),translate(rec['right']),rec['direction']);t.key()
 ownrow=t.advance(tm,{})
 assert t.q==302 and t.d==-1
 t.key();word=leftbits(t.L)
 # The entire left half is fixed finite bits plus zero exterior: data-independent.
 # Its first a ones are erased, one zero crossed, then b ones cleared by carry.
 a=len(word)-len(word.lstrip('1'));tail=word[a:]
 assert tail.startswith('0')
 tail=tail[1:];b=len(tail)-len(tail.lstrip('1'))
 pair=(q,a,b);counts[pair]+=rec['multiplicity']
 details.append({'source_index':rec['site'][0],'source_site':rec['site'][1],'entry_native':q,'entry_direction':rec['direction'],'302_left_word_nearest_first':word,'erase_ones':a,'carry_ones':b})
 if q==103 or a>0: selected.append(rec)
report={'status':'ALL1432_REDUCED_RETURN_WORDS_CHECKED','input_sha256':hashlib.sha256((ROOT/'research218_encoding/RETURN_FULL_CONTRACTS.json').read_bytes()).hexdigest(),'groups':[{'incoming_state':q,'erase_ones':a,'carry_ones':b,'count':n} for (q,a,b),n in sorted(counts.items())],'total':sum(counts.values()),'all_left_words_constant':True,'right_context':'May depend on gap,registers,sparehead,and arbitrary finite sparetail; untouched by302->4 prefix operation','scope':'Checks the recorded symbolic premises and one incoming literal step,not independent derivation of every1432 entry from dispatcher. Independent representative derivation is separate.'}
(D/'RETURN_WORD_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n');(D/'RETURN_WORDS.json').write_text(json.dumps(details,indent=2)+'\n')
print(json.dumps(report,indent=2))
