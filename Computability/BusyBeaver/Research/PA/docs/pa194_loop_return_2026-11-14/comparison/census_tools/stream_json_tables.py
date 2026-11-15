"""Bounded-retention JSON tree walker for explicit TM shapes.
Retains only subtrees that can serve as transition rows, actions, paired
actions, row records, or whole tables. All other children are traversed and
discarded. The lexical parser uses the standard JSON decoder for scalars.
"""
import json,re
import json_inventory as js
BAD=object()
FIELDS={'state','source','q','current_state','from','read','symbol','read_bit','read_symbol','b','write','write_bit','write_symbol','w','direction','move','dir','d','next','target','next_state','to','t'}
KEY=re.compile(r'\(?\s*\d+\s*[,;:]\s*[01]\s*\)?\Z')
WS=re.compile(r'\s*')
def row5(x):return isinstance(x,list) and len(x)==5 and js.integer(x[0]) and x[1] in (0,1) and x[2] in (0,1) and js.direction(x[3]) and js.integer(x[4])
def shapes(x):
 r=set()
 if row5(x):r.add('row')
 if isinstance(x,list) and len(x)==2 and all(js.action(a) for a in x):r.add('pair')
 if js.action(x):r.add('action')
 if js.rowrecord(x) is not None:r.add('record')
 return r

def scan(data,emit):
 text=data.decode('utf-8');decoder=json.JSONDecoder();n=len(text)
 def ws(i):return WS.match(text,i).end()
 def value(i,path):
  i=ws(i)
  if i>=n:raise ValueError('unexpected end')
  ch=text[i]
  if ch=='[':
   i=ws(i+1);items=[];keep=True;kind=None;forms=None;index=0
   if i<n and text[i]==']':return [],i+1
   while True:
    child,i=value(i,path+'/'+str(index));index+=1
    if keep:
     if child is BAD:keep=False;items=[]
     else:
      child_kind='compound' if isinstance(child,(dict,list)) else 'primitive'
      if kind is None:kind=child_kind
      if kind!=child_kind:keep=False;items=[]
      elif kind=='primitive':
       items.append(child)
       if len(items)>5:keep=False;items=[]
      else:
       sh=shapes(child);forms=sh if forms is None else forms&sh
       if not forms:keep=False;items=[]
       else:items.append(child)
    i=ws(i)
    if text[i]==']':i+=1;break
    if text[i]!=',':raise ValueError('expected comma at '+str(i))
    i=ws(i+1)
   result=items if keep else BAD
  elif ch=='{':
   i=ws(i+1);numbered={};row={};full=True
   if i<n and text[i]=='}':return {},i+1
   while True:
    if text[i]!='"':raise ValueError('expected object key')
    key,i=decoder.raw_decode(text,i);i=ws(i)
    if text[i]!=':':raise ValueError('expected colon')
    child,i=value(i+1,path+'/'+str(key))
    if full:
     if not (key.isdigit() or KEY.fullmatch(key)) or child is BAD:full=False;numbered={}
     else:numbered[key]=child
    if key in FIELDS and child is not BAD and not isinstance(child,(dict,list)):row[key]=child
    i=ws(i)
    if text[i]=='}':i+=1;break
    if text[i]!=',':raise ValueError('expected comma')
    i=ws(i+1)
   if full:result=numbered
   elif js.rowrecord(row) is not None:result=row
   else:result=BAD
  else:
   result,i=decoder.raw_decode(text,i)
  if result is not BAD:
   try:tm=js.decode(result)
   except (ValueError,TypeError,KeyError):tm=None
   if tm and len(tm[1])>=2:emit(path,tm)
  return result,i
 _,i=value(0,'$')
 if ws(i)!=n:raise ValueError('trailing JSON input')
