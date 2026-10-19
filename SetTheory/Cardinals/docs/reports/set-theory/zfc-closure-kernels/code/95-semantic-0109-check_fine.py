#!/usr/bin/env python3
"""Check a frozen fine-word grammar's finite syntactic obligations only."""
import argparse,json
from functools import cache
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('result',type=Path);p.add_argument('--emit',type=Path);a=p.parse_args()
d=json.loads(a.input.read_text());r=json.loads(a.result.read_text());g={w:(x,y)for w,x,y in r['rules']};dictionary=d['dictionary'];assert len(g)==len(r['rules'])==r['private_rules']
def free(w,bit):return w in dictionary and dictionary[w]['mask']&(1<<bit)
for w,(x,y)in g.items():
 assert w==x+y
 for bit,v in enumerate((x,y)):assert free(v,bit)or v in g
seen=set()
def visit(w):
 if w in seen:return
 seen.add(w)
 for bit,v in enumerate(g[w]):
  if not free(v,bit):visit(v)
visit(d['ax']);assert seen==set(g)
def join(x,y):return[x[0]+1,max(x[0]+1,x[1],y[1]),max(x[2],y[2])+1]
@cache
def prop(w):return join(*[dictionary[v]['properties']if free(v,bit)else prop(v)for bit,v in enumerate(g[w])])
assert prop(d['ax'])==r['properties'];assert prop(d['ax'])[0]<=d['ax_properties'][0];assert prop(d['ax'])[1]<=6;assert prop(d['ax'])[2]<=d['ax_properties'][2]+64-d['full_properties'][2]
def expand(w):return ''.join(d['atom'][c]for c in w)
emitted={w:tuple(row)for w,row in d['fixed'].items()}
@cache
def spell(w):
 row=tuple(dictionary[v]['spelling']if free(v,bit)else spell(v)for bit,v in enumerate(g[w]));s=''.join(row);assert expand(s)==w
 if s in emitted:assert emitted[s]==row
 emitted[s]=row;return s
newax=spell(d['ax']);assert len(emitted)==len(d['fixed'])+len(g)
result=dict(status='PASS_FINITE_FINE_GRAMMAR_ONLY',fixed_rules=len(d['fixed']),private_rules=len(g),total_grammar_rules=len(emitted),AX_fine_length=len(d['ax']),AX_coarse_calls=len(newax),AX_properties=prop(d['ax']),all_rules_reachable=True,exact_fine_AX_equality=expand(newax)==expand(d['ax_word']),unbounded_binary_simulation=False)
if a.emit:
 candidate=dict(d['seed']);candidate.update(rules_count=len(emitted),rules=[[w,*row]for w,row in sorted(emitted.items())],original_AX_word=d['ax_word'],modified_AX_word=newax,roots=sorted((set(candidate['roots'])-{d['ax_word']})|{newax}),properties=[],source='Search result, not a certified binary TM')
 a.emit.write_text(json.dumps(candidate,indent=2)+'\n')
print(json.dumps(result,indent=2))
