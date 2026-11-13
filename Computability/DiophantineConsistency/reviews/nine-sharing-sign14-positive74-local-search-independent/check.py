#!/usr/bin/env python3
import collections,hashlib,json,math,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-local-search';src=root/'research/nine-sharing-sign14-positive74-circuit-retry01-check/src/DiophantineConsistency/Sign14Positive74Circuit.lean';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(src)=='cdd4117cd0b8af7eefbca2d53388068350970f78dba7e73dc9be2fe1b51f105d'
s=src.read_text().split('def gates : List Gate := [',1)[1].split(']\ndef parents',1)[0];raw=re.findall(r'⟨\.(add|sub|mul), \.(var|port|lit|reg) (-?\d+), \.(var|port|lit|reg) (-?\d+)⟩',s);assert len(raw)==74==s.count('⟨')
gates=[(op,(a,int(x)),(b,int(y))) for op,a,x,b,y in raw]
for i,(_,a,b) in enumerate(gates):
 for typ,j in (a,b):assert (typ!='reg' or 0<=j<i) and (typ!='var' or 0<=j<14) and (typ!='port' or 0<=j<4)
for root_idx,sq in zip((23,41,48,61,64),range(65,70)):
 assert gates[root_idx][0]=='sub' and gates[sq]==('mul',('reg',root_idx),('reg',root_idx))
 uses=[i for i,(_,a,b) in enumerate(gates) if a==('reg',root_idx) or b==('reg',root_idx)];assert uses==[sq]
# Adding twice and subtracting once in the positive control gives the original g73 and makes two gates live.
assert gates[73]==('add',('reg',72),('reg',69)) and gates[70:]==[('add',('reg',65),('reg',66)),('add',('reg',70),('reg',67)),('add',('reg',71),('reg',68)),('add',('reg',72),('reg',69))]
P=1000000007;assert P%4==3 and all(P%d for d in range(2,math.isqrt(P)+1));base=json.loads((p/'result.json').read_text());sign=json.loads((p/'sign-result.json').read_text())
for name,rec in (('search.py',base),('search_signs.py',sign)):
 script=p/name;assert rec['search_sha256']==sha(script) and rec['source_sha256']==sha(src) and rec['prime']==P and rec['samples']==3 and rec['seed']==0x46BE and rec['result']['original_live']==74 and not rec['result']['one_gate_candidates'] and not rec['result']['two_gate_candidates'];ct=rec['result']['counts'];assert ct['targets']==74 and ct['first_gates']==sum(2*n*n+n for n in range(31,105))==746845 and ct['second_queries']==sum(4*n-1 for n in range(31,105))==19906 and ct['sample_zero_nonconstant']==ct['targets_with_sample_zero']==0 and ct['square_root_queries']==200
 c=rec['positive_control'];assert c['original_live']==76 and len(c['one_gate_candidates'])==4 and len(c['two_gate_candidates'])==17
 text=script.read_text();assert "for signs in product((1, -1), repeat=SAMPLES)" in text and "for operation in ('+', '*')" in text and "pool.setdefault(evaluate('-', values[a], values[b])" in text and 'range(-4, 9)' in text and 'sample_zero_nonconstant' in text
assert sign['sign_reversal_candidates']==[] and 'for mask in range(1,32)' in (p/'search_signs.py').read_text()
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-circuit-retry01-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'bounded same-target one/two-gate prefilter, 31 root-sign variants and 76-gate positive control; no exact identity or global minimality claim'},indent=2))
