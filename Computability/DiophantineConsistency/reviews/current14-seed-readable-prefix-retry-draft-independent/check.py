#!/usr/bin/env python3
import ast,hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];old=root/'research/current14-seed-readable-prefix-draft/Current14QuotedPrefix.lean';p=root/'research/current14-seed-readable-prefix-retry-draft';q=p/'Current14QuotedPrefix.lean';sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest();assert sha(root/'equation.tex')=='94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635' and sha(old)=='a1e2a83f3486ce2af92ce165e72f6889f6e6456a0d14810ecee425d888d2a1d0' and sha(q)=='9f64e92fe3bee828ea7d640bc73252a8509635f2a3de544e9d4343654f138a79' and sha(p/'README.md')=='46c76b1df5acadbdd54c13dfa40f5834e438cc24c241f41e5aea4cb1abdf9001'
a=old.read_text();s=q.read_text();m=lambda text:ast.literal_eval(re.search(r'def quoted : List \(List String\) := (\[.*?\]\])\s*\n\ndef quotedExpr',text,re.S).group(1));assert m(a)==m(s) and a.split('def initial (p : Fin 4 → ℤ) : Env :=',1)[1].split('\ndef step',1)[0]==s.split('def initial (p : Fin 4 → ℤ) : Env :=',1)[1].split('\ndef allowedNames',1)[0]
expected=['b','q','C','X','Y','E','k','ell','c','a','H','Delta','D','R','tau','V','P','Q','S','U','W','Z','result'];raw=re.search(r'def allowedNames : List String :=\s*(\[.*?\])',s,re.S).group(1);allowed=ast.literal_eval(raw);assert allowed==expected==[x[0] for x in m(s)] and len(set(allowed))==23 and '+' not in allowed and '' not in allowed and 'if allowedNames.contains name then' in s and 'if (lookup name env).isSome then none else' in s
for z in ('theorem reject_reserved','theorem reject_empty','theorem reject_duplicate','theorem reject_unknown','theorem reject_trailing','theorem reject_exhausted','theorem reject_malformed'):
 assert len(re.findall(r'^'+z+r'\b',s,re.M))==1
for z in ('step (initial p) ["+", "=", "1"] = none','step (initial p) ["", "=", "1"] = none','step (("b", Expr.var 0) :: initial p) ["b", "=", "1"] = none','step (initial p) ["b", "=", "unknown"] = none','step (initial p) ["b", "=", "J", "F"] = none','decode (initial p) 0 ["J"] = none','step (initial p) ["b", "J"] = none'):assert z in s
assert 'rw [quotedExpr_eq]\n  all_goals rfl' in s and 'quotedExpr p = some (displayedExpr p)' in s and 'standardTheory ⊢ φ 🡘 ∼mappedNativeRefutation embedding' in s
# Source-only operational model checks controls and fixed quote; no Lean elaboration is inferred.
env={x:x for x in ['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma','beta','K','mu','omega','1','2','3','4']}
def decode(env,fuel,tokens):
 if fuel==0 or not tokens:return None
 op,*tail=tokens
 if op in ('+','-','*'):
  a=decode(env,fuel-1,tail)
  if a is None:return None
  b=decode(env,fuel-1,a[1])
  return None if b is None else ((op,a[0],b[0]),b[1])
 if op in ('sq','cube'):
  a=decode(env,fuel-1,tail);return None if a is None else ((op,a[0]),a[1])
 return (env[op],tail) if op in env else None
def step(env,line):
 if len(line)<2 or line[1]!='=' or line[0] not in allowed or line[0] in env:return None
 a=decode(env,64,line[2:]);return None if a is None or a[1] else dict(env,**{line[0]:a[0]})
assert all(step(env,x) is None for x in (['+','=','1'],['','=','1'],['b','=','unknown'],['b','=','J','F'],['b','J'])) and step(dict(env,b='x'),['b','=','1']) is None and decode(env,0,['J']) is None
for line in m(s):env=step(env,line);assert env is not None
assert 'result' in env
print(json.dumps({'status':'PASS_DELTA_SOURCE_REVIEW','allowed_names':len(allowed),'negative_controls':7,'scope':'source-only whitelist/control review; Lean and PDF byte semantics not established'},indent=2))
