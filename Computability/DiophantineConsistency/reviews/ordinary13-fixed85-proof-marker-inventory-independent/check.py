from pathlib import Path
from hashlib import sha256
from collections import Counter
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-fixed85-proof-escape-inventory')
P=Path('research/ordinary13-fixed85-source-selection-plan/selection.json')
inv=json.loads((D/'inventory.json').read_text());receipt=json.loads((D/'receipt.json').read_text())
assert sha256((D/'scan.py').read_bytes()).hexdigest()==receipt['scanner_sha256']
assert sha256((D/'inventory.json').read_bytes()).hexdigest()==receipt['inventory_sha256']
assert sha256(P.read_bytes()).hexdigest()==inv['selection_sha256']
mods=json.loads(P.read_text())['selected_modules'];assert len(mods)==1354
names=('sorry','admit','axiom','unsafe','sorryAx','native_decide','run_tac','implemented_by','opaque','partial','postulate','ofReduceBool')
tokens=re.compile(r"(?<![A-Za-z0-9_'])(?:"+'|'.join(names)+r")(?![A-Za-z0-9_'])")
choice=re.compile(r'(?<![A-Za-z0-9_])Classical\.choice(?![A-Za-z0-9_])')
constant=re.compile(r'(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*constant\s+[A-Za-z_]')
# Independent finite-state blanking pass. It intentionally models only the
# packet's documented subset of Lean lexical forms; it is not a Lean lexer.
def mask(src):
 out=[];comments=[];strings=[];i=0
 def blank(piece):return ''.join('\n' if c=='\n' else ' ' for c in piece)
 while i<len(src):
  if src.startswith('--',i):
   end=src.find('\n',i);end=len(src) if end<0 else end
   piece=src[i:end];comments.append(piece);out.append(blank(piece));i=end;continue
  if src.startswith('/-',i):
   start=i;depth=1;i+=2
   while depth and i<len(src):
    if src.startswith('/-',i):depth+=1;i+=2
    elif src.startswith('-/',i):depth-=1;i+=2
    else:i+=1
   assert depth==0
   piece=src[start:i];comments.append(piece);out.append(blank(piece));continue
  if src[i]=='"':
   start=i;i+=1
   while i<len(src):
    if src[i]=='\\':i+=2;continue
    if src[i]=='"':i+=1;break
    i+=1
   else:raise AssertionError('unfinished quoted string')
   piece=src[start:i];strings.append(piece);out.append(blank(piece));continue
  if src[i]=="'" and (i==0 or not (src[i-1].isalnum() or src[i-1]=='_')):
   match=re.match(r"'(?:\\.|[^\\\n'])'",src[i:])
   if match:
    piece=match.group();out.append(blank(piece));i+=len(piece);continue
  out.append(src[i]);i+=1
 return ''.join(out),comments,strings
fixture='theorem t : True := by sorry\n-- admit\n/- axiom /- unsafe -/ -/\n#eval "sorry"\nunsafe def f := 1\n'
f,comments,strings=mask(fixture)
assert [x.group() for x in tokens.finditer(f)]==['sorry','unsafe']
assert 'admit' in comments[0] and 'axiom' in comments[1] and 'sorry' in strings[0]
# Explicit boundaries: aliases and quoted syntax cannot be semantically resolved
# by this lexical inventory, even if a target identifier appears elsewhere.
alias='open Classical\n#check choice\n'
assert not list(choice.finditer(mask(alias)[0]))
quoted='def «sorry» := 1\n'
assert [x.group() for x in tokens.finditer(mask(quoted)[0])]==['sorry']
hits=[];excluded=Counter();choices=[];admit_comments=[];qualified_choose=[]
for name,entry in sorted(mods.items()):
 path=Path(entry['source_path']);raw=path.read_bytes();assert sha256(raw).hexdigest()==entry['sha256'],name
 source=raw.decode();code,cs,ss=mask(source)
 for kind,blocks in [('comment',cs),('string',ss)]:
  for block in blocks:
   for x in tokens.finditer(block):excluded[kind+':'+x.group()]+=1
 if any(re.search(r'\badmit\b',c) for c in cs):admit_comments.append(name)
 for match in tokens.finditer(code):
  line=source.count('\n',0,match.start())+1;col=match.start()-(source.rfind('\n',0,match.start())+1)+1
  hits.append((name,line,col,match.group()))
 for match in constant.finditer(code):
  off=code.find('constant',match.start(),match.end());line=source.count('\n',0,off)+1;col=off-(source.rfind('\n',0,off)+1)+1
  hits.append((name,line,col,'constant'))
 for match in re.finditer(r"(?<![A-Za-z0-9_])Classical\.choose(?![A-Za-z0-9_!'])",code):
  line=source.count('\n',0,match.start())+1
  qualified_choose.append((name,line))
 for match in choice.finditer(code):
  line=source.count('\n',0,match.start())+1;col=match.start()-(source.rfind('\n',0,match.start())+1)+1
  hits.append((name,line,col,'Classical.choice'));choices.append((name,line,col))
claimed=[(h['module'],h['line'],h['column'],h['token']) for h in inv['code_hits']]
assert sorted(hits)==sorted(claimed)
assert dict(sorted(excluded.items()))==inv['comment_and_string_marker_counts']
assert Counter(x[3] for x in hits)==Counter({'Classical.choice':159})
assert len({x[0] for x in choices})==51
assert ('DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011',16) in qualified_choose
assert len(qualified_choose)>0
assert sorted(admit_comments)==['DiophantineConsistency.Compact44.FreeJOrdinaryTailWitness','DiophantineConsistency.IPRAOpenAtomDecision']
# Direct spot-checks retain the signed source coordinates and duplicate hits.
assert ('DiophantineConsistency.IPRAAddOneDirect',165) in {(n,l) for n,l,_ in choices}
assert sum(1 for n,l,_ in choices if n=='DiophantineConsistency.IPRAAddOneDirect' and l==202)==2
for p,needle in [('Lean/DiophantineConsistency/Compact44/FreeJOrdinaryTailWitness.lean','q and n admit the specified ordinary strong'),('Lean/DiophantineConsistency/IPRAOpenAtomDecision.lean','Open NNF formulas admit native decision')]:assert needle in Path(p).read_text()
print(json.dumps({'selection_sha256':sha256(P.read_bytes()).hexdigest(),
 'reviewed_inventory_sha256':sha256((D/'inventory.json').read_bytes()).hexdigest(),
 'reviewed_scanner_sha256':sha256((D/'scan.py').read_bytes()).hexdigest(),
 'selected_sources_independently_scanned':len(mods),
 'marker_positions_match_reported_inventory':True,
 'excluded_marker_counts_match':dict(sorted(excluded.items())),
 'qualified_choice_hits':len(choices),'modules_with_choice_hits':len({x[0] for x in choices}),
 'admit_comment_modules':sorted(admit_comments),
 'blind_spot_controls':['unqualified choice alias not detected','quoted identifier may be a lexical false positive'],
 'unscanned_qualified_Classical_choose_occurrences':len(qualified_choose),
 'unscanned_choose_source_spot_check':['DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011',16],
 'lean_executed':False,'scope':'Independent bounded lexical cross-check; not a Lean lexer, semantic proof or axiom audit, or provider verification.'},sort_keys=True,indent=2))
