#!/usr/bin/env python3
"""Independent source-signature and sparse-polynomial cut review. No Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
pins={
 'research/ordinary14-natural80-main-pairs-draft/Natural80MainPairs.lean':'22350958652773aa4f900c69e99b0891b4811168d70c479a4c463bb0924028c0',
 'research/ordinary14-natural80-main-pairs-draft/check_source.py':'fbd15b10040643a65c8b745ed5fc4ededf8968c561423a53beaa701a2582ee52',
 'research/ordinary14-natural80-main-pairs-draft/result.json':'ab18e84d3168a67929014be0a459bda36ca7cd8fc8b8841816413c580399a458',
 'research/ordinary14-positive-guard74/candidate.json':'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093',
 'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean':'5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b',
 'research/ordinary14-74-first-factor-client-draft/FirstFactor74.lean':'fca24f5e8e3be0743e3423f66573e099a211f3c2cfc973d69f77c0a2ff8d62f4',
 'research/ordinary14-74-factor-residues-draft/FactorResidues74.lean':'368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60',
 'research/ordinary14-natural80-guard-gap-draft/Natural80GuardGap.lean':'df59908f11990a28b4b788d0014757a897f2bdc1a4011772e0e825397cad43eb',
 'research/ordinary14-natural80-ownzero-norm-draft/Natural80OwnZeroNorm.lean':'670f8a6e7208afccde1051d72b3154990e1347cbf8d51a3845a89f56f81fcb74',
 'research/ordinary14-pair-eval-ring-bridge-draft/PairEvalRingBridge.lean':'0fdb641db2008362ae3ec363bea66f6b4a4b475c1de2d5d00b7c1e9a81adc510',
 'Lean/DiophantineConsistency/ArithmeticAdaptiveTransport2011.lean':'e8b22ad05230a0f0815766adcc989caf66251e9bad34eb524da83f9155b5ee24',
 'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean':'ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d',
 'Lean/DiophantineConsistency/ArithmeticAdaptiveScaledNorms2011.lean':'b3b164e528edf0c2b51eecd994140d30389d80b36ae830dccc286dc0e6bf0863',
}
s={}
for path,digest in pins.items():
 data=(D/path).read_bytes();assert hashlib.sha256(data).hexdigest()==digest,path;s[Path(path).name]=data.decode()
def signature(text,name):
 m=re.search(r'\b(?:theorem|def)\s+'+re.escape(name)+r'\b(.*?)(?=\s+:=\s*by\b)',text,re.S);assert m,name
 return re.sub(r'\s+',' ',m.group(1)).strip()
client=s['Natural80MainPairs.lean']
for name in ('rhs_eval','rhs_rep'):
 h=signature(client,name);assert '(hbeta : (p 0 : DiffRing V)=ι beta)' in h
 assert all(tok not in h for tok in ('hMC','hMF','hgap','hK','0<','0 <'))
for name in ('root_eval','root_rep'):
 h=signature(client,name)
 for tok in ('(hbeta : (p 0 : DiffRing V)=ι beta)','(hMC : (p 2 : DiffRing V)=ι MC)', '(hMF : (p 3 : DiffRing V)=ι MF)', '(hgap : u 1+u 2<q beta u)'):assert tok in h,(name,tok)
 assert '0<u 12' not in h and '0 < u 12' not in h and 'hK' not in h
h=signature(client,'norm_of_80_zero')
for tok in ('(hbeta : (p 0 : DiffRing V)=ι beta)','(hK : (p 1 : DiffRing V)=ι K)', '(hMC : (p 2 : DiffRing V)=ι MC)', '(hMF : (p 3 : DiffRing V)=ι MF)', '(hb : 0<beta)', '(hKpos : 0<K)', '(hz : InternalZero (P80NaturalForcedGamma.graph p).output v)'):assert tok in h,tok
assert all(tok not in h for tok in ('0<v 12','0 < v 12','MC<beta','MF<2*beta'))
for n in ('rhs_rep','root_rep','norm_of_80_zero'):
 assert '#print axioms DiophantineConsistency.Natural80MainPairsDraft.'+n in client
for tok in ('have hF : u 1≤q beta u','have hq2 : 1≤q beta u*q beta u', 'tsub_add_cancel_of_le hF','tsub_add_cancel_of_le hq2','(hrhs : Equivalent (pairEval (mainRhs p) u) (natural rhs))','magnitude_equivalent hroot','unit_square_norm','units_of_80_zero','gap_of_80_zero'):assert tok in client,tok
assert 'def Equivalent (p q : Pair V) : Prop := p.1+q.2=p.2+q.1' in s['ArithmeticSignedPairs.lean']
assert 'def natural (a : V) : Pair V := (a,0)' in s['ArithmeticSignedPairs.lean']
assert 'theorem magnitude_equivalent {p q : Pair V} (h : Equivalent p q) : magnitude p=magnitude q' in s['ArithmeticAdaptiveTransport2011.lean']
hn=signature(s['ArithmeticAdaptiveScaledNorms2011.lean'],'unit_square_norm')
for tok in ('(hu :','magnitude (pairEval z v)*magnitude (pairEval z v) + (pairEval rhs v).2 = (pairEval rhs v).1'):assert tok in hn
rr=signature(s['PairEvalRingBridge.lean'],'represented_of_ring_eval')
for tok in ('e.evalRing (fun j => ι (v j))=ι a-ι b','Equivalent (pairEval e v) (a,b)'):assert tok in rr
for file,theorem in [('Natural80GuardGap.lean','gap_of_80_zero'),('Natural80OwnZeroNorm.lean','units_of_80_zero')]:
 h=signature(s[file],theorem)
 for tok in ('(hbeta :', '(hK :','(hb : 0<beta)', '(hKpos : 0<K)', '(hz : InternalZero'):assert tok in h,(file,tok)
 assert '0<v 12' not in h and '0 < v 12' not in h
# Check every literal 74 graph row and the relevant typed field projection.
g=json.loads(s['candidate.json']);text=s['P74PositiveGuard.lean'];block=text.split('-- BEGIN LITERAL GRAPH',1)[1].split('-- END LITERAL GRAPH',1)[0];rows=[]
for line in block.splitlines():
 if not line.strip():continue
 m=re.fullmatch(r'\s*let (\w+) := (\w+|\d+) ([+*\-]) (\w+|\d+)\s*',line);assert m,line
 n,x,op,y=m.groups();parse=lambda t:int(t) if t.isdecimal() else t;rows.append([n,op,parse(x),parse(y)])
assert rows==g['source'] and len(rows)==74
aliases=re.findall(r'let\s+(\w+)\s*:\s*Expr \(Fin 14\)\s*:=\s*\.var (\d+)',text)
assert aliases==[(v,str(i)) for i,v in enumerate(g['witnesses'])]
fields=re.findall(r'^\s+(\w+) : Expr \(Fin 14\)\s*$',text.split('structure Graph where',1)[1].split('set_option',1)[0],re.M)
tupletxt=re.search(r'-- END LITERAL GRAPH\s*⟨([^⟩]+)⟩',text).group(1);fieldvals=[v.strip() for v in tupletxt.split(',')]
assert len(fields)==len(fieldvals);field=dict(zip(fields,fieldvals))
for k,v in {'main':'F1','U':'U','a':'a','c':'c','Dstar':'Dstar'}.items():assert field[k]==v
r={n:(op,x,y) for n,op,x,y in rows}
expected={
 'qm':('*','J','beta'), 'q':('+',1,'qm'), 'q2':('*','q','q'), 'q3':('*','q','q2'),
 'X':('*','q','w'), 'Y':('*','q3','s'), 'U':('*','Y','q2'), 'qF':('-','q','F'),
 'k':('+','eta','zeta'), 'kY':('*','Y','k'), 'c':('+','eta','kY'),
 'E':('*','X','Y'), 'a':('+','E','Y'), 'g15':('*',4,'a'), 'H':('+',3,'g15'),
 'g17':('*','a','a'), 'Delta':('+','H','g17'), 'g19':('*','a','c'),
 'b0':('+','X','g19'), 'g44':('*','qF','qm'), 'G':('+','alpha','g44'),
 'g46':('-','q2',1), 'g47':('*','G','g46'), 'g48':('*','MF','q'),
 'g49':('+','MC','g48'), 'g50':('*','J','g49'), 'R':('+','g47','g50'),
 'g52':('-','k','R'), 'r0':('-','g52',1), 'g54':('*','U','gamma'),
 'shift':('-','g54','r0'), 'g58':('*','U','b0'), 'g59':('*','H','shift'),
 'Dstar':('+','g58','g59'), 'c2':('*','c','c'), 'g62':('*','U','U'),
 'g63':('*','Delta','c2'), 'g64':('+',1,'g63'), 'g65':('*','g62','g64'),
}
for n,row in expected.items():assert r[n]==row,(n,r[n],row)
first=s['FirstFactor74.lean']
for textcut in ('def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta','def X (beta : V) (v : Fin 14 → V) : V := q beta v*v 6','def Y (beta : V) (v : Fin 14 → V) : V := (q beta v*(q beta v*q beta v))*v 7'):assert textcut in first
# Formal sparse integer-polynomial verification of the root and RHS cuts in abstract graph values.
def v(x):return {(x,):1}
def c(x):return {():x} if x else {}
def add(x,y):
 z=dict(x)
 for mon,a in y.items():z[mon]=z.get(mon,0)+a
 return {mon:a for mon,a in z.items() if a}
def neg(x):return {mon:-a for mon,a in x.items()}
def sub(x,y):return add(x,neg(y))
def mul(x,y):
 z={}
 for a,xv in x.items():
  for b,yv in y.items():
   mon=tuple(sorted(a+b));z[mon]=z.get(mon,0)+xv*yv
 return {mon:a for mon,a in z.items() if a}
U,X,A,C,H,K,R,G=map(v,['U','X','A','C','H','K','R','G']);one=c(1)
literal=add(mul(U,add(X,mul(A,C))),mul(H,sub(mul(U,G),sub(sub(K,R),one))))
P=add(mul(U,add(X,mul(A,C))),mul(H,add(add(mul(U,G),R),one)));N=mul(H,K)
assert literal==sub(P,N)
literalrhs=mul(mul(U,U),add(one,mul(add(H,mul(A,A)),mul(C,C))))
rhs=add(add(mul(U,U),mul(mul(mul(U,U),H),mul(C,C))),
        mul(mul(mul(U,U),mul(A,A)),mul(C,C)))
assert literalrhs==rhs
# Truncated subtraction is safe under the recorded bounds, but not universally.
for q in range(1,15):
 for F in range(q+1):assert max(q-F,0)==q-F
 assert max(q*q-1,0)==q*q-1
assert max(1-2,0)!=1-2
print(json.dumps({'scope':'bounded source signatures and independent exact algebraic graph cuts; no Lean elaboration or model theorem','pinned_files':len(pins),'literal_graph_rows':len(rows),'main_graph_rows_checked':len(expected),'exact_root_and_rhs_cuts':2,'gap_free_root_subtraction_counterexample':[1,2], 'gamma_positivity_premise':False,'axiom_reports_executed':False},sort_keys=True,indent=2))
