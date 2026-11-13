#!/usr/bin/env python3
"""Exact graph/literal/display-circuit reconciliation; no Lean or PDF semantics."""
import hashlib,json,re,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent;sha=lambda x:hashlib.sha256(x).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
pins=json.loads((d/'pins.json').read_bytes())
for f,h in pins.items():need(sha((r/f).read_bytes())==h,'pin '+f)
def read(f):return (r/f).read_text()
def obj(f):return json.loads((r/f).read_bytes())
old=obj('research/adaptive-square-sums/candidate.json');new=obj('research/adaptive87-four-square-free-positive-ordinate87-36/graph.json')
ren={'y':'auxPositive','auxResidual':'fa_minus','firstSquare':'a0_sq','mainSquare':'a1_sq','auxSquare':'fa_sq','strongSquare':'strong_sq','firstMain':'sum0','firstMainAux':'sum1','sumSquares':'output'}
def cv(x):return ren.get(x,x) if isinstance(x,str) else x
need([cv(x) for x in old['witnesses']]==new['witnesses'] and old['fixed_numerals']==new['fixed_numerals'],'coordinate/ports')
need([[cv(x) for x in row] for row in old['source']]==new['source'] and cv(old['output'])==new['output'] and len(new['source'])==87,'exact renamed graph')
# Check the exact Lean literal headers, all rows, and output, no Lean parsing claim.
s=read('Lean/DiophantineConsistency/AdaptiveDirectOrdinateSquareSumsLiteral.lean');draft=read('research/ipra-standard-13-frontier/draft-src/AdaptiveDirectOrdinateSquareSumsLiteral.lean');need(s==draft,'tracked/draft literal')
signature='def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n';need(s.count(signature)==1,'literal signature')
actual=s.split(signature,1)[1].split('\n\n/-- The generated DAG',1)[0].rstrip('\n').splitlines()
want=[f'  let {n} : Expr (Fin 13) := .var {i}' for i,n in enumerate(old['witnesses'])]+[f'  let {n} : Expr (Fin 13) := .constant (p {i})' for i,n in enumerate(old['fixed_numerals'])]+[f'  let {n} := {a} {o} {b}' for n,o,a,b in old['source']]+['  '+old['output']]
need(actual==want and 'theorem literal_eq_optimized' in s,'Lean literal rows')
# Check each printed 87-gate line and user-facing variable declaration.
tex=read('equation36.tex');pr={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega','qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed'}
def fmt(x):return pr.get(str(x),str(x)).replace('_',r'\_')
lines=[line for line in tex.splitlines() if line[:1].isdigit() and '. ' in line and ' = ' in line and line.endswith(r'\\')]
need(len(lines)==87,'display row count')
for k,(line,(name,o,a,b)) in enumerate(zip(lines,old['source']),1):need(line==f'{k}. {fmt(name)} = {fmt(a)} {o} {fmt(b)}'+r'\\','display row '+str(k))
m=re.search(r'The only unknowns are the thirteen separately named positive-integer variables\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]',tex,re.S);need(m is not None,'display variable declaration')
printed=[v.strip().lstrip('\\') for v in m.group(1).split(',')];need(printed==['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma'] and len(set(printed))==13,'display variables')
native=read('research/ipra-standard-13-frontier/draft-src/IPRASquareSumsNative.lean');standard=read('research/ipra-standard-13-frontier/draft-src/IPRAStandardSquareSums13.lean')
need(native==read('Lean/DiophantineConsistency/IPRASquareSumsNative.lean'),'native current/draft source')
need('theorem literal_equivalence' in native and '(AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)' in native and '∼mappedNativeRefutation embedding' in native,'native target')
need('(provable_iff _).2 IPRASquareSumsNative.literal_equivalence' in standard and 'theorem literal_iff_translated_consistency' in standard and '(Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ' in standard,'standard target')
need(sha((r/'equation36.pdf').read_bytes())=='321e9d2714b7c40af7af20d5d28299346f10c5413f432ec32cceb59ccc775269','recorded PDF bytes')
hist={'DiophantineConsistency.AdaptiveDirectOrdinateSquareSumsLiteral':'research/ipra-standard-13-frontier/draft-src/AdaptiveDirectOrdinateSquareSumsLiteral.lean','DiophantineConsistency.IPRASquareSumsNative':'research/ipra-standard-13-frontier/draft-src/IPRASquareSumsNative.lean','DiophantineConsistency.IPRAStandardSquareSums13':'research/ipra-standard-13-frontier/draft-src/IPRAStandardSquareSums13.lean'}
for role in ('author','peer'):
 state=obj('reviews/ipra-frontier13-historical-pair-terminal/'+role+'/rebuild-state.json');need(state['status']=='PASS','historical '+role)
 rr={a['module']:a for a in state['records']}
 for name,file in hist.items():need(rr[name]['exit']==0 and rr[name]['source_sha256']==pins[file],'historical source '+role+' '+name)
terminal=obj('reviews/ipra-frontier13-historical-pair-terminal/outer-terminal-observation.json');need(terminal['observed_exit_code']==0 and 'MATCHED_SELECTIVE_PASS 8 affected modules' in terminal['observed_stdout'],'recorded paired exit')
print(json.dumps({'scope':'exact renamed graph, Lean literal text and TeX circuit rows; historical proof and PDF semantics not rechecked','pins_sha256':sha((d/'pins.json').read_bytes()),'renamed_graph_rows':len(new['source']),'inputs_and_ports_identical':True,'tracked_literal_matches_frontier_draft':True,'printed_gate_rows':len(lines),'historical_native_and_standard_statement_shapes':True,'historical_paired_source_hashes_match':True,'pdf_sha256':pins['equation36.pdf']},sort_keys=True,indent=2))
