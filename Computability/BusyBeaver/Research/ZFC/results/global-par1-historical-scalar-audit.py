"""Exact Nat working-interface calculation; no blank-start/machine claim."""
from pathlib import Path
import hashlib,json
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');B=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
def pair(a,b):return (a+b)*(a+b+1)//2+b
def unpair(z):
 from math import isqrt
 s=(isqrt(8*z+1)-1)//2;b=z-s*(s+1)//2;return s-b,b
imp=lambda a,b:4*pair(a,b)
# Native fields are(TW,WS,D,H), source p1=D+x and p2=H after parameter read.
initial=(2,0,0,36);target=1
assert 2==4*pair(0,0)+2 and 3==4*pair(0,0)+3 and 36==imp(0,3)
t,s,d,h=initial;b=d+target
old_compare=imp(t,b)
# Replacing166 by167 at earlierMP node161 adds instead of clearing/pushing.
new_tw_before_cons=t+b;head,tail=unpair(s);new_compare=imp(head,new_tw_before_cons)
assert (old_compare,new_compare)==(28,36)
original=(b,pair(0,s),b,0)if old_compare==h else(0,s,b,0)
modified=(b,tail,b,0)if new_compare==h else(0,tail,b,0)
assert original==(0,0,1,0)and modified==(1,0,1,0)
def drop(w):t,s,d,h=w;return h,pair(t,s),d,h
def nip(w):
 t,s,d,h=w
 if h==1:return None
 a,b=unpair(s);return t,b,d,a
trace=[modified,drop(modified)];trace.append(nip(trace[-1]));trace.append(nip(trace[-1]));assert trace[-1]is None
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source_refs={n:sha(B/n)for n in ['Dag254.lean','L2Macros254.lean','L2Lib254.lean','L2Control254.lean','Enum254.lean','SeedInvariant254.lean','Code254.lean']}
out=dict(status='PASS_SCALAR_SOURCE_INTERFACE_COUNTEREXAMPLE',scope='Exact changed MP effect from an explicitly good working state; no claim that a modified blank execution reaches it or halts.',initial_working=initial,goal=target,old_comparison=old_compare,new_comparison=new_compare,original_output=original,modified_output=modified,modified_cleanup_trace=trace,cleanup_word=['DROP0','NIP0','NIP0'],initial_theorem_certificates=dict(top='SeedInvariant254.Formula.sound (.all 0 .truth), code2',stack='Enum254.good_zero, code0',cache='SeedInvariant254.Formula.sound (.weaken 0 (.eqRefl 0)), code36'),source_derivation=['L2Lib254.loop198/loop205: clean node167 adds p1 toTW and restoresp1; leavesWS unchanged.','Dag254 node161 invokespar1 beforecons; global166→167 changes this call in addition to success130.','L2Macros254.cons popsWShead and pairs it as antecedent, so compare=Imp(headWS,TW+p1).','loop216 clearsTW beforecomparison; success130 executes167 onTW0 and thereforeacceptsgoal1.','DROP/NIP macros have no globalpar1 call and retain original cleanup behavior.'],interpretation='The oldGood/Inv preservation theorem cannot survive this rule in a nonrefutingC254 model; semantic local truth preservation already fails in an inhabited irreflexive structure. No unconditional ConZFC or modifiedblankhalting assertion.',source_hashes=source_refs,driver_sha256=sha(__file__),lean_build=False,table_mutation=False)
Path('/tmp/zfc-global-par1/scalar-counterexample.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
