#!/usr/bin/env python3
"""Prospective tests of the OWN maintained producer. Not run during source preparation.

Run only after independent source review. This imports the locally pinned own
producer, never the attributed upstream renderer. It does not invoke Lean.
"""
import hashlib, importlib.util, json, pathlib, shutil, sys, tempfile
HERE=pathlib.Path(__file__).resolve().parent
PRODUCER=HERE/'production/generate_dominated_implication_lean.py'
PIN='ebcbb86642d4d389748451dc662b42f7ac62e7aa4b235bbf4e5d8e5a1ec5c1e9'
def sha(b): return hashlib.sha256(b).hexdigest()
assert sha(PRODUCER.read_bytes())==PIN
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('own_shared58_producer',PRODUCER)
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
raw=(p.HERE/p.SOURCE).read_text()
final=(HERE/'expected/upstream-core.lean').read_text()
assert sha(raw.encode())==p.INPUT_PINS[p.SOURCE]
assert sha(final.encode())==p.EXPECTED_CORE
results=[]
def positive(name, fn):
 value=fn();results.append({'name':name,'kind':'positive','status':'PASS'});return value
def rejected(name, fn):
 try: fn()
 except (AssertionError,KeyError,IndexError,ValueError) as e:
  results.append({'name':name,'kind':'negative','status':'REJECTED','exception':type(e).__name__,'message':str(e)[:400]})
 else: raise AssertionError('negative control accepted: '+name)
def changed(text,old,new):
 assert text.count(old)==1,(old,text.count(old));return text.replace(old,new)
def equal(x,y):assert x==y
positive('raw_58_six_targets',lambda:p.audit(raw))
positive('two_inlinings_exact_upstream',lambda:equal(p.render_core(raw),final))
positive('final_56_six_targets',lambda:p.audit(final,True))
positive('pinned_pair_generation',lambda:equal(p.generate()[:2],(final,(p.HERE/p.ADAPTER).read_text())))
# Semantic mutations bypass only the outer SHA gate to challenge the inference checker itself.
rejected('wrong_K_instance',lambda:p.audit(changed(final,'  d12 h a b\n','  d12 h b a\n'),True))
rejected('wrong_Peirce_instance',lambda:p.audit(changed(final,'  d18 h a b\n','  d18 h b a\n'),True))
rejected('wrong_S_minor_instance',lambda:p.audit(changed(final,'(d53 h a b c)','(d53 h a c b)'),True))
rejected('wrong_composition_instance',lambda:p.audit(changed(final,'  d51 h a b c\n','  d51 h b a c\n'),True))
rejected('undeclared_K_proof_fact',lambda:p.audit(changed(final,'  d12 h a b\n','  hab\n'),True))
rejected('wrong_reflexivity_guard',lambda:p.audit(final.replace('(L.refl _)','(L.refl (wim v0 v0))',1),True))
rejected('wrong_guard_hypothesis',lambda:p.audit(final.replace('v3 hb0)','v3 (L.refl _))',1),True))
rejected('missing_private_step',lambda:p.audit(final.replace('private theorem d1 ','private theorem d59 ',1),True))
# Wrong source roles or altered blocks must fail before text is emitted.
rejected('old_swapped_S_inline_arguments',lambda:p.render_core(changed(raw,'  d56 h a b c\n','  d56 h c u a b\n')))
rejected('old_swapped_rho_inline_arguments',lambda:p.render_core(changed(raw,'  d58 h c u a b\n','  d58 h a b c\n')))
rejected('changed_pinned_S_block',lambda:p.render_core(changed(raw,'(d53 h v0 v1 v2)','(d53 h v0 v2 v1)')))
# Input-pin/output-pin gates are distinct from the semantic tests above.
original_here=p.HERE
with tempfile.TemporaryDirectory(prefix='shared58-controls-') as td:
 temp=pathlib.Path(td)
 for name in p.INPUT_PINS:
  q=temp/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes((original_here/name).read_bytes())
 p.HERE=temp
 try:
  for name in p.INPUT_PINS:
   q=temp/name;before=q.read_bytes();q.write_bytes(before+b'\n')
   try:rejected('input_pin:'+name,p.generate)
   finally:q.write_bytes(before)
  expected=p.EXPECTED_CORE;p.EXPECTED_CORE='0'*64
  try:rejected('wrong_expected_output_pin',p.generate)
  finally:p.EXPECTED_CORE=expected
 finally:p.HERE=original_here
assert len([r for r in results if r['kind']=='positive'])==4
assert len([r for r in results if r['kind']=='negative'])==15
print(json.dumps({'status':'PASS_OWN_PRODUCER_CONTROLS','producer_sha256':PIN,'results':results,'compiler_invocations':0,'supplied_renderer_invocations':0},indent=2))
