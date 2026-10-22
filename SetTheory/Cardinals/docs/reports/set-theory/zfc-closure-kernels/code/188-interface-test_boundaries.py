"""Owned mutations of the actual admission predicates and opaque-step guard."""
if not __debug__:raise RuntimeError('Assertions must be enabled')
from pathlib import Path
import json
D=Path(__file__).parent
ns={'__file__':str(D/'check_templates.py')}
s=(D/'check_templates.py').read_text().split('rows=[];templates={};fallback=0')[0]
exec(compile(s,str(D/'check_templates.py'),'exec'),ns)
A=ns['A'];P=ns['P'];PR=ns['PR'];check=ns['prefix_ok'];frame=ns['syntactic_frame'];home=ns['home'];step=ns['step_checked']
assert check('00000001') and check('1')
assert not check('10') and not check('000000001') and not check('')
try:step(None,(0,True,(PR,A.B(1)),(A.B(0),)))
except AssertionError:pass
else:raise AssertionError('Opaque read was accepted')
assert home((2,True,(PR,A.B(1)),(A.B(0),)))is not None
assert home((2,True,(PR,A.B(1),A.B(1)),(A.B(0),)))is None
# The source operation would cross P: CC demands too many ones, or CB carry overflows S.
assert not frame((True,0,'0','CC',1,False,'',0,0,1))
assert not frame((True,0,'10','CB',1,False,'00',0,1,0))
assert not frame((True,0,'101','CC',1,False,'wrong',0,0,0))
result={'status':'NEGATIVE_BOUNDARY_TESTS_PASS','cases':['prefix ends zero','eight-zero run','empty opaque prefix','ordinary opaque read','Home opaque chunk not final','CC strip crosses prefix','CB increment overflows suffix','wrong source target suffix']}
(D/'BOUNDARY_TESTS.json').write_text(json.dumps(result,indent=2));print(result)
