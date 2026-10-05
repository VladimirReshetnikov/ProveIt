"""Additional independent reconstruction of every coefficient printed in the article."""
import json
from pathlib import Path
from check_coefficients import reconstruct
values,checks,profiles=reconstruct(2,2,10)
expected=[1,3,2,1,0,3,26,101,124,-1409,-13266]
if values!=expected:raise RuntimeError((values,expected))
result={'status':'PASS','order':10,'coefficients':[str(v) for v in values],'polynomial_checks':checks,'larger_component_profiles':profiles}
Path(__file__).with_name('order_ten.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
