#!/usr/bin/env python3
"""Record, without prescribing an exact erroneous value, a version-specific
loss of accuracy in tiny-step order differentiation of mpmath.polylog.
The independent reference is the differentiated defining integral.
This is a diagnostic; it is not a general claim about the library.
"""
import json, platform
from pathlib import Path
import mpmath as mp

mp.mp.dps=50
x=mp.mpf('1.5')
naive=mp.diff(lambda s:-mp.polylog(s,-mp.exp(x)),1)
reference=mp.quad(lambda t:(mp.log(t)+mp.euler)/(1+mp.exp(t-x)),
                  [0,1,x+2,12,mp.inf])
report={
  'python':platform.python_version(),'mpmath':mp.__version__,'dps':mp.mp.dps,
  'x':str(x),'order':1,
  'tiny_step_order_derivative':mp.nstr(naive,52),
  'defining_integral_derivative':mp.nstr(reference,52),
  'absolute_discrepancy':mp.nstr(abs(naive-reference),20),
  'scope':'Observed diagnostic. No assertion about the cause or every version.'
}
print(json.dumps(report,indent=2))
