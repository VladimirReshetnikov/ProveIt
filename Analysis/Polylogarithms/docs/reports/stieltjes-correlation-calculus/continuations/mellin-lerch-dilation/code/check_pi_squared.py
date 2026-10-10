#!/usr/bin/env python3
"""Direct local-subtraction quadrature of the displayed pi-squared identity."""
from pathlib import Path
import json
import mpmath as mp
from check_dilated_polygamma import subtracted_fp

if __name__ == "__main__":
    mp.mp.dps=42
    value=subtracted_fp(2,3,0,1,"1/4")
    error=abs(value-mp.pi**2)
    result={"working_precision":mp.mp.dps,"p":2,"q":3,"r":0,"k":1,
            "a":"1/4","integral":str(value),"pi_squared":str(mp.pi**2),
            "absolute_error":str(error),"passed":error<mp.mpf('1e-35')}
    target=Path(__file__).resolve().parents[1]/"results"/"pi_squared_check.json"
    target.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
    assert result["passed"]
