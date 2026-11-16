import hashlib,json,sys
from pathlib import Path
p=Path(sys.argv[1])/'Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2/machines/PA194AX11H/instructions.json'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='43a4ba0d62f95fe766d5369940b0aa8b7a4da04824feb8836905e289640f59f7'
x=json.loads(p.read_text())[3519:3553];assert len(x)==34
def fmt(i):
 if i[0]=='inc':return f'.inc {i[1]} (some {i[2]})'
 if i[0]=='dec':return f'.dec {i[1]} (some {i[2]}) (some {i[3]})'
 if i[0]=='jump':return f'.jump (some {i[1]})'
 raise ValueError(i)
s='''import PA194AX11HGateRows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194AX11HGateData
open M6.Source PA194AX11HGateRows

def gateData : List Instruction := [
'''+',\n'.join('  '+fmt(i) for i in x)+'''
]

theorem data_correct : newGate = gateData.map some := by decide +kernel
#print axioms data_correct
end PA194AX11HGateData
'''
out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True);(out/'PA194AX11HGateData.lean').write_text(s)
