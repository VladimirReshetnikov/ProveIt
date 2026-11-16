import hashlib,json,sys
from pathlib import Path
root=Path(sys.argv[1])/'Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2'
a=root/'inputs/primary.instructions.json';b=root/'machines/PA194AX11H/instructions.json'
assert hashlib.sha256(a.read_bytes()).hexdigest()=='6c3127cd0da15fda49ed99cea199a009b9bc1e1707100846df9a2df02a22d507'
assert hashlib.sha256(b.read_bytes()).hexdigest()=='43a4ba0d62f95fe766d5369940b0aa8b7a4da04824feb8836905e289640f59f7'
x=json.loads(a.read_text())[3554:3568];y=json.loads(b.read_text())[3572:3586]
assert len(x)==len(y)==14
def fmt(i):
 if i[0]=='inc': return f'.inc {i[1]} (some {i[2]})'
 if i[0]=='dec': return f'.dec {i[1]} (some {i[2]}) (some {i[3]})'
 if i[0]=='jump': return f'.jump (some {i[1]})'
 raise ValueError(i)
s='''import PA194AX11HSource
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PA194AX11HFieldRows
open M6.Source

def oldField : List Instruction := [
'''+',\n'.join('  '+fmt(i) for i in x)+'''
]

def newField : List Instruction := [
'''+',\n'.join('  '+fmt(i) for i in y)+'''
]

def relocate : Instruction → Instruction
  | .inc r next => .inc r (next.map (· + 18))
  | .dec r zero positive => .dec r (zero.map (· + 18)) (positive.map (· + 18))
  | .jump next => .jump (next.map (· + 18))
  | .halt => .halt

theorem exact_field : oldField.map relocate = newField := by decide +kernel
#print axioms exact_field
end PA194AX11HFieldRows
'''
Path(sys.argv[2]).mkdir(parents=True,exist_ok=True)
(Path(sys.argv[2])/'PA194AX11HFieldRows.lean').write_text(s)
