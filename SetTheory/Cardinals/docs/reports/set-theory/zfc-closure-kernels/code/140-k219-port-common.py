"""Small shared parsers and exact identities for the K219 release."""
from pathlib import Path
import hashlib,json
BASE_ARCHIVE_SHA='132cbb326fcbf6e54957a03095c5f790e207f4ed8ebfb6ceb6e272f329e4ee00'
BASE_TABLE_SHA='4466ec4f947a9c5112397c30ca25b0e70e3ac39ee54878b3e4493a0297d732e4'
BASE_SOURCE_SHA='837e92d7b1c107330f160f654f6c36ff0b03dfbf6bc2b89c6f782eb7db4c4ce7'
TABLE_SHA='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
SOURCE_SHA='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
CANONICAL_SHA='02079501e6255951cbc1c31d2c3cab076574d3d61c892f0e5a541cd1789442ec'
PHY=(6,2,0,4,3,7,8,5,1)

def require(condition,message):
    if not condition:raise ValueError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def sha_file(path):return sha(Path(path).read_bytes())
def dump(path,value):Path(path).write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def parse_table(raw,start=0,halt=254):
    table={};starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):starts.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q,bit,w,d,z=line.split();q,bit,w,z=map(int,(q,bit,w,z))
            require((q,bit)not in table and bit in(0,1)and w in(0,1)and d in('L','R'),'Malformed transition')
            table[q,bit]=(w,1 if d=='R'else-1,z)
    states={q for q,bit in table}
    require(starts==[start]and start in states and halt not in states,'Start or terminal convention')
    require(set(table)=={(q,bit)for q in states for bit in(0,1)},'Incomplete transition table')
    require({z for w,d,z in table.values()}-states=={halt},'Unexpected terminal label')
    return table

def table_bytes(table,start=0):
    return ('#! start '+str(start)+'\n'+''.join(f'{q} {bit} {w} {"R"if d==1 else"L"} {z}\n'for(q,bit),(w,d,z)in sorted(table.items()))).encode('ascii')
