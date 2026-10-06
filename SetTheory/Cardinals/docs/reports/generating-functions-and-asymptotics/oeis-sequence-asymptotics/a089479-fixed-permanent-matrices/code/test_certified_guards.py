"""Standard-library negative tests; valid both normally and under python -O."""
from pathlib import Path
from contextlib import redirect_stdout
import io,os,runpy,tempfile,json
root=Path(__file__).resolve().parent
expected=json.loads((root/'constant_certificate.json').read_text())
old=Path.cwd()
with tempfile.TemporaryDirectory(prefix='fixedpermanent_certificate_test_') as tmp:
    try:
        os.chdir(tmp)
        with redirect_stdout(io.StringIO()): ns=runpy.run_path(str(root/'certify_constants.py'))
        actual=json.loads(Path('constant_certificate.json').read_text())
        if actual!=expected:raise ArithmeticError('valid certificate changed')
    finally:os.chdir(old)
eval_=ns['evaluate'];I=ns['I'];ec=ns['ec'];r=ns['r']
cases=[lambda:eval_(ec[:-1],r,kind='e'),lambda:eval_(ec,r,-1,'e'),lambda:eval_(ec,r,5,'e'),lambda:eval_(ec,r,1.5,'e'),lambda:eval_(ec,r,1,'unknown'),lambda:eval_(ec,I('1.50000000001'),kind='e'),lambda:eval_(ec,I('-1.50000000001'),kind='e'),lambda:I(2,1),lambda:I(1)/I(-1,1)]
for number,case in enumerate(cases,1):
    try:case()
    except (ArithmeticError,ValueError,ZeroDivisionError):pass
    else:raise ArithmeticError('corruption case not rejected: '+str(number))
print('PASS: valid certificate reproduced; all '+str(len(cases))+' negative guard cases rejected')
