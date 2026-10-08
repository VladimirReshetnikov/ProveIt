"""Run manually in a complete ProveIt checkout. Missing imports are errors."""
from fastunknot.diagram import Diagram
from fastunknot.group_certificate import verify_group_certificate
from fastunknot_adapter import group_exposure_decide

for s,w,expected in [(1,[],'UNKNOT'),(2,[1],'UNKNOT'),(3,[1,-2],'UNKNOT'),
                     (2,[1,1,1],'INCONCLUSIVE'),(3,[1,-2,1,-2],'INCONCLUSIVE')]:
    diagram=Diagram.from_braid(s,w)
    result=group_exposure_decide(diagram,seconds=10)
    assert result['status']==expected,(s,w,result)
    if expected=='UNKNOT':assert verify_group_certificate(diagram,result['certificate'])
print('Five upstream adapter smoke cases passed.')
