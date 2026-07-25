import BoundedZFCConsistency.Consistency

/-!
# Kernel audit for the model-relative consistency layer

Every statement below carries a model of the axiom set as an explicit
hypothesis.  The audit exists partly to keep that hypothesis visible: nothing
here proves consistency of ZF or of ZFC outright, and the assumption listings
show no hidden appeal to one.
-/

namespace LeanProofs
namespace BoundedZFCConsistency
namespace ConsistencyAudit

#check @not_restrictedBProv_bot_of_hasModel
#check @not_bProv_bot_of_hasModel
#check @not_restrictedBProv_bot_of_not_bProv_bot
#check @not_restrictedZFprov_bot_of_hasModel
#check @RestrictedZFCprov
#check @restrictedZFCprov_erase
#check @restrictedZFCprov_mono
#check @restrictedZFCprov_cofinal
#check @restrictedZFCprov_of_restrictedZFprov
#check @not_restrictedZFCprov_bot_of_hasModel

#print axioms not_restrictedBProv_bot_of_hasModel
#print axioms not_bProv_bot_of_hasModel
#print axioms not_restrictedBProv_bot_of_not_bProv_bot
#print axioms not_restrictedZFprov_bot_of_hasModel
#print axioms restrictedZFCprov_erase
#print axioms restrictedZFCprov_mono
#print axioms restrictedZFCprov_cofinal
#print axioms restrictedZFCprov_of_restrictedZFprov
#print axioms not_restrictedZFCprov_bot_of_hasModel

end ConsistencyAudit
end BoundedZFCConsistency
end LeanProofs
