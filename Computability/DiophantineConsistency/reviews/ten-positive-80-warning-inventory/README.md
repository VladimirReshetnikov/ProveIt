# Historical warning inventory for the 127-stage plan

`check.py` inventories each planned stage against its retained single-object
receipt/log, nine-prefix warning-policy record, or adaptive/HA87 historical
author warning fields. It found reported diagnostic policies for three
modules: stage 3 `ArithmeticPellPigeonhole` (three warnings), stage 5
`ModelArithmetic` (three), and stage 13 `ModelRatioBounds` (four). All matched
single-object logs were present, hash-matched their receipts, and had no
warning/error markers. The structured inventory is
`observations/attempt01.json`, SHA-256
`7e96b3fb0edf597d0e63097d2e66295f27dd6adf7b537a9c869ad60d5a356871`.

This is historical context, not authorization for a warning exception or a
prediction of fresh output. In particular, no stage-13 log has been approved
by this inventory; the running replay's strict policy can accept it only if a
separately reviewed future runner explicitly allows an exact baseline.
Records without a warning-policy field are reported as such; this script does
not independently replay Lean or inspect every historical raw log.
