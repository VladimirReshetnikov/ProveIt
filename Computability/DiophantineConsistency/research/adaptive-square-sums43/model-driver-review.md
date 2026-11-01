# Prelaunch model-driver path correction

The first draft of `replay_model.py` had SHA-256
`e76c7b8eb41be9480e3a51efe347425361744216ac1e2ca961d165e16b05abd1`.
Independent review found that its `PARENT` path incorrectly named
`/tmp/ipra-square-sums43-native-peer-1vr18p6s`; the native-44 parent receipt
actually names `/tmp/ipra-square-sums44-native-peer-1vr18p6s`. The draft was
not launched, and its parent-receipt check would have failed closed.

The corrected driver has SHA-256
`ec0bbeca9aeb15b209f0fcdba9706a134043a9f3a96a8b4f5aa3b855b5c30d00`.
This note records a prelaunch review finding, not a replay failure or pass.
