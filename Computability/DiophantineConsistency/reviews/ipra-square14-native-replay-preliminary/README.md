# Preliminary fourteen-variable native input

The preparer exited 0 and froze eight source modules, but its replay driver
incorrectly required six distinct modules despite an eight-module order and did
not guard the 2,140 inherited 107-parent fallback companion records. This packet
is preserved as preliminary and must not be used for replay. A distinct v2
preparer and driver correct both issues.

Manifest SHA-256:
`48aae8498b13b8301ae8c9ece38bea0a5b7bc122fef4f76f2c6a502311c58203`.
