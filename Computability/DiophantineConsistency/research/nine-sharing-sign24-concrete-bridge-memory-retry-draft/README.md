# Sign24 concrete bridge scoped memory retry

Two independent sign24 bridge strategies previously failed with Lean
interpreter exceptions at `-M2800`, with sampled peak RSS around 2.94 billion
bytes. A sign25 endpoint using an otherwise matching `-M3600` interpreter
limit passed all stages while the retained 4 GiB RSS and 10 GiB host-memory
guards remained in force. This source-only retry uses the exact original
sign24 bridge source and provider union, raises only its Lean interpreter
limit to `-M3600`, and uses a fresh output. The original source's status as
checked remains unchanged until this attempt compiles and is independently
audited. Point-time provider and sampling qualifications remain. No iPRA
endpoint, exact Lean degree, external JSON or PDF binding follows from a
bridge alone.
