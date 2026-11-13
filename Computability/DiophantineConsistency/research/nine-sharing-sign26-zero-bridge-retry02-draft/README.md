# Sign26 reverse bridge retry 02: source-only

The helper source differs from retry 01 only by replacing `simpa only` with `simpa` in its final normalization. Retry 01 reported Fin-vector applications left unreduced; this asks the standard simplifier to reduce them without changing the theorem or resource limits. The final reverse theorem source is byte-identical to retry 01. The original whnf timeout cause remains unknown. No theorem is claimed until Lean and audit succeed.
