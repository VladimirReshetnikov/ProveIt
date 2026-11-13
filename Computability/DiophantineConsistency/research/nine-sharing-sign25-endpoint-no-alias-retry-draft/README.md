# Sign25 direct endpoint with opacity in all stages

The prior no-alias attempt compiled its native endpoint child, then hit an
interpreter memory exception in the standard wrapper, which lacked the local
irreducibility settings used in the native stage. This source-only retry
replays the same native source and adds those settings to both the standard and
translated wrappers. The resource limits are unchanged. The precise cause of
the earlier exception remains unknown; these changes may not resolve it.
Until a guarded run and independent audit, no new endpoint is claimed.
