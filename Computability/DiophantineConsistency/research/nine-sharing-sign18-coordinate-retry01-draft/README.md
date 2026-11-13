# Sign18 main-root coordinate fresh retry source

The first guarded attempt failed because `simp only` left Fin vector
applications unreduced in the lift and drop paths. This source-only retry
uses full simplification there, including natural numeral embeddings. No Lean
compilation or coordinate proof is claimed.
