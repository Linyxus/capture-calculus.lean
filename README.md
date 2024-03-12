# Lean Mechanization of Capture Calculus

Currently it contains the mechanization of both System F<: and System CC<:box.

- `FSub/`, the System F<: type soundness proof. Intrinsically typed and de Bruijn indexed.
- `CC/`, the proof for System CC<:box. It is de Bruijn indexed and extrinsically typed.
  Main type soundness results (progress and preservation) are in `CC/Reduction/Safety.lean`.
  
The next step is to mechanize the soundness theorems of the separation calculus.

