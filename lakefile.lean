import Lake
open Lake DSL

package captureCalculus

@[default_target]
lean_lib FSub

@[default_target]
lean_lib CC

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
