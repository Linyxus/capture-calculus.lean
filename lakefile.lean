import Lake
open Lake DSL

package «captureCalculus» {
  -- add package configuration options here
}

lean_lib «CaptureCalculus» {
  -- add library configuration options here
}

@[default_target]
lean_exe «captureCalculus» {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
