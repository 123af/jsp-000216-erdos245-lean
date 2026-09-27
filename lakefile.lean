import Lake
open Lake DSL

package jsp000216Erdos245 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "b63f6e8a68d220e3b3bc4f3792bb53650d375f24"

@[default_target]
lean_lib Jsp000216
