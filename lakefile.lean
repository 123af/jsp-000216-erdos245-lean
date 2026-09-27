import Lake
open Lake DSL

package jsp000216Erdos245 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "v4.35.0-rc3"

require MiscYD from git
  "https://github.com/YaelDillies/misc-yd.git" @
    "cd12c538d66f15a358a6904e7c847cd67661096f"

@[default_target]
lean_lib Jsp000216
