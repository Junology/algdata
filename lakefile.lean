import Lake
open Lake DSL

package algdata {
  -- add any package configuration options here
}

@[default_target]
lean_lib Algdata {
  -- add any library configuration options here
}

meta if get_config? doc = some "on" then
require «dog-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

