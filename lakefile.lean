import Lake
open Lake DSL

package «algdata» {
  -- add any package configuration options here
}

@[default_target]
lean_lib Algdata {
  -- add any library configuration options here
}

meta if get_config? doc = some "on" then
require «dog-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

-- Use a commit with `chore: bump to nightly-YYYY-MM-DD` commit message.
require std from git "https://github.com/leanprover/std4" @ "28459f72f3190b0f540b49ab769745819eeb1c5e"

require dijkstra from git "git@github.com:Junology/dijkstra.git" @ "master"
/-
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
-/
