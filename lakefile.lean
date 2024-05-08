import Lake
open Lake DSL

package «hashmap» where
  -- add package configuration options here

lean_lib «Hashmap» where
  -- add library configuration options here

@[default_target]
lean_exe «hashmap» where
  root := `Main

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
