import Lake
open Lake DSL

package «hashmap» where
  -- add package configuration options here

lean_lib «Hashmap» where
  -- add library configuration options here

@[default_target]
lean_exe «hashmap» where
  root := `Main

require std from git "https://github.com/leanprover/std4" @ "48643957cb394f0740a292b14954747c96bcd00e"
