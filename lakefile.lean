import Lake
open Lake DSL

package «hashmap» where
  -- add package configuration options here

lean_lib «Hashmap» where
  -- add library configuration options here

@[default_target]
lean_exe «hashmap» where
  root := `Main

lean_exe «insert» where
  root := `Hashmap.Benchmark.Insert

lean_exe «insert_replace» where
  root := `Hashmap.Benchmark.InsertReplace

lean_exe «empty» where
  root := `Hashmap.Benchmark.Empty

lean_exe «filtermap» where
  root := `Hashmap.Benchmark.FilterMap
