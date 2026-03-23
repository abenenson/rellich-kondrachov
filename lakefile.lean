import Lake
open Lake DSL

package «rellich-kondrachov» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

lean_lib «MathlibExtensions» where
  srcDir := "."
  roots := #[`MathlibExtensions]

@[default_target]
lean_lib «RellichKondrachov» where
  srcDir := "."
  roots := #[`RellichKondrachov]
