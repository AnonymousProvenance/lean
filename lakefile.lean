import Lake
open Lake DSL

package "provenance" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    -- The library's carriers (`Tuple`, `Relation`, …) are deliberately opaque
    -- `def`s; since Lean v4.31 instance search and rewriting respect
    -- transparency and cannot see through them, so restore the pre-4.31
    -- behavior (as Mathlib does in similar situations).
    ⟨`backward.isDefEq.respectTransparency, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.33.0"

-- The complexity results (`Provenance.HavingComplexity`) build on the
-- descriptive-complexity library, whose releases follow their own versioning;
-- the one pinned below is cut against the Mathlib pin above.
require "descriptive-complexity" from git
  "https://github.com/PierreSenellart/descriptive-complexity" @ "v1.2.0"

@[default_target]
lean_lib «Provenance» where
  -- add any library configuration options here
