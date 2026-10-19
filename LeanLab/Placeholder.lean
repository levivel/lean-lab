import Mathlib.Tactic

/-! `[...]` marks a proof for you to fill in. It works like `sorry`, so
`leanlab check` still counts it as unfinished. -/

macro "[...]" : tactic => `(tactic| sorry)
macro "[...]" : term => `(sorry)
