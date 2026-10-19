import LeanLab.Placeholder
import Mathlib.Tactic

/-! # Practice 0: First steps with Lean

Welcome to Lean! This is the very first lesson: read it from top to bottom.
The first half is a guided tour with working examples — hover over or put
your cursor on each line and watch the Infoview panel (in VS Code) or the
right-hand pane (in the web editor at https://live.lean-lang.org/).

The second half is exercises: replace every `[...]` with your own answer.
`[...]` is this lab's placeholder — it behaves exactly like Lean's built-in
`sorry`, which means "I'll prove this later", so the file still compiles
while you work.

Grade yourself: `leanlab check Practice/P0_Basics.lean`
Stuck? `leanlab solution P0_Basics` -/

namespace Practice.Basics

/-! ## 1. Talking to Lean: `#eval` and `#check`

`#eval` asks Lean to *compute* something and show the result.
Put your cursor at the end of each line to see the answer. -/

#eval 2 + 2              -- 4
#eval 10 * 10 + 1        -- 101
#eval "Hello, " ++ "Lean!"  -- "Hello, Lean!"

/- `#check` asks Lean for the *type* of something — what kind of thing it is —
without computing anything. Every expression in Lean has a type. -/

#check 2 + 2             -- ℕ  (a natural number)
#check "hello"           -- String  (a piece of text)
#check true              -- Bool  (a computer-science boolean: `true` or `false`)
#check (2 + 2 = 4)       -- Prop  (a mathematical statement — maybe true, maybe not!)

/- Three basic types to remember:

* `Nat` — the natural numbers 0, 1, 2, 3, … Lean usually prints it as `ℕ`.
* `String` — text, written in double quotes.
* `Bool` — exactly two values, `true` and `false`.

Note the difference between `Bool` and `Prop`: a `Bool` is a value a program
can compute, while a `Prop` is a mathematical claim that you can *prove*.
`2 + 2 = 4` is a `Prop`, and proving such claims is what Lean is famous for. -/

/-! ## 2. `def`: giving things names

`def` names a value. The pattern is `def name : type := value`. -/

def meaningOfLife : ℕ := 42
def greeting : String := "Hello, Lean!"

#eval meaningOfLife      -- 42
#eval greeting           -- "Hello, Lean!"

/- `def` also makes functions. Arguments go in parentheses before the colon:
`(n : ℕ)` means "this function takes a natural number, called `n`". -/

def double (n : ℕ) : ℕ := 2 * n

#eval double 21          -- 42   (function application is just a space, no parens!)
#check double            -- ℕ → ℕ  ("a function from naturals to naturals")

/-! ## 3. Your first proof: `rfl`

A `theorem` is a `Prop` together with a proof. The pattern is

    theorem name : statement := by tactic

Everything after `by` is a list of *tactics* — commands that build the proof
step by step. The simplest tactic is `rfl` ("reflexivity"): it proves any
goal of the form `a = b` where both sides compute to the same value.
Here Lean unfolds `double 2` to `2 * 2`, computes `4`, and sees `4 = 4`. -/

theorem double_two : double 2 = 4 := by rfl

/-! ## 4. Proving something for *all* numbers: `simp`

`rfl` works when both sides are concrete values, but what about a statement
with a variable in it, like `n + 0 = n` *for every* `n`? There is nothing to
compute — `n` is unknown — so we use `simp` ("simplify") instead: it rewrites
the goal using a big library of known simplification facts until, with luck,
nothing is left to prove.

(We add a `'` to the name because Mathlib, the maths library we imported,
already proves this fact under the name `Nat.add_zero` — names must be new.) -/

theorem add_zero' (n : ℕ) : n + 0 = n := by simp

/-! ## 5. A taste of logic: `∧` ("and")

`p ∧ q` means "`p` and `q` are both true". Two things to know:

* To *use* a proof `h : p ∧ q`, take it apart: `h.1` proves `p`, `h.2` proves `q`.
* To *prove* a goal `q ∧ p`, the tactic `constructor` splits it into two
  goals (first `q`, then `p`), each introduced by a `·` bullet.

Two more tactics appear below:
* `intro h` — to prove "if … then …" (`→`), assume the "if" part and name it `h`.
* `exact e` — finish the current goal by handing Lean the exact proof `e`. -/

theorem and_swap' (p q : Prop) : p ∧ q → q ∧ p := by
  intro h          -- assume `h : p ∧ q`; the goal becomes `q ∧ p`
  constructor      -- split into two goals: `q` and `p`
  · exact h.2      -- the second half of `h` proves `q`
  · exact h.1      -- the first half of `h` proves `p`

/- A slicker version, for later: `⟨x, y⟩` (type `\<` and `\>`) is the
"anonymous constructor" — it builds a proof of an `∧` from its two halves,
so the whole proof is one line: `exact ⟨h.2, h.1⟩`. -/

/-! ## 6. Theorem names are for *reusing*

Why do theorems get names? So you can use them again! A proved theorem
becomes a fact Lean knows, and you can invoke it by name anywhere below.
For example, `rw [double_two]` ("rewrite") replaces `double 2` by `4` in the
goal, because `double_two` says those are equal. -/

theorem double_two_plus_ten : double 2 + 10 = 14 := by
  rw [double_two]  -- the goal `double 2 + 10 = 14` becomes `4 + 10 = 14`,
                   -- which `rw` finishes automatically with `rfl`

/-! ## Exercises

Replace each `[...]` below. They are roughly in order of difficulty, and
everything you need appeared above. Check your work with
`leanlab check Practice/P0_Basics.lean`. -/

/-- Exercise 1 — warm-up: both sides compute to the same number.
Which one-word tactic proves it? -/
theorem my_first_proof : 2 + 2 = 4 := by
  [...]

/- Exercise 2 — write a definition: `triple n` should be `3 * n`.
(Here `[...]` stands for a missing *value*, not a missing proof. The
`set_option` line just quiets an "unused variable `n`" warning until you
fill the body in — you can delete it once you use `n`.) -/
set_option linter.unusedVariables false in
/-- `triple n` should be `3 * n`. -/
def triple (n : ℕ) : ℕ :=
  [...]

/-- Exercise 3 — prove a fact about your own function (like `double_two`). -/
theorem triple_three : triple 3 = 9 := by
  [...]

/-- Exercise 4 — a statement about *every* `n`, so `rfl` won't do.
Which tactic simplifies it away? -/
theorem add_zero_twice (n : ℕ) : n + 0 + 0 = n := by
  [...]

/-- Exercise 5 — logic: assume `p`, then prove both halves of `p ∧ p`.
You'll need `intro`, then `constructor` and `exact` (or one `⟨…, …⟩`). -/
theorem and_self' (p : Prop) : p → p ∧ p := by
  [...]

/-- Exercise 6 — reuse a theorem by name: rewrite with `triple_three`
(yes, the one *you* proved in Exercise 3!) and let Lean finish. -/
theorem triple_three_plus_one : triple 3 + 1 = 10 := by
  [...]

end Practice.Basics
