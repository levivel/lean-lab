import LeanLab.Placeholder
import Mathlib.Tactic

/-! # Practice 0: First steps in Lean (start here!)

Welcome! This is your very first lesson. Read it from top to bottom —
the first half is a guided tour with worked examples, the second half
has exercises for you.

Replace every `[...]` with a definition or a proof. Put your cursor
inside a proof to see the goal in the Lean Infoview panel.

Tactics to try: `rfl`, `simp`, `intro`, `constructor`, `exact`.

Grade yourself: `leanlab check Practice/P0_Basics.lean`
Stuck? `leanlab solution P0_Basics`

No Lean installed? Paste this file into https://live.lean-lang.org/
(or run `leanlab share Practice/P0_Basics.lean`). -/

namespace Practice.Basics

/-! ## Part 1 — Talking to Lean: `#eval` and `#check`

Lean is two things at once: a programming language and a proof checker.
The two most useful commands for exploring are:

* `#eval e`  — *run* the expression `e` and show its value.
* `#check e` — don't run anything, just show the *type* of `e`.

Click on (or put your cursor at the end of) each line below and look at
the Infoview panel — or hover over the blue underline. -/

#eval 2 + 2            -- 4
#eval "Hello, " ++ "Lean!"   -- "Hello, Lean!"

/-! Every expression in Lean has a **type**. Three basic ones:

* `Nat`    — the natural numbers 0, 1, 2, 3, … (written `ℕ` in math files)
* `String` — text, like `"hello"`
* `Bool`   — the two values `true` and `false` -/

#check 42              -- 42 : Nat        ("42 has type Nat")
#check "hello"         -- "hello" : String
#check true            -- true : Bool
#check 2 + 2           -- 2 + 2 : Nat     (types work on whole expressions)

/-! ## Part 2 — Naming things with `def`

`def` gives a name to a value or a function. A function definition lists
its arguments with their types, then the result type, then `:=` and the
body. Here `(n : Nat)` means "takes one argument `n` of type `Nat`". -/

def greeting : String := "Hello, Lean!"

def double (n : Nat) : Nat := 2 * n

#eval greeting         -- "Hello, Lean!"
#eval double 5         -- 10  (note: function application is just a space!)
#check double          -- double : Nat → Nat  ("a function from Nat to Nat")

/-! ## Part 3 — Your first proof: `rfl`

A `theorem` is like a `def`, but what it defines is a *proof*. After the
colon comes the statement; after `:= by` comes a list of **tactics** —
commands that build the proof step by step.

The simplest tactic is `rfl` ("reflexivity"): it proves any statement of
the form `a = b` where both sides compute to the same value. Lean
literally runs the computation and checks the two sides match. -/

theorem double_two : double 2 = 4 := by rfl

/-! `rfl` only works when Lean can *compute* both sides to the same
answer. For statements about an unknown `n`, we need something stronger. -/

/-! ## Part 4 — Proving things for *all* numbers: `simp`

`n + 0 = n` is true for every natural number `n`, but `rfl`-style
computation can't check infinitely many cases one by one. The `simp`
tactic ("simplify") rewrites the goal using a large library of known
facts until nothing is left to prove.

(Mathlib already knows this fact as `Nat.add_zero` — we give our version
a fresh name ending in `'` so the two don't clash.) -/

theorem add_zero' (n : Nat) : n + 0 = n := by simp

/-! ## Part 5 — A first logic proof

Propositions (`Prop`) are statements that may be provable. `p ∧ q` means
"p and q"; `p ∧ q → q ∧ p` means "if p and q both hold, then q and p
both hold" (we may swap the two sides of an "and").

The proof below uses three tactics:
* `intro h`      — assume the hypothesis, calling it `h`
* `constructor`  — to prove `q ∧ p`, split it into two goals: `q` and `p`
* `exact h.2` / `exact h.1` — close each goal with the right part of `h`
  (`h.1` is the proof of `p`, `h.2` is the proof of `q`) -/

theorem and_swap (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  constructor
  · exact h.2
  · exact h.1

/-! The same proof in one line, using the *anonymous constructor* `⟨…, …⟩`
(type `\<` and `\>` for the brackets) which packages the two halves of an
"and" directly: -/

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  exact ⟨h.2, h.1⟩

/-! ## Part 6 — Theorem names and reusing theorems

The name after `theorem` (like `double_two` or `and_swap` above) is a
*label for the proof*. Once proved, you can use the theorem anywhere by
name — no need to reprove it. `example` is a nameless theorem: useful for
practice, but it can't be reused later.

Below, `and_swap q p h` applies our theorem with `p := q`, `q := p` to
the hypothesis `h : q ∧ p`, giving a proof of `p ∧ q` — applying a
theorem looks exactly like calling a function. -/

example (p q : Prop) (h : q ∧ p) : p ∧ q := by
  exact and_swap q p h

/-! ## Exercises

Your turn! Replace each `[...]` below. They get gradually harder.
Check your work with `leanlab check Practice/P0_Basics.lean`. -/

-- (This line just silences "unused variable" warnings while the
-- exercises below still contain `[...]` — ignore it.)
set_option linter.unusedVariables false

/- **Exercise 1.** Evaluate things yourself: put your cursor after each
`#eval`/`#check` and predict the output *before* looking. (Not graded.) -/

#eval double 21
#check greeting

/- **Exercise 2.** Define `triple`, the function that multiplies a
natural number by 3. (Replace `[...]` with the function body.) -/

def triple (n : Nat) : Nat := [...]

/- **Exercise 3.** Prove that your `triple` sends 3 to 9. One tactic is
enough — both sides compute to the same number. -/

theorem triple_three : triple 3 = 9 := by
  [...]

/- **Exercise 4.** A `simp` proof about *all* naturals, like Part 4. -/

theorem mul_one' (n : Nat) : n * 1 = n := by
  [...]

/- **Exercise 5.** A logic proof like Part 5: from a proof of `p`, prove
`p ∧ p`. Try `constructor` + `exact`, or the anonymous constructor. -/

theorem and_self_intro (p : Prop) (hp : p) : p ∧ p := by
  [...]

/- **Exercise 6.** Reuse a theorem by name, like Part 6: `and_swap`
turns `p ∧ q` into `q ∧ p`; applying it twice gets you back. -/

theorem and_swap_twice (p q : Prop) (h : p ∧ q) : p ∧ q := by
  [...]

end Practice.Basics
