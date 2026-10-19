# lean-lab

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.

## Lean Lab

- Online lab (lessons, exercises, progress, sharing): https://claude.ai/artifact/BDVVwc2HH5zUtviXJ8SLye
- `Practice/` — exercises with `[...]` blanks to fill in; `Solutions/` — checked answers; `Scratch/` — your own files
- Run `leanlab` in Terminal for the commands.

### How to start

New to Lean? **Start with Lesson 1: `Practice/P0_Basics.lean`.** It assumes
nothing and walks you through `#eval`, `#check`, types, `def`, and your first
proofs, with exercises at the end.

1. Open the lab: `leanlab open` (or open this folder in VS Code with the
   Lean 4 extension). Open `Practice/P0_Basics.lean` and read it top to bottom.
2. Replace each `[...]` with your answer; the Infoview panel shows the current
   proof goal when your cursor is inside a proof.
3. Grade yourself: `leanlab check Practice/P0_Basics.lean`.
4. Stuck? Peek at the worked answers: `leanlab solution P0_Basics`.

No Lean installed? Try any lesson in the Lean web editor at
https://live.lean-lang.org/ — paste the file in, or run
`leanlab share Practice/P0_Basics.lean` to get a ready-made link.

### Lessons

| # | File | Topics |
|---|------|--------|
| 1 | `Practice/P0_Basics.lean` | **Start here** — `#eval`/`#check`, basic types, `def`, first proofs with `rfl`, `simp`, simple logic |
| 2 | `Practice/P1_Logic.lean` | Propositional logic: `intro`, `exact`, `constructor`, `rintro`, `left`/`right` |
| 3 | `Practice/P2_Naturals.lean` | Natural numbers and induction |
| 4 | `Practice/P3_RealsSets.lean` | Real numbers, sets and functions (using Mathlib) |
| 5 | `Practice/P4_Induction.lean` | Induction, deeper |
| 6 | `Practice/P5_Primes.lean` | Divisibility and primes |
| 7 | `Practice/P6_Limits.lean` | Sequences and limits |
| 8 | `Practice/P7_Groups.lean` | Group theory |
