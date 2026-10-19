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
- `Practice/` — lessons and exercises with `[...]` blanks to fill in; `Solutions/` — checked answers; `Scratch/` — your own files
- Run `leanlab` in Terminal for the commands.

### Start here: Lesson 1

New to Lean? Begin with **`Practice/P0_Basics.lean`** — a guided tour of
`#eval`, `#check`, the basic types (`ℕ`, `String`, `Bool`), writing `def`s,
and your first proofs with `rfl`, `simp`, and a little logic. It ends with
six short exercises.

1. Open the lesson: `leanlab open Practice/P0_Basics.lean` (or just open the
   file in VS Code). Put your cursor on a line to see what Lean thinks in the
   Infoview panel.
2. Read the lesson from the top, then replace each `[...]` in the exercises
   with your answer.
3. Grade yourself: `leanlab check Practice/P0_Basics.lean`.
4. Stuck? Peek at the worked answers: `leanlab solution P0_Basics`.

No install needed to try it: paste the lesson into the Lean web editor at
https://live.lean-lang.org/ (or run `leanlab share Practice/P0_Basics.lean`
to get a ready-made link).

### Lessons

| # | File | Topic |
|---|------|-------|
| 1 | `Practice/P0_Basics.lean` | First steps: `#eval`, `#check`, types, `def`, `rfl`, `simp`, `∧` — **start here** |
| 2 | `Practice/P1_Logic.lean` | Propositional logic: `intro`, `exact`, `constructor`, `rintro` |
| 3 | `Practice/P2_Naturals.lean` | Natural numbers and induction |
| 4 | `Practice/P3_RealsSets.lean` | Real numbers and sets |
| 5 | `Practice/P4_Induction.lean` | More induction |
| 6 | `Practice/P5_Primes.lean` | Primes and divisibility |
| 7 | `Practice/P6_Limits.lean` | Limits of sequences |
| 8 | `Practice/P7_Groups.lean` | Group theory |

Each lesson has matching worked answers in `Solutions/`.
