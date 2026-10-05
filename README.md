# S(6) ≤ 1801 if R₄(3) ≤ 61: a centred Schur bound and the structure at the frontier

This repository contains a paper by Adam McKenna (2026) and its Lean 4
formalization.

- Paper: [paper/schur-centred-bound.pdf](paper/schur-centred-bound.pdf)
  (source: [paper/schur-centred-bound.md](paper/schur-centred-bound.md))
- Statements: [Challenge.lean](Challenge.lean). It imports only Mathlib.
- Proofs: the library [ClassicalSchur/](ClassicalSchur/), made available
  under the same names by [Solution.lean](Solution.lean).
- Comparator configuration: [comparator.json](comparator.json).

## Results

`S(n)` is the Schur number: the largest `N` such that `[1, N]` is covered by
`n` sumfree sets. `R_k(3)` is the triangle Ramsey number with `k` colours.

1. **The centred bound.** If `R_k(3) ≤ r`, then
   `S(k + 1) ≤ 2(k + 1)⌊(r − 1)/2⌋ + 1`
   (`ClassicalSchur.not_coveredBySumFree_Icc_of_triangleRamsey`).
2. **`S(3) ≤ 13`**, from `R_2(3) ≤ 6`. It is known that `S(3) = 13`, so
   the bound is exact. Lean proves the upper bound `S(3) ≤ 13`
   (`ClassicalSchur.not_coveredBySumFree_Icc_fourteen_three`).
3. **Under the hypothesis `R_4(3) ≤ 61`:** `R_5(3) ≤ 302`
   (`ClassicalSchur.triangleRamsey_succ`) and `S(6) ≤ 1801`
   (`ClassicalSchur.not_coveredBySumFree_Icc_six_of_triangleRamsey_four_sixtyOne`).
   For comparison, the published bounds are `R_4(3) ≤ 62` and
   `S(6) ≤ 1836`.
4. **The frontier.** Let `R_k(3) ≤ u + 1`, `2t = (k + 1)u`, `m = (k + 2)t`,
   and let `c` be a Schur colouring of `[1, 2m + 1]` with `k + 2` colours. Put
   `q = c(m + 1)`, and let `V` be the set of points `x ≠ m` of
   `{0, …, 2m + 1}` with `c(|m − x|) = q`. Then:
   - each colour occurs `t` times in `[1, m]` (balanced colour classes);
   - `V` has `2t + 1` points, and each point of `V` has exactly `u`
     neighbours in `V` of each colour `≠ q` (nested saturation);
   - `c(m + 1 − d) = c(m + 1 + d)` for every `d ∈ [1, m]` with `c(d) = q`
     (forced reflection);
   - for each colour `i ≠ q`, the points of `V` joined to `2m + 1` in colour
     `i` form a set of `u` points, closed under `x ↦ 2m − x` with no fixed
     point, whose differences avoid the colours `i` and `q`; so `u` is even.
5. **Six colours under `R_4(3) ≤ 61`** (`k = 4`, `u = 60`, `t = 150`,
   `m = 900`): a Schur colouring of `[1, 1801]` with six colours gives five
   sets of 60 points, each closed under `x ↦ 1800 − x` with no fixed point and
   with differences in at most four colours
   (`ClassicalSchur.schur_six_frontier_structure`).

## What this repository does not prove

- **`R_4(3) ≤ 61`.** It is the hypothesis `TriangleRamsey 4 61`, an explicit
  argument of every theorem that uses it. It is a computer-assisted claim of
  M. Tatarevic
  ([r3333-upper-bound](https://github.com/milostatarevic/r3333-upper-bound),
  commit `ddd7755476db3f0751181db0daec75342576cdd1`). His Lean development
  derives it from a premise that a finite list of SAT formulas has no
  satisfying assignment. Solvers check that premise outside the Lean kernel;
  his repository publishes their UNSAT records, not LRAT certificates. Adam
  McKenna's project made and checked LRAT certificates for all 56,830
  formulas, with AI assistance: `lrat-check` accepted all of them, and a
  second check by Claude, which used none of the code of the first pipeline,
  verified the same proofs with the CakeML-verified checker `cake_lpr`. The
  record is
  [issue #1](https://github.com/milostatarevic/r3333-upper-bound/issues/1),
  posted by Adam McKenna on 2 October 2026. These checks rely on the builds
  of the checkers and on Tatarevic's Lean emitters that produce the formulas,
  and do not review his reduction by hand. This repository does not import
  his development.
- **`S(6) ≤ 1800`.** The frontier theorems describe a Schur colouring of
  `[1, 1801]` with six colours. They do not exclude it. Whether the five
  60-point sets can exist is open.
- **Novelty.** No earlier statement of these results was found in the
  sources that were read, but the method of the centred bound is probably not
  new. The zbMATH summary of H. Wan (J. Graph Theory 26 (1997) 119–122) gives
  a Schur bound `S_n` for even `n ≥ 6` and does not define `S_n`. If `S_n` is
  the largest `N` (as here), the summary gives `S(6) ≤ 1922`, 1 above the
  value 1921 that the centred bound gives from Wan's own `R_5(3) ≤ 322`. If
  `S_n` is the least `N` such that every colouring has a monochromatic
  solution, the summary gives `S(6) ≤ 1921`, and the two bounds agree for
  every even `n` from 6 to 30. The abstract of Li Huai'en (J. Zhengzhou Univ.
  (Sci.) 1992) gives an `R_n(3)` bound and says that the paper also lowers the
  Schur-number bounds; it gives no Schur value. Neither full text was read.
  See the paper, section Literature.

## Lean

- Lean `v4.35.0-rc3`, Mathlib tag `v4.35.0-rc3`. `lake-manifest.json` pins
  every dependency.
- Build: `lake exe cache get && lake build`.
- Comparator: `scripts/verify-comparator.sh` runs the toolchain's
  `lake comparator` the way the Palomar Registry does (Linux with
  `bubblewrap`). The CI workflow (`.github/workflows/ci.yml`) runs it on
  every push to `main`, on every pull request, and when it is started by
  hand (`workflow_dispatch`).
- All 14 compared theorems use only the axioms `propext`, `Classical.choice`
  and `Quot.sound`. There is no `sorry` outside the statements of
  `Challenge.lean`.

| Module | Contents |
| --- | --- |
| `ClassicalSchur.Basic` | `SumFree`, `CoveredBySumFree` |
| `ClassicalSchur.Ramsey` | `TriangleRamsey`, the pigeonhole bound `ramseyBound` |
| `ClassicalSchur.SchurBound` | `triangleRamsey_succ`, the centred bound and its cases `S(3) ≤ 13` and `S(6) ≤ 1801` |
| `ClassicalSchur.Frontier` | Schur colourings, colour neighbourhoods, and the frontier theorems |

Differences between the Lean and the prose: natural numbers are the ambient
type; `S(n)` is not defined in Lean, so each bound `S(n) ≤ M` is stated as
`¬ CoveredBySumFree (Set.Icc 1 (M + 1)) n`; colours are elements of `Fin n`;
a Schur colouring is a map on all of `ℕ` that is constrained only on
`[1, N]`; distances use `Nat.dist`; neighbourhoods are finite sets inside
`{0, …, 2m + 1}`; `TriangleRamsey k N` quantifies over pair colourings by
natural numbers from a set of at most `k` colours; the frontier theorems hold
for all natural `k`, `u`, `t` and are vacuous at `k = 0` or `u = 0`, while
the paper assumes `k, u, t ≥ 1`. The paper, Section 6, lists all
differences.

## How this was made

The arguments for the centred bound and for the frontier were first proposed
by AI agents based on ChatGPT (OpenAI) in a project discussion, on 27 September
and 2 October 2026. A Claude agent (Anthropic) audited the argument for the
centred bound: it rebuilt each step and checked small cases exhaustively.
The AI system Claude (Anthropic; model Claude Opus 5.5) checked each step of
the frontier argument, restated it with explicit hypotheses, and wrote all
Lean definitions and proofs, under the direction of Adam McKenna.

The Lean kernel checks every proof. On 2 October 2026 an independent Claude
agent rebuilt the Lean module of the frontier, ran its axiom audit again, and
checked its statements and each step against the argument, including the
example with `S(3) = 13`. On 3 October 2026 another independent Claude agent
checked all 14 compared statements and all proofs of Sections 2 to 4 of the
paper against the Lean, and recomputed the numbers. The comparison of
`Challenge.lean` with `Solution.lean` (the types and values of the 7
definitions and the types of the 14 theorems) was done by the Claude session
that wrote the repository, not by a separate agent; the comparator run in CI
is the formal check of it. The results have not been peer reviewed.

## Licence

Apache License 2.0; see [LICENSE](LICENSE).

## Citation

See [CITATION.cff](CITATION.cff).
