# An independent statement check for the Lean proof of VP ≠ VNP

Comparator accepts the Lean proof of VP ≠ VNP in
[`anthropics/formal-math/vp-vnp`](https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp).
That only matters if its challenge statement "corresponds to its intended informal meanings"
([Lean reference](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)).

`Independent.lean` restates the claims from the textbooks, without reading `vp-vnp`.
`Bridge.lean` proves `vp-vnp`'s theorems imply them.

| Claim in `Independent.lean` | Proved from |
|---|---|
| `MainLowerBound` | `Solution.mainTheorem` |
| `MainLowerBoundBorder` | `Solution.mainTheoremApprox` |
| `VP_ssubset_VNP` | `Solution.separation` |
| `VNP_not_subset_VPbar` | `Solution.separationClosure` |
| `PermanentRealLowerBound` | `Solution.permanent_over_real` |

Only standard axioms ([build](logs/bridge-build.log)). Comparator accepts the bridge against
`BridgeChallenge.lean`, which imports only `Independent`, in Lean's kernel and nanoda
([log](logs/bridge-comparator.log)).

The bridge is one-way: `vp-vnp`'s theorems imply these claims. The converse is not shown.

## What `Independent.lean` states

Circuits are straight-line programs over F with inputs, arbitrary constants from F, and binary
`+` and `×`. Size counts every gate. A circuit computes f if some gate equals f as a formal
polynomial.

- `MainLowerBound`: ∃ c > 0, ∀ p, ∃ m₀, for every field F of characteristic p and every
  m ≥ m₀, every circuit for HC_m has more than m^(c·(log₂ m)^(1/3)) gates, and so does every
  circuit for per_m if p ≠ 2.
- `MainLowerBoundBorder`: the same, for circuits over F(ε) computing f + ε·g with g ∈ F[ε][x].
- `VP_ssubset_VNP`, `VNP_not_subset_VPbar`: for every field. VP is p-families with polynomial
  circuit size. VNP is Valiant's p-definable families, f(x) = Σ_{e ∈ {0,1}^u} g(x, e) with
  g ∈ VP. VP-bar is p-families with polynomial border complexity as above.
- `PermanentRealLowerBound`: the bound for per_m over ℝ.

## Sources

Each definition in `Independent.lean` cites one of:

- Valiant, "Completeness classes in algebra", STOC 1979.
- Bürgisser, *Completeness and Reduction in Algebraic Complexity Theory*, Springer 2000, Ch. 2.
- Bürgisser, Clausen, Shokrollahi, *Algebraic Complexity Theory*, Ch. 4 and 15.
- Bürgisser, "The complexity of factors of multivariate polynomials", FoCM 2004.
- Mahajan, "Algebraic Complexity Classes", arXiv:1307.3863.

## Differences

None broke an implication.

- `hc` differs for m ≤ 1. The bridge takes m ≥ 2.
- The permanent is transposed. Same polynomial.
- VP-bar uses Laurent series in `Statement.lean` (stronger), `F(ε)` here.
- Families and the VNP sum are encoded differently.

## Provenance

Claude agents wrote all the Lean here. One wrote `Independent.lean` from the sources above,
told not to read `vp-vnp`. Nothing enforced that. Another wrote `Bridge.lean` against the
frozen file.

No human has checked `Independent.lean`. That needs someone who knows algebraic complexity.

## `vp-vnp`'s checks, rerun

At commit `11b6c7e`, on macOS:

- Build passes. `sorry` only in `Challenge.lean` ([log](logs/formal-math-build.log)).
- Standard axioms ([log](logs/formal-math-print-axioms.txt)).
- Comparator accepts, with `vp-vnp`'s pinned tools and config ([log](logs/formal-math-comparator.log), [tools](logs/comparator-setup/tools.txt)).

Both Comparator runs skipped landrun's sandbox, which is Linux-only
([stub](logs/comparator-setup/landrun-passthrough)), and ran after building. `vp-vnp`
has no `#eval`, `initialize` or elaborators, one tactic macro aside ([scan](logs/formal-math-source-scan.txt)).

## Reproducing

    lake exe cache get
    lake build

Apache 2.0, as `vp-vnp`.
